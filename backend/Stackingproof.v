(*========================================================================*)
(*                                                                        *)
(*                    CompcertTSO                                         *)
(*                                                                        *)
(*          Jaroslav Sevcik, University of Cambridge                      *)
(*          Viktor Vafeiadis, University of Cambridge                     *)
(*          Francesco Zappa Nardelli, INRIA Rocquencourt                  *)
(*          Suresh Jagannathan, Purdue University                         *)
(*          Peter Sewell, University of Cambridge                         *)
(*                                                                        *)
(*          (building on CompCert 1.5 and a 1.8 pre-release)              *)
(*                                                                        *)
(*  This document and the CompCertTSO sources are copyright 2005, 2006,   *)
(*  2007, 2008, 2009, 2010, 2011 Institut National de Recherche en        *)
(*  Informatique et en Automatique (INRIA), and Suresh Jagannathan,       *)
(*  Jaroslav Sevcik, Peter Sewell and Viktor Vafeiadis.                   *)
(*                                                                        *)
(*  All rights reserved.  This file is distributed under the terms of     *)
(*  the INRIA Non-Commercial License Agreement.                           *)
(*                                                                        *)
(*                                                                        *)
(*                                                                        *)
(*                                                                        *)
(*                                                                        *)
(*========================================================================*)

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for the translation from Linear to Mach. *)

(** This file proves semantic preservation for the [Stacking] pass.
  For the target language Mach, we use the abstract semantics
  given in file [Machabstr], where a part of the activation record
  is not resident in memory.  Combined with the semantic equivalence
  result between the two Mach semantics (see file [Machabstr2concr]),
  the proof in this file also shows semantic preservation with
  respect to the concrete Mach semantics. *)

Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import Ast.
Require Import Integers.
Require Import Pointers.
Require Import Values.
Require Import Op.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Locations.
Require Import Linear.
Require Import Lineartyping.
Require Import Mach.
Require Import Machabstr.
Require Import Bounds.
Require Import Conventions.
Require Import Stacklayout.
Require Import Stacking.
Require Import Simulations MCsimulation.
Require Import Memcomp Traces.
Require Import Libtactics.


Definition genv_rel : Linear.genv -> Mach.genv -> Prop :=
 (fun x y => Genv.genv_match (fun a b => transf_fundef a = OK b) y x).


(** * Properties of frames and frame accesses *)

(** ``Good variable'' properties for frame accesses. *)

Lemma typesize_typesize:
  forall ty, Ast.typesize ty = 4 * Locations.typesize ty.
Proof.
  destruct ty; auto.
Qed.

Section PRESERVATION.

(* Assume fixed global environments that are related: *)
Variables (ge : Linear.genv) (tge : Mach.genv).
Hypothesis TRANSF: genv_rel ge tge.

Let lts := (mklts thread_labels (Linear.step ge)).
Let tlts := (mklts thread_labels (ma_step tge)).

Section FRAME_PROPERTIES.

Variable stack: Machabstr.stackframes.
Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable tf: Mach.function.
Hypothesis TRANSF_F: transf_function f = OK tf.

Lemma unfold_transf_function:
  tf = Mach.mkfunction
         f.(Linear.fn_sig)
         (transl_body f fe (align_framesize (align_stacksize (Int.unsigned f.(Linear.fn_stacksize)) fe_retaddrsize)
           fe.(fe_size) fe_retaddrsize))
         (align_stacksize (Int.unsigned f.(Linear.fn_stacksize)) fe_retaddrsize)
         f.(Linear.fn_stacksize)
         (align_framesize (align_stacksize (Int.unsigned f.(Linear.fn_stacksize)) fe_retaddrsize)
           fe.(fe_size) fe_retaddrsize).
Proof.
  generalize TRANSF_F. unfold transf_function.
  repeat (destruct zle; try done).
  unfold fe, b. congruence.
Qed.

Lemma align_framesize_le:
  forall ssz fsz rsz,
    fsz <= align_framesize ssz fsz rsz.
Proof.
  intros. unfold align_framesize.
  pose proof (align_le (ssz + rsz + fsz) 16). 
  omega.
Qed.

Lemma align_stacksize_le:
  forall ssz rsz,
    ssz <= align_stacksize ssz rsz.
Proof.
  intros; unfold align_stacksize. 
  pose proof (align_le (ssz + rsz) (align_size ssz) (align_size_pos _)). 
  omega.
Qed.

Lemma stacksize_no_overflow: fe.(fe_size) <= -Int.min_signed.
Proof.
  generalize TRANSF_F. unfold transf_function.
  case zle; try done. 
  intros E _. 
  pose proof (align_framesize_le (align_stacksize (Int.unsigned 
    (Linear.fn_stacksize f)) fe_retaddrsize) (fe_size fe) fe_retaddrsize).
  pose proof (align_stacksize_le (Int.unsigned 
    (Linear.fn_stacksize f)) fe_retaddrsize). 
  pose proof (Int.unsigned_range (Linear.fn_stacksize f)).
  unfold fe, b, fe_retaddrsize in *. 
  omega.
Qed.

(** A frame index is valid if it lies within the resource bounds
  of the current function. *)

Definition index_valid (idx: frame_index) :=
  match idx with
  | FI_local x Tint => 0 <= x < b.(bound_int_local)
  | FI_local x Tfloat => 0 <= x < b.(bound_float_local)
  | FI_arg x ty => 0 <= x /\ x + typesize ty <= b.(bound_outgoing)
  | FI_saved_int x => 0 <= x < b.(bound_int_callee_save)
  | FI_saved_float x => 0 <= x < b.(bound_float_callee_save)
  end.

Definition type_of_index (idx: frame_index) :=
  match idx with
  | FI_local x ty => ty
  | FI_arg x ty => ty
  | FI_saved_int x => Tint
  | FI_saved_float x => Tfloat
  end.

(** Non-overlap between the memory areas corresponding to two
  frame indices. *)

Definition index_diff (idx1 idx2: frame_index) : Prop :=
  match idx1, idx2 with
  | FI_local x1 ty1, FI_local x2 ty2 =>
      x1 <> x2 \/ ty1 <> ty2
  | FI_arg x1 ty1, FI_arg x2 ty2 =>
      x1 + typesize ty1 <= x2 \/ x2 + typesize ty2 <= x1
  | FI_saved_int x1, FI_saved_int x2 => x1 <> x2
  | FI_saved_float x1, FI_saved_float x2 => x1 <> x2
  | _, _ => True
  end.

Ltac AddPosProps :=
  generalize (bound_int_local_pos b); intro;
  generalize (bound_float_local_pos b); intro;
  generalize (bound_int_callee_save_pos b); intro;
  generalize (bound_float_callee_save_pos b); intro;
  generalize (bound_outgoing_pos b); intro;
  generalize (align_float_part b); intro.

Lemma size_pos: fe.(fe_size) >= 0.
Proof.
  AddPosProps.
  unfold fe, make_env, fe_size; omega.
Qed.

Opaque function_bounds.

Lemma offset_of_index_disj:
  forall idx1 idx2,
  index_valid idx1 -> index_valid idx2 ->
  index_diff idx1 idx2 ->
  offset_of_index fe idx1 + 4 * typesize (type_of_index idx1) <= offset_of_index fe idx2 \/
  offset_of_index fe idx2 + 4 * typesize (type_of_index idx2) <= offset_of_index fe idx1.
Proof.
  AddPosProps.
  intros.
  destruct idx1; destruct idx2;
  try (destruct t); try (destruct t0);
  unfold offset_of_index, fe, make_env,
    fe_size, fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save,
    type_of_index, typesize;
  simpl in H5; simpl in H6; simpl in H7;
  try omega.
  destruct H7; clarify. omega.
  destruct H7; clarify. omega.
Qed.

Remark aligned_4_4x: forall x, (4 | 4 * x).
Proof. intro. exists x; ring. Qed.

Remark aligned_4_8x: forall x, (4 | 8 * x).
Proof. intro. exists (x * 2); ring. Qed.

Remark aligned_4_align8: forall x, (4 | align x 8).
Proof. 
  intro. apply Zdivides_trans with 8. exists 2; auto. apply align_divides. omega.
Qed.

Hint Resolve Zdivide_0 Zdivide_refl Zdivide_plus_r
             aligned_4_4x aligned_4_8x aligned_4_align8: align_4.

Hint Extern 4 (?X | ?Y) => (exists (Y/X); reflexivity) : align_4.

Lemma offset_of_index_aligned:
  forall idx, (4 | offset_of_index fe idx).
Proof.
  intros.
  destruct idx;
  unfold offset_of_index, fe, make_env,
    fe_size, fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save;
  auto with align_4.
  destruct t; auto with align_4.
Qed.

Lemma frame_size_aligned:
  (4 | fe_size fe).
Proof.
  unfold offset_of_index, fe, make_env,
    fe_size, fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save;
  auto with align_4.
Qed.

(** The following lemmas give sufficient conditions for indices
  of various kinds to be valid. *)

Lemma index_local_valid:
  forall ofs ty,
  slot_within_bounds f b (Local ofs ty) ->
  index_valid (FI_local ofs ty).
Proof.
  unfold slot_within_bounds, index_valid. auto.
Qed.

Lemma index_arg_valid:
  forall ofs ty,
  slot_within_bounds f b (Outgoing ofs ty) ->
  index_valid (FI_arg ofs ty).
Proof.
  unfold slot_within_bounds, index_valid. auto.
Qed.

Lemma index_saved_int_valid:
  forall r,
  In r int_callee_save_regs ->
  index_int_callee_save r < b.(bound_int_callee_save) ->
  index_valid (FI_saved_int (index_int_callee_save r)).
Proof.
  intros. red. split. 
  apply Zge_le. apply index_int_callee_save_pos; auto. 
  auto.
Qed.

Lemma index_saved_float_valid:
  forall r,
  In r float_callee_save_regs ->
  index_float_callee_save r < b.(bound_float_callee_save) ->
  index_valid (FI_saved_float (index_float_callee_save r)).
Proof.
  intros. red. split. 
  apply Zge_le. apply index_float_callee_save_pos; auto. 
  auto.
Qed.

Hint Resolve index_local_valid index_arg_valid
             index_saved_int_valid index_saved_float_valid: stacking.

(** The offset of a valid index lies within the bounds of the frame. *)

Lemma offset_of_index_valid:
  forall idx,
  index_valid idx ->
  0 <= offset_of_index fe idx /\
  offset_of_index fe idx + 4 * typesize (type_of_index idx) <= fe.(fe_size).
Proof.
  AddPosProps.
  intros.
  destruct idx; try destruct t;
  unfold offset_of_index, fe, make_env,
    fe_size, fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save,
    type_of_index, typesize;
  unfold index_valid in H5; simpl typesize in H5;
  omega.
Qed.

(** Offsets for valid index are representable as signed machine integers
  without loss of precision. *)

Lemma offset_of_index_no_overflow:
  forall idx,
  index_valid idx ->
  Int.signed (Int.repr (offset_of_index fe idx)) = offset_of_index fe idx.
Proof.
  intros.
  generalize (offset_of_index_valid idx H). intros [A B].
  apply Int.signed_repr.
  split. apply Zle_trans with 0; auto. compute; intro; discriminate.
  assert (offset_of_index fe idx < fe_size fe).
    generalize (typesize_pos (type_of_index idx)); intro. omega.
  apply Zlt_succ_le. 
  change (Zsucc Int.max_signed) with (- Int.min_signed).
  generalize stacksize_no_overflow. omega. 
Qed.

(** Characterization of the [get_slot] and [set_slot]
  operations in terms of the following [index_val] and [set_index_val]
  frame access functions. *)

Definition index_val (idx: frame_index) (fr: frame) :=
  fr (type_of_index idx) (offset_of_index fe idx (* - tf.(fn_framesize) *)).

Definition set_index_val (idx: frame_index) (v: val) (fr: frame) :=
  update (type_of_index idx) (offset_of_index fe idx (* - tf.(fn_framesize) *)) v fr.

Lemma slot_valid_index:
  forall idx,
  index_valid idx -> 
  slot_valid tf.(fn_framesize) (type_of_index idx) (offset_of_index fe idx).
Proof.
  intros.
  destruct (offset_of_index_valid idx H) as [A B].
  rewrite <- typesize_typesize in B.
  rewrite unfold_transf_function.
  constructor; auto using offset_of_index_aligned.
  unfold fn_framesize. 
  by eapply Zle_trans, align_framesize_le.
Qed.

Lemma get_slot_index:
  forall fr idx ty v,
  index_valid idx ->
  ty = type_of_index idx ->
  v = index_val idx fr ->
  get_slot tf.(fn_framesize) fr ty (Int.signed (Int.repr (offset_of_index fe idx))) = Some v.
Proof.
  intros. subst v; subst ty. rewrite offset_of_index_no_overflow; auto.
  unfold index_val. unfold get_slot. 
  destruct slot_valid_dec as [|NV]; try done.
  elim NV; apply slot_valid_index; auto.
Qed.

Lemma set_slot_index:
  forall fr idx v,
  index_valid idx ->
  set_slot tf.(fn_framesize) fr (type_of_index idx) (Int.signed (Int.repr (offset_of_index fe idx)))
                 v = Some (set_index_val idx v fr).
Proof.
  intros.  rewrite offset_of_index_no_overflow; auto.
  unfold set_slot.
  destruct slot_valid_dec as [|NV]; try done.
  elim NV; apply slot_valid_index; auto.
Qed.

(** ``Good variable'' properties for [index_val] and [set_index_val]. *)

Lemma get_set_index_val_same:
  forall fr idx v,
  index_val idx (set_index_val idx v fr) = v.
Proof.
  intros. unfold index_val, set_index_val. apply update_same. 
Qed.

Lemma get_set_index_val_other:
  forall fr idx idx' v,
  index_valid idx -> index_valid idx' -> index_diff idx idx' ->
  index_val idx' (set_index_val idx v fr) = index_val idx' fr.
Proof.
  intros. unfold index_val, set_index_val. apply update_other.
  repeat rewrite typesize_typesize. 
  exploit (offset_of_index_disj idx idx'); auto. (* omega. *)
Qed.

Lemma get_set_index_val_overlap:
  forall ofs1 ty1 ofs2 ty2 v fr,
  S (Outgoing ofs1 ty1) <> S (Outgoing ofs2 ty2) ->
  Loc.overlap (S (Outgoing ofs1 ty1)) (S (Outgoing ofs2 ty2)) = true ->
  index_val (FI_arg ofs2 ty2) (set_index_val (FI_arg ofs1 ty1) v fr) = Vundef.
Proof.
  intros. unfold index_val, set_index_val, offset_of_index, type_of_index.
  assert (~(ofs1 + typesize ty1 <= ofs2 \/ ofs2 + typesize ty2 <= ofs1)).
  destruct (orb_prop _ _ H0). apply Loc.overlap_aux_true_1. auto. 
  apply Loc.overlap_aux_true_2. auto.
  unfold update. 
  destruct (zeq (4 * ofs1 (* - fn_framesize tf *))
                (4 * ofs2 (* - fn_framesize tf) *))).
  destruct (typ_eq ty1 ty2). 
  elim H. decEq. decEq. omega. auto.
  auto.
  repeat rewrite typesize_typesize.
  rewrite zle_false. apply zle_false. omega. omega.
Qed.

(** Accessing stack-based arguments in the caller's frame. *)


Definition get_parent_slot (cs: stackframes) (ofs: Z) (ty: typ) (v: val) : Prop :=
  get_slot (parent_size cs) (parent_frame cs)
           ty (Int.signed (Int.repr (4 * ofs))) = Some v.

(** * Agreement between location sets and Mach environments *)

(** The following [agree] predicate expresses semantic agreement between:
- on the Linear side, the current location set [ls] and the location
  set of the caller [ls0];
- on the Mach side, a register set [rs], a frame [fr] and a call stack [cs].
*)

Record agree (ls ls0: locset) (rs: regset) (fr: frame) (cs: stackframes): Prop :=
  mk_agree {
    (** Machine registers have the same values on the Linear and Mach sides. *)
    agree_reg:
      forall r, ls (R r) = rs r;

    (** Machine registers outside the bounds of the current function
        have the same values they had at function entry.  In other terms,
        these registers are never assigned. *)
    agree_unused_reg:
      forall r, ~(mreg_within_bounds b r) -> rs r = ls0 (R r);

    (** Local and outgoing stack slots (on the Linear side) have
        the same values as the one loaded from the current Mach frame 
        at the corresponding offsets. *)
    agree_locals:
      forall ofs ty, 
      slot_within_bounds f b (Local ofs ty) ->
      ls (S (Local ofs ty)) = index_val (FI_local ofs ty) fr;
    agree_outgoing:
      forall ofs ty, 
      slot_within_bounds f b (Outgoing ofs ty) ->
      ls (S (Outgoing ofs ty)) = index_val (FI_arg ofs ty) fr;

    (** Incoming stack slots (on the Linear side) have
        the same values as the one loaded from the parent Mach frame 
        at the corresponding offsets. *)
    agree_incoming:
      forall ofs ty,
      In (S (Incoming ofs ty)) (loc_parameters f.(Linear.fn_sig)) ->
      get_parent_slot cs ofs ty (ls (S (Incoming ofs ty)));

    (** The areas of the frame reserved for saving used callee-save
        registers always contain the values that those registers had
        on function entry. *)
    agree_saved_int:
      forall r,
      In r int_callee_save_regs ->
      index_int_callee_save r < b.(bound_int_callee_save) ->
      index_val (FI_saved_int (index_int_callee_save r)) fr = ls0 (R r);
    agree_saved_float:
      forall r,
      In r float_callee_save_regs ->
      index_float_callee_save r < b.(bound_float_callee_save) ->
      index_val (FI_saved_float (index_float_callee_save r)) fr = ls0 (R r)
  }.

Hint Resolve agree_reg agree_unused_reg 
             agree_locals agree_outgoing agree_incoming
             agree_saved_int agree_saved_float: stacking.

(** Values of registers and register lists. *)

Lemma agree_eval_reg:
  forall ls ls0 rs fr cs r,
  agree ls ls0 rs fr cs -> rs r = ls (R r).
Proof.
  intros. symmetry. eauto with stacking.
Qed.

Lemma agree_eval_regs:
  forall ls ls0 rs fr cs rl,
  agree ls ls0 rs cs fr -> map rs rl = reglist ls rl.
Proof.
  induction rl; simpl; intros.
  auto. f_equal. eapply agree_eval_reg; eauto. auto.
Qed.

Hint Resolve agree_eval_reg agree_eval_regs: stacking.

(** Preservation of agreement under various assignments:
  of machine registers, of local slots, of outgoing slots. *)

Lemma agree_set_reg:
  forall ls ls0 rs fr cs r v,
  agree ls ls0 rs fr cs ->
  mreg_within_bounds b r ->
  agree (Locmap.set (R r) v ls) ls0 (Regmap.set r v rs) fr cs.
Proof.
  intros. constructor; eauto with stacking.
  intros. case (mreg_eq r r0); intro.
  subst r0. rewrite Locmap.gss; rewrite Regmap.gss; auto.
  rewrite Locmap.gso. rewrite Regmap.gso. eauto with stacking.
  auto. red. auto.
  intros. rewrite Regmap.gso. eauto with stacking. 
  red; intro; subst r0. contradiction.
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
Qed.

Lemma agree_set_local:
  forall ls ls0 rs fr cs v ofs ty,
  agree ls ls0 rs fr cs ->
  slot_within_bounds f b (Local ofs ty) ->
  exists fr',
    set_slot tf.(fn_framesize) fr ty (Int.signed (Int.repr (offset_of_index fe (FI_local ofs ty)))) v = Some fr' /\
    agree (Locmap.set (S (Local ofs ty)) v ls) ls0 rs fr' cs.
Proof.
  intros.
  exists (set_index_val (FI_local ofs ty) v fr); split.
  set (idx := FI_local ofs ty). 
  change ty with (type_of_index idx).
  apply set_slot_index; unfold idx. auto with stacking. (* congruence. congruence. *)
  constructor; eauto with stacking.
  (* agree_reg *)
  intros. rewrite Locmap.gso. eauto with stacking. red; auto.
  (* agree_local *)
  intros. case (slot_eq (Local ofs ty) (Local ofs0 ty0)); intro.
  rewrite <- e. rewrite Locmap.gss. 
  replace (FI_local ofs0 ty0) with (FI_local ofs ty).
  symmetry. apply get_set_index_val_same. congruence.
  assert (ofs <> ofs0 \/ ty <> ty0).
    case (zeq ofs ofs0); intro. compare ty ty0; intro.
    congruence. tauto.  tauto. 
  rewrite Locmap.gso. rewrite get_set_index_val_other; eauto with stacking.
  red. auto.
  (* agree_outgoing *)
  intros. rewrite Locmap.gso. rewrite get_set_index_val_other; eauto with stacking.
  red; auto. red; auto.
  (* agree_incoming *)
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
  (* agree_saved_int *)
  intros. rewrite get_set_index_val_other; eauto with stacking.
  red; auto.
  (* agree_saved_float *)
  intros. rewrite get_set_index_val_other; eauto with stacking.
  red; auto.
Qed.

Lemma agree_set_outgoing:
  forall ls ls0 rs fr cs v ofs ty,
  agree ls ls0 rs fr cs ->
  slot_within_bounds f b (Outgoing ofs ty) ->
  exists fr',
    set_slot tf.(fn_framesize) fr ty (Int.signed (Int.repr (offset_of_index fe (FI_arg ofs ty)))) v = Some fr' /\
    agree (Locmap.set (S (Outgoing ofs ty)) v ls) ls0 rs fr' cs.
Proof.
  intros.
  exists (set_index_val (FI_arg ofs ty) v fr); split.
  set (idx := FI_arg ofs ty). 
  change ty with (type_of_index idx).
  apply set_slot_index; unfold idx. auto with stacking. (* congruence. congruence. *)
  constructor; eauto with stacking.
  (* agree_reg *)
  intros. rewrite Locmap.gso. eauto with stacking. red; auto.
  (* agree_local *)
  intros. rewrite Locmap.gso. rewrite get_set_index_val_other; eauto with stacking.
  red; auto. red; auto.
  (* agree_outgoing *)
  intros. unfold Locmap.set. 
  case (Loc.eq (S (Outgoing ofs ty)) (S (Outgoing ofs0 ty0))); intro.
  (* same location *)
  replace ofs0 with ofs by congruence. replace ty0 with ty by congruence.
  symmetry. apply get_set_index_val_same.
  (* overlapping locations *)
  caseEq (Loc.overlap (S (Outgoing ofs ty)) (S (Outgoing ofs0 ty0))); intros.
  symmetry. apply get_set_index_val_overlap; auto.
  (* disjoint locations *)
  rewrite get_set_index_val_other; eauto with stacking.
  red. eapply Loc.overlap_aux_false_1; eauto.
  (* agree_incoming *)
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
  (* saved ints *)
  intros. rewrite get_set_index_val_other; eauto with stacking. red; auto.
  (* saved floats *)
  intros. rewrite get_set_index_val_other; eauto with stacking. red; auto.
Qed.

Lemma agree_undef_regs:
  forall rl ls ls0 rs fr cs,
  agree ls ls0 rs fr cs ->
  (forall r, In r rl -> In (R r) temporaries) ->
  agree (Locmap.undef (List.map R rl) ls) ls0 (undef_regs rl rs) fr cs.
Proof.
  induction rl; intros; simpl.
  auto.
  eapply IHrl; eauto.
  apply agree_set_reg; auto with coqlib.
  assert (In (R a) temporaries) by auto with coqlib.
  red. destruct (mreg_type a).
  destruct (zlt (index_int_callee_save a) 0).
  generalize (bound_int_callee_save_pos b). omega.
  elim (int_callee_save_not_destroyed a). auto. apply index_int_callee_save_pos2; auto.
  destruct (zlt (index_float_callee_save a) 0).
  generalize (bound_float_callee_save_pos b). omega.
  elim (float_callee_save_not_destroyed a). auto. apply index_float_callee_save_pos2; auto.
  intros. apply H0. auto with coqlib.
Qed.

Lemma agree_undef_temps:
  forall ls ls0 rs fr cs,
  agree ls ls0 rs fr cs ->
  agree (LTL.undef_temps ls) ls0 (Mach.undef_temps rs) fr cs.
Proof.
  intros. unfold undef_temps, LTL.undef_temps.
  change temporaries with (List.map R (int_temporaries ++ float_temporaries)).
  apply agree_undef_regs; auto.
  intros.
  change temporaries with (List.map R (int_temporaries ++ float_temporaries)).
  apply List.in_map. auto.
Qed.

Lemma agree_undef_op:
  forall op env ls ls0 rs fr cs,
  agree ls ls0 rs fr cs ->
  agree (Linear.undef_op op ls) ls0 (Mach.undef_op (transl_op env op) rs) fr cs.
Proof.
  intros. exploit agree_undef_temps; eauto. intro.
  destruct op; simpl; auto.
Qed.

Lemma agree_undef_getparam:
  forall ls ls0 rs fr cs,
  agree ls ls0 rs fr cs ->
  agree (Locmap.set (R IT1) Vundef ls) ls0 (rs#IT1 <- Vundef) fr cs.
Proof.
  intros. exploit (agree_undef_regs (IT1 :: nil)); eauto.
  simpl; intros. intuition congruence.
Qed.

Lemma agree_return_regs:
  forall ls ls0 rs fr cs rs',
  agree ls ls0 rs fr cs ->
  (forall r,
    ~In r int_callee_save_regs -> ~In r float_callee_save_regs ->
    rs' r = rs r) ->
  (forall r,
    In r int_callee_save_regs \/ In r float_callee_save_regs ->
    rs' r = ls0 (R r)) ->
  (forall r, return_regs ls0 ls (R r) = rs' r).
Proof.
  intros; unfold return_regs.
  case (In_dec Loc.eq (R r) temporaries); intro.
  rewrite H0. eapply agree_reg; eauto. 
    apply int_callee_save_not_destroyed; auto.
    apply float_callee_save_not_destroyed; auto. 
  case (In_dec Loc.eq (R r) destroyed_at_call); intro.
  rewrite H0. eapply agree_reg; eauto.
  apply int_callee_save_not_destroyed; auto. 
    apply float_callee_save_not_destroyed; auto.
  symmetry; apply H1.
  generalize (register_classification r).  tauto. 
Qed. 

(** Agreement over callee-save registers and stack locations *)

Definition agree_callee_save (ls1 ls2: locset) : Prop :=
  forall l,
  match l with
  | R r => In r int_callee_save_regs \/ In r float_callee_save_regs
  | S s => True
  end ->
  ls2 l = ls1 l.

Definition agree_callee_save_regs (ls1 ls2: locset) : Prop :=
  forall l,
  match l with
  | R r => In r int_callee_save_regs \/ In r float_callee_save_regs
  | S s => False
  end ->
  ls2 l = ls1 l.

Definition agree_parent (ls : locset) (s : list stackframe) :=
  match s with
    | nil => agree_callee_save_regs ls (parent_locset s)
    | _   => agree_callee_save ls (parent_locset s)
  end.

Remark mreg_not_within_bounds:
  forall r,
  ~mreg_within_bounds b r -> In r int_callee_save_regs \/ In r float_callee_save_regs.
Proof.
  intro r; unfold mreg_within_bounds.
  destruct (mreg_type r); intro.
  left. apply index_int_callee_save_pos2. 
  generalize (bound_int_callee_save_pos b). omega.
  right. apply index_float_callee_save_pos2. 
  generalize (bound_float_callee_save_pos b). omega.
Qed.

Lemma agree_callee_save_regs_agree:
  forall ls ls1 ls2 rs fr cs,
  agree ls ls1 rs fr cs ->
  agree_callee_save_regs ls1 ls2 ->
  agree ls ls2 rs fr cs.
Proof.
  intros. inv H. constructor; auto.
  intros. rewrite agree_unused_reg0; auto.
  symmetry. apply H0. apply mreg_not_within_bounds; auto.
  intros. rewrite (H0 (R r)); auto. 
  intros. rewrite (H0 (R r)); auto. 
Qed.

Lemma agree_callee_save_impl_regs:
  forall ls ls'
    (AG: agree_callee_save ls ls'),
      agree_callee_save_regs ls ls'.
Proof.
  intros. intro l; specialize (AG l).
  by destruct l.
Qed.

Lemma agree_callee_save_agree:
  forall ls ls1 ls2 rs fr cs,
  agree ls ls1 rs fr cs ->
  agree_callee_save ls1 ls2 ->
  agree ls ls2 rs fr cs.
Proof.
  intros. 
  eauto using agree_callee_save_regs_agree, agree_callee_save_impl_regs.
Qed.

Lemma agree_callee_save_return_regs:
  forall ls1 ls2,
  agree_callee_save (return_regs ls1 ls2) ls1.
Proof.
  intros; red; intros.
  unfold return_regs. destruct l; auto.
  generalize (int_callee_save_not_destroyed m); intro.
  generalize (float_callee_save_not_destroyed m); intro.
  destruct (In_dec Loc.eq (R m) temporaries). tauto.
  destruct (In_dec Loc.eq (R m) destroyed_at_call). tauto.
  auto.
Qed.

Lemma agree_callee_save_set_result:
  forall ls1 ls2 v sg,
  agree_callee_save ls1 ls2 ->
  agree_callee_save (Locmap.set (R (Conventions.loc_result sg)) v ls1) ls2.
Proof.
  intros; red; intros. rewrite H; auto. 
  symmetry; apply Locmap.gso. destruct l; simpl; auto.
  red; intro. subst m. elim (loc_result_not_callee_save _ H0).
Qed.

Lemma agree_callee_save_regs_set_result:
  forall ls1 ls2 v sg,
  agree_callee_save_regs ls1 ls2 ->
  agree_callee_save_regs (Locmap.set (R (Conventions.loc_result sg)) v ls1) ls2.
Proof.
  intros; red; intros. rewrite H; auto. 
  symmetry; apply Locmap.gso. destruct l; simpl; auto.
  red; intro. subst m. elim (loc_result_not_callee_save _ H0).
Qed.

Lemma agree_parent_set_result:
  forall ls s v sg,
  agree_parent ls s ->
  agree_parent (Locmap.set (R (Conventions.loc_result sg)) v ls) s.
Proof.
  intros; destruct s; simpl in *; 
    eauto using agree_callee_save_regs_set_result, agree_callee_save_set_result.
Qed.

(** A variant of [agree] used for return frames. *)

Definition agree_frame (ls ls0: locset) (fr: frame) (cs: stackframes): Prop :=
  exists rs, agree ls ls0 rs fr cs.

Lemma agree_frame_agree:
  forall ls1 ls2 rs fr cs ls0,
  agree_frame ls1 ls0 fr cs ->
  agree_callee_save ls2 ls1 ->
  (forall r, rs r = ls2 (R r)) ->
  agree ls2 ls0 rs fr cs.
Proof.
  intros. destruct H as [rs' AG]. inv AG.
  constructor; auto.
  intros. rewrite <- agree_unused_reg0; auto.
  rewrite <- agree_reg0. rewrite H1. symmetry; apply H0.
  apply mreg_not_within_bounds; auto.
  intros. rewrite <- H0; auto.
  intros. rewrite <- H0; auto.
  intros. rewrite <- H0; auto.
Qed.

(** * Correctness of saving and restoring of callee-save registers *)

(** The following lemmas show the correctness of the register saving
  code generated by [save_callee_save]: after this code has executed,
  the register save areas of the current frame do contain the
  values of the callee-save registers used by the function. *)

Section SAVE_CALLEE_SAVE.

Variable bound: frame_env -> Z.
Variable number: mreg -> Z.
Variable mkindex: Z -> frame_index.
Variable ty: typ.
Variable sp: option pointer.
Variable csregs: list mreg.

Hypothesis number_inj: 
  forall r1 r2, In r1 csregs -> In r2 csregs -> r1 <> r2 -> number r1 <> number r2.
Hypothesis mkindex_valid:
  forall r, In r csregs -> number r < bound fe -> index_valid (mkindex (number r)).
(*
Hypothesis mkindex_not_link:
  forall z, mkindex z <> FI_link.
Hypothesis mkindex_not_retaddr:
  forall z, mkindex z <> FI_retaddr.
*)
Hypothesis mkindex_typ:
  forall z, type_of_index (mkindex z) = ty.
Hypothesis mkindex_inj:
  forall z1 z2, z1 <> z2 -> mkindex z1 <> mkindex z2.
Hypothesis mkindex_diff:
  forall r idx,
  idx <> mkindex (number r) -> index_diff (mkindex (number r)) idx.

Lemma save_callee_save_regs_correct:
  forall l k rs fr,
  incl l csregs ->
  NoDup l ->
  exists fr',
    taustar tlts 
       (State stack tf sp
         (save_callee_save_regs bound number mkindex ty fe l k) rs fr)
       (State stack tf sp k rs fr')
  /\ (forall r,
       In r l -> number r < bound fe ->
       index_val (mkindex (number r)) fr' = rs r)
  /\ (forall idx,
       index_valid idx ->
       (forall r,
         In r l -> number r < bound fe -> idx <> mkindex (number r)) ->
       index_val idx fr' = index_val idx fr).
Proof.
  induction l; intros; simpl save_callee_save_regs.
  (* base case *)
  exists fr. split. apply taustar_refl.
  split. intros. elim H1.
  auto.
  (* inductive case *)
  set (k1 := save_callee_save_regs bound number mkindex ty fe l k).
  assert (R1: incl l csregs). eauto with coqlib.
  assert (R2: NoDup l). inversion H0; auto.
  unfold save_callee_save_reg.
  destruct (zlt (number a) (bound fe)).
  (* a store takes place *)
  set (fr1 := set_index_val (mkindex (number a)) (rs a) fr).
  exploit (IHl k rs fr1); auto. 
  fold k1. intros [fr' [A [B C]]].
  exists fr'.
  split. eapply taustar_step; simpl. 
  apply exec_Msetstack. instantiate (1 := fr1). 
  unfold fr1. rewrite <- (mkindex_typ (number a)).
  eapply set_slot_index; eauto with coqlib.
  eexact A.
  split. intros. simpl in H1. destruct H1. subst r.
    rewrite C. unfold fr1. apply get_set_index_val_same.
    apply mkindex_valid; auto with coqlib.
    intros. apply mkindex_inj. apply number_inj; auto with coqlib.
    inversion H0. congruence.
    apply B; auto.
  intros. rewrite C; auto with coqlib. 
    unfold fr1. apply get_set_index_val_other; auto with coqlib. 
  (* no store takes place *)
  exploit (IHl k rs fr); auto. intros [fr' [A [B C]]].
  exists fr'.
  split. exact A.
  split. intros. simpl in H1; destruct H1. subst r. omegaContradiction.
    apply B; auto. 
  intros. apply C; auto with coqlib.
Qed.

End SAVE_CALLEE_SAVE. 

Lemma save_callee_save_int_correct:
  forall k sp rs fr,
  exists fr',
    taustar tlts 
       (State stack tf sp
         (save_callee_save_int fe k) rs fr)
       (State stack tf sp k rs fr')
  /\ (forall r,
       In r int_callee_save_regs ->
       index_int_callee_save r < bound_int_callee_save b ->
       index_val (FI_saved_int (index_int_callee_save r)) fr' = rs r)
  /\ (forall idx,
       index_valid idx ->
       match idx with FI_saved_int _ => False | _ => True end ->
       index_val idx fr' = index_val idx fr).
Proof.
  intros.
  exploit (save_callee_save_regs_correct fe_num_int_callee_save index_int_callee_save FI_saved_int
                                         Tint sp int_callee_save_regs); try done.
  exact index_int_callee_save_inj.
  intros. red. split; auto. generalize (index_int_callee_save_pos r H). omega.
  intro; congruence.
  auto.
  intros until idx. destruct idx; simpl; auto. congruence.
  apply incl_refl.
  apply int_callee_save_norepet.
  intros [fr' [A [B C]]]. 
  exists fr'; intuition. unfold save_callee_save_int; eauto. 
  apply C. auto. intros; subst idx. auto.
Qed.

Lemma save_callee_save_float_correct:
  forall k sp rs fr,
  exists fr',
    taustar tlts 
       (State stack tf sp
         (save_callee_save_float fe k) rs fr)
       (State stack tf sp k rs fr')
  /\ (forall r,
       In r float_callee_save_regs ->
       index_float_callee_save r < bound_float_callee_save b ->
       index_val (FI_saved_float (index_float_callee_save r)) fr' = rs r)
  /\ (forall idx,
       index_valid idx ->
       match idx with FI_saved_float _ => False | _ => True end ->
       index_val idx fr' = index_val idx fr).
Proof.
  intros.
  exploit (save_callee_save_regs_correct fe_num_float_callee_save index_float_callee_save FI_saved_float
                                         Tfloat sp float_callee_save_regs);
  try exact index_float_callee_save_inj; try apply incl_refl; try done; try (intros; congruence).
  - destruct idx; simpl; auto; congruence.
  - by apply float_callee_save_norepet. 
  by intros [fr' [A [B C]]]; exists fr'; intuition; unfold save_callee_save_float; eauto. 
Qed.

Lemma save_callee_save_correct:
  forall sp k rs ls cs,
  (forall r, rs r = ls (R r)) ->
  (forall ofs ty,
     In (S (Outgoing ofs ty)) (loc_arguments f.(Linear.fn_sig)) ->
     get_parent_slot cs ofs ty (ls (S (Outgoing ofs ty)))) ->
  exists fr',
    taustar tlts
       (State stack tf sp (save_callee_save fe k) rs empty_frame)
       (State stack tf sp k rs fr')
  /\ agree (call_regs ls) ls rs fr' cs.
Proof.
  intros. unfold save_callee_save.
  exploit save_callee_save_int_correct; eauto. 
  intros [fr1 [A1 [B1 C1]]].
  exploit save_callee_save_float_correct. 
  intros [fr2 [A2 [B2 C2]]].
  exists fr2.
  split. eapply taustar_trans. eexact A1. eexact A2.
  constructor; unfold call_regs; auto.
  (* agree_local *)
  intros. rewrite C2; auto with stacking. 
  rewrite C1; auto with stacking. 
  (* agree_outgoing *)
  intros. rewrite C2; auto with stacking. 
  rewrite C1; auto with stacking.
  (* agree_incoming *)
  intros. apply H0. unfold loc_parameters in H1.
  exploit list_in_map_inv; eauto. intros [l [A B]].
  exploit loc_arguments_acceptable; eauto. intro C.
  destruct l; simpl in A; try done.
  simpl in C. destruct s; try contradiction. inv A. auto.
  (* agree_saved_int *)
  intros. rewrite C2; auto with stacking.
  rewrite B1; auto with stacking. 
  (* agree_saved_float *)
  intros. rewrite B2; auto with stacking. 
Qed.

(** The following lemmas show the correctness of the register reloading
  code generated by [reload_callee_save]: after this code has executed,
  all callee-save registers contain the same values they had at
  function entry. *)

Section RESTORE_CALLEE_SAVE.

Variable bound: frame_env -> Z.
Variable number: mreg -> Z.
Variable mkindex: Z -> frame_index.
Variable ty: typ.
Variable sp: option pointer.
Variable csregs: list mreg.
Hypothesis mkindex_valid:
  forall r, In r csregs -> number r < bound fe -> index_valid (mkindex (number r)).
(*
Hypothesis mkindex_not_link:
  forall z, mkindex z <> FI_link.
Hypothesis mkindex_not_retaddr:
  forall z, mkindex z <> FI_retaddr.
*)
Hypothesis mkindex_typ:
  forall z, type_of_index (mkindex z) = ty.
Hypothesis number_within_bounds:
  forall r, In r csregs ->
  (number r < bound fe <-> mreg_within_bounds b r).
Hypothesis mkindex_val:
  forall ls ls0 rs fr cs r, 
  agree ls ls0 rs fr cs -> In r csregs -> number r < bound fe ->
  index_val (mkindex (number r)) fr = ls0 (R r).

Lemma restore_callee_save_regs_correct:
  forall k fr ls0 l ls rs cs
  (IN: incl l csregs)
  (ND: NoDup l)
  (AGREE: agree ls ls0 rs fr cs),
  exists ls', exists rs',
    taustar tlts
      (State stack tf sp
        (restore_callee_save_regs bound number mkindex ty fe l k) rs fr)
      (State stack tf sp k rs' fr)
  /\ (forall r, In r l -> rs' r = ls0 (R r))
  /\ (forall r, ~(In r l) -> rs' r = rs r)
  /\ agree ls' ls0 rs' fr cs.
Proof.
  induction l; intros; simpl restore_callee_save_regs.
  (* base case *)
  exists ls; exists rs. 
  split; [apply taustar_refl|]. 
  by split; [inversion 1|].
  (* inductive case *)
  set (k1 := restore_callee_save_regs bound number mkindex ty fe l k).
  assert (R0: In a csregs) by (apply IN; auto with coqlib).
  assert (R1: incl l csregs) by eauto with coqlib.
  assert (R2: NoDup l) by (inversion ND; auto).
  unfold restore_callee_save_reg.
  destruct (zlt (number a) (bound fe)).
  set (ls1 := Locmap.set (R a) (ls0 (R a)) ls).
  set (rs1 := Regmap.set a (ls0 (R a)) rs).
  assert (R3: agree ls1 ls0 rs1 fr cs). 
    unfold ls1, rs1. apply agree_set_reg. auto. 
    rewrite <- number_within_bounds; auto. 
  generalize (IHl ls1 rs1 cs R1 R2 R3). 
  intros [ls' [rs' [A [B [C D]]]]].
  exists ls'. exists rs'. split. 
  apply taustar_step with (State stack tf sp k1 rs1 fr); simpl.
  apply exec_Mgetstack. apply get_slot_index; auto.
  symmetry. eapply mkindex_val; eauto.  
  auto.
  split. inversion 1; intros.
  subst r. rewrite C. unfold rs1. apply Regmap.gss. inversion ND; auto.
  auto.
  split; try done; intros. simpl in *. rewrite C. unfold rs1. apply Regmap.gso.
  apply sym_not_eq; tauto. tauto.
  (* no load takes place *)
  generalize (IHl ls rs cs R1 R2 AGREE).  
  intros [ls' [rs' [A [B [C D]]]]].
  exists ls'; exists rs'. split. assumption.
  split. inversion 1; intros. 
  subst r. apply (agree_unused_reg _ _ _ _ _ D).
  rewrite <- number_within_bounds. auto. auto. auto.
  split; try done; intros; apply C; simpl in *; tauto.
Qed.

End RESTORE_CALLEE_SAVE.

Lemma restore_int_callee_save_correct:
  forall sp k fr ls0 ls rs cs,
  agree ls ls0 rs fr cs ->
  exists ls', exists rs',
    taustar tlts
       (State stack tf sp
         (restore_callee_save_int fe k) rs fr)
       (State stack tf sp k rs' fr)
  /\ (forall r, In r int_callee_save_regs -> rs' r = ls0 (R r))
  /\ (forall r, ~(In r int_callee_save_regs) -> rs' r = rs r)
  /\ agree ls' ls0 rs' fr cs.
Proof.
  intros. unfold restore_callee_save_int.
  apply restore_callee_save_regs_correct with int_callee_save_regs ls; try done.
    by intros ? X; split; auto; generalize (index_int_callee_save_pos _ X); omega.
    by intros ? X; unfold mreg_within_bounds; rewrite (int_callee_save_type _ X); tauto. 
    by eauto with stacking. 
  apply int_callee_save_norepet.
Qed.

Lemma restore_float_callee_save_correct:
  forall sp k fr ls0 ls rs cs,
  agree ls ls0 rs fr cs ->
  exists ls', exists rs',
    taustar tlts
       (State stack tf sp
          (restore_callee_save_float fe k) rs fr)
       (State stack tf sp k rs' fr)
  /\ (forall r, In r float_callee_save_regs -> rs' r = ls0 (R r))
  /\ (forall r, ~(In r float_callee_save_regs) -> rs' r = rs r)
  /\ agree ls' ls0 rs' fr cs.
Proof.
  intros. unfold restore_callee_save_float.
  apply restore_callee_save_regs_correct with float_callee_save_regs ls; try done.
(*    by intros ? X; split; auto; generalize (index_float_callee_save_pos _ X); omega.
    by intros ? X; unfold mreg_within_bounds; rewrite (float_callee_save_type _ X); tauto. 
    by eauto with stacking. *)
  apply float_callee_save_norepet.
Qed.

Lemma restore_callee_save_correct:
  forall sp k fr ls0 ls rs cs,
  agree ls ls0 rs fr cs ->
  exists rs',
    taustar tlts
       (State stack tf sp (restore_callee_save fe k) rs fr)
       (State stack tf sp k rs' fr)
  /\ (forall r, 
        In r int_callee_save_regs \/ In r float_callee_save_regs -> 
        rs' r = ls0 (R r))
  /\ (forall r, 
        ~(In r int_callee_save_regs) ->
        ~(In r float_callee_save_regs) ->
        rs' r = rs r).
Proof.
  intros. unfold restore_callee_save.
  exploit restore_int_callee_save_correct; eauto.
  intros [ls1 [rs1 [A [B [C D]]]]].
  exploit restore_float_callee_save_correct. eexact D.
  intros [ls2 [rs2 [P [Q [R S]]]]].
  exists rs2. split. eapply taustar_trans. eexact A. eexact P.
  split. intros. elim H0; intros.
  rewrite R. apply B. auto. apply list_disjoint_notin with int_callee_save_regs.
  apply int_float_callee_save_disjoint. auto.
  apply Q. auto.
  intros. rewrite R. apply C. auto. auto.
Qed.

End FRAME_PROPERTIES.

(** * Semantic preservation *)

Definition stacksize_of_fn f := 
  align_stacksize (Int.unsigned f.(Linear.fn_stacksize)) fe_retaddrsize.

Definition framesize_of_fn f := 
  let fe := make_env (function_bounds f) in
  align_framesize (stacksize_of_fn f) fe.(fe_size) fe_retaddrsize.

(** Preservation of code labels through the translation. *)

Section LABELS.

Remark find_label_fold_right:
  forall (A: Type) (fn: A -> Mach.code -> Mach.code) lbl,
  (forall x k, Mach.find_label lbl (fn x k) = Mach.find_label lbl k) ->  forall (args: list A) k,
  Mach.find_label lbl (List.fold_right fn k args) = Mach.find_label lbl k.
Proof.
  induction args; simpl. auto. 
  intros. rewrite H. auto.
Qed.

Remark find_label_save_callee_save:
  forall fe lbl k,
  Mach.find_label lbl (save_callee_save fe k) = Mach.find_label lbl k.
Proof.
  intros. unfold save_callee_save, save_callee_save_int, save_callee_save_float, save_callee_save_regs.
  repeat rewrite find_label_fold_right. reflexivity.
  intros. unfold save_callee_save_reg. 
  case (zlt (index_float_callee_save x) (fe_num_float_callee_save fe));
  intro; reflexivity.
  intros. unfold save_callee_save_reg.  
  case (zlt (index_int_callee_save x) (fe_num_int_callee_save fe));
  intro; reflexivity.
Qed.

Remark find_label_restore_callee_save:
  forall fe lbl k,
  Mach.find_label lbl (restore_callee_save fe k) = Mach.find_label lbl k.
Proof.
  intros. unfold restore_callee_save, restore_callee_save_int, restore_callee_save_float, restore_callee_save_regs.
  rewrite !find_label_fold_right; try done;
  by intros; unfold restore_callee_save_reg; case zlt.
Qed.

Lemma find_label_transl_code:
  forall fe shift lbl c,
  Mach.find_label lbl (transl_code fe shift c) =
    option_map (transl_code fe shift) (Linear.find_label lbl c).
Proof.
  induction c; simpl; intros; try done.
  destruct a; unfold transl_instr; 
    try rewrite find_label_restore_callee_save; try done. 
  by destruct s. 
  by destruct s.
  by simpl; case peq.
Qed.

Lemma transl_find_label:
  forall f tf lbl c,
  transf_function f = OK tf ->
  Linear.find_label lbl f.(Linear.fn_code) = Some c ->
  Mach.find_label lbl tf.(Mach.fn_code) = 
    Some (transl_code (make_env (function_bounds f)) (framesize_of_fn f) c).
Proof.
  intros. 
  rewrite (unfold_transf_function _ _ H). unfold fn_code.
  by unfold transl_body; rewrite find_label_save_callee_save, 
    find_label_transl_code, H0. 
Qed.

End LABELS.

(** Code inclusion property for Linear executions. *)

Lemma find_label_incl:
  forall lbl c c', 
  Linear.find_label lbl c = Some c' -> incl c' c.
Proof.
  induction c; simpl; try done.
  intro c'. case (Linear.is_label lbl a); intros.
  injection H; intro; subst c'. red; intros; auto with coqlib. 
  apply incl_tl. auto.
Qed.

(** Preservation / translation of global symbols and functions. *)

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = OK tf.
Proof.
  intros v f H.
  pose proof (proj2 TRANSF v).
  destruct (Genv.find_funct_ptr ge v);
   destruct (Genv.find_funct_ptr tge v); try done.
  clarify; eexists; done.
Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof.
  intros v f H.
  destruct v as [| |p|]; try done; simpl in *.
  apply function_ptr_translated; done.
Qed.

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. by intros; destruct TRANSF. Qed.

Lemma sig_preserved:
  forall f tf,
  transf_fundef f = OK tf ->
  Mach.funsig tf = Linear.funsig f.
Proof.
  intros [] ? H; monadInv H; try done; revert EQ.
  unfold transf_function. 
  (* case ifP; try done. *)
  by repeat (destruct zle); intros; clarify.
Qed.

Lemma find_function_translated:
  forall f0 ls ls0 rs fr cs ros f,
  agree f0 ls ls0 rs fr cs ->
  Linear.find_function ge ros ls = Some f ->
  exists tf,
  find_function tge ros rs = Some tf /\ transf_fundef f = OK tf.
Proof.
  intros until f; intro AG.
  destruct ros; simpl.
  rewrite (agree_eval_reg _ _ _ _ _ _ m AG). intro.
  apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); try congruence.
  intro. apply function_ptr_translated; auto.
Qed.

Hypothesis wt_ge: forall x f, Genv.find_funct_ptr ge x = Some f -> wt_fundef f.

Lemma find_function_well_typed:
  forall ros ls f,
  Linear.find_function ge ros ls = Some f -> wt_fundef f.
Proof.
  intros until f; destruct ros; simpl.
    by destruct ls; try done; eauto.
  by destruct Genv.find_symbol; try done; eauto.
Qed.

(** Correctness of stack pointer relocation in operations and
  addressing modes. *)

Definition shift_sp (tf: Mach.function) (sp: option pointer) :=
  match sp with
  | None => None
  | Some p => Some (MPtr.add p (Int.repr (-tf.(fn_framesize))))
  end.

Remark shift_offset_sp:
  forall f tf sp n v,
  transf_function f = OK tf ->
  offset_sp sp n = Some v ->
  offset_sp (shift_sp tf sp)
    (Int.add (Int.repr (framesize_of_fn f)) n) = Some v.
Proof.
  intros. destruct sp; try done.
  unfold offset_sp in *. 
  unfold shift_sp. 
  rewrite (unfold_transf_function _ _ H). unfold fn_framesize.
  clarify.
  f_equal; f_equal.
  rewrite <- Int.neg_repr, <- MPtr.add_add_r, <- Int.add_assoc.
  f_equal.
  rewrite <- (Int.add_zero n) at 2; rewrite <- (Int.add_commut n).
  f_equal.
  rewrite Int.add_commut; apply Int.add_neg_zero.
Qed.

Lemma shift_eval_addressing:
  forall f tf sp addr args v,
  transf_function f = OK tf ->
  eval_addressing ge sp addr args = Some v ->
  eval_addressing tge (shift_sp tf sp) 
                 (transl_addr (framesize_of_fn f) addr) args =
  Some v.
Proof.
  intros; unfold transl_addr, eval_addressing, shift_stack_addressing in *;
  destruct addr; try (rewrite symbols_preserved); auto.
  destruct args; try done.
  by apply shift_offset_sp.
Qed.

Lemma shift_eval_operation:
  forall f tf sp op args v,
  transf_function f = OK tf ->
  eval_operation ge sp op args = Some v ->
  eval_operation tge (shift_sp tf sp) 
                 (transl_op (framesize_of_fn f) op) args = Some v.
Proof.
  intros until v. destruct op; intros; auto; simpl in *.
  by apply shift_eval_addressing.
Qed.

(** Preservation of the arguments to an external call. *)

Section EXTERNAL_ARGUMENTS.

Variable cs: Machabstr.stackframes.
Variable ls: locset.
Variable rs: regset.
Variable sg: signature.

Hypothesis AG1: forall r, rs r = ls (R r).
Hypothesis AG2: forall (ofs : Z) (ty : typ),
      In (S (Outgoing ofs ty)) (loc_arguments sg) ->
      get_parent_slot cs ofs ty (ls (S (Outgoing ofs ty))).

Lemma transl_external_arguments_rec:
  forall locs,
  incl locs (loc_arguments sg) ->
  extcall_args (parent_size cs) rs (parent_frame cs) locs = Some (map ls locs).
Proof.
   unfold extcall_args in *.
  induction locs; simpl; try done; intros INCL.
  rewrite IHlocs; [|apply (incl_cons_inv INCL)].
  assert (loc_argument_acceptable a). 
    by apply loc_arguments_acceptable with sg; auto with coqlib.
  destruct a as [|[]]; try done.
  by rewrite <- AG1.
  unfold extcall_arg; unfold get_parent_slot in AG2; rewrite AG2; try done.
  by apply INCL; left.
Qed.

Lemma transl_external_arguments:
  extcall_arguments (parent_size cs) rs (parent_frame cs) sg (map ls (loc_arguments sg)).
Proof.
  unfold extcall_arguments. 
  apply transl_external_arguments_rec.
  auto with coqlib.
Qed.

End EXTERNAL_ARGUMENTS.

(** The proof of semantic preservation relies on simulation diagrams
  of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                  +|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  Matching between source and target states is defined by [match_states]
  below.  It implies:
- Agreement between, on the Linear side, the location sets [ls]
  and [parent_locset s] of the current function and its caller,
  and on the Mach side the register set [rs], the frame [fr]
  and the caller's frame [parent_frame ts].
- Inclusion between the Linear code [c] and the code of the
  function [f] being executed.
- Well-typedness of [f].
*)

Inductive match_stacks: list Linear.stackframe -> Machabstr.stackframes -> Prop :=
  | match_stacks_nil: forall fr sz,
      match_stacks nil (Stackbase fr sz)
  | match_stacks_cons:
      forall f sp c ls tf fr s ts,
      match_stacks s ts ->
      transf_function f = OK tf ->
      wt_function f ->
      agree_frame f ls (parent_locset s) fr ts ->
      incl c (Linear.fn_code f) ->
      match_stacks
       (Linear.Stackframe f sp ls c :: s)
       (Machabstr.Stackframe tf (shift_sp tf sp) 
         (transl_code (make_env (function_bounds f)) (framesize_of_fn f) c) fr ts).

Inductive match_states: Linear.state -> Machabstr.state -> Prop :=
  | match_states_intro:
      forall s f sp c ls ts tf rs fr
        (STACKS: match_stacks s ts)
        (TRANSL: transf_function f = OK tf)
        (WTF: wt_function f)
        (AG: agree f ls (parent_locset s) rs fr ts)
        (INCL: incl c (Linear.fn_code f)),
      match_states (Linear.State s f sp c ls)
                   (Machabstr.State ts tf (shift_sp tf sp) (transl_code (make_env (function_bounds f)) (framesize_of_fn f) c) rs fr)
  | match_states_call:
      forall s f ls ts tf rs
        (STACKS: match_stacks s ts)
        (TRANSL: transf_fundef f = OK tf)
        (WTF: wt_fundef f)
        (AG1: forall r, rs r = ls (R r))
        (AG2: forall ofs ty, 
                In (S (Outgoing ofs ty)) (loc_arguments (Linear.funsig f)) ->
                get_parent_slot ts ofs ty (ls (S (Outgoing ofs ty))))
        (AG3: agree_parent ls s),
      match_states (Linear.Callstate s f ls)
                   (Machabstr.Callstate ts tf rs)
  | match_states_return:
      forall s ls ts rs
        (STACKS: match_stacks s ts)
        (AG1: forall r, rs r = ls (R r))
        (AG2: agree_parent ls s),
      match_states (Linear.Returnstate s ls)
                   (Machabstr.Returnstate ts rs)
  | match_states_blocked:
      forall s ls ts rs efsig
        (STACKS: match_stacks s ts)
        (AG1: forall r, rs r = ls (R r))
        (AG2: agree_parent ls s),
      match_states (Linear.Blockedstate s ls efsig)
                   (Machabstr.Blockedstate ts rs efsig).


Theorem transf_step_correct:
  forall s1 t s2, Linear.step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', weakstep tlts s1' t s2' /\ match_states s2 s2'.
Proof.
  Opaque Zplus Zmult offset_of_index.
  assert (RED: forall f i c,
          transl_code (make_env (function_bounds f)) (framesize_of_fn f) (i :: c) = 
          transl_instr (make_env (function_bounds f)) (framesize_of_fn f) i
                       (transl_code (make_env (function_bounds f)) (framesize_of_fn f) c)) by done.
  (step_cases (destruct 1) Case); simpl; intros;
  try inv MS;
  try rewrite RED;
  try (generalize (WTF _ (INCL _ (in_eq _ _))); intro WTI);
  try (generalize (function_is_within_bounds f WTF _ (INCL _ (in_eq _ _)));
       intro BOUND; simpl in BOUND);
  unfold transl_instr.
  Case "exec_Lgetstack".
  inv WTI. destruct BOUND.
  exists (State ts tf (shift_sp tf sp) (transl_code (make_env (function_bounds f)) (framesize_of_fn f) b)
             (rs0#r <- (rs (S sl))) fr).
  split. destruct sl. 
  (* Lgetstack, local *)
  apply step_weakstep; simpl; apply exec_Mgetstack.
  apply get_slot_index; try done.
  eapply agree_locals; eauto.
  (* Lgetstack, incoming *)
  apply step_weakstep; simpl; apply exec_Mgetparam.
  change (get_parent_slot ts z t (rs (S (Incoming z t)))).
  eapply agree_incoming; eauto.
  (* Lgetstack, outgoing *)
  apply step_weakstep; simpl; apply exec_Mgetstack.
  apply get_slot_index; try done.
  eapply agree_outgoing; eauto.
  (* Lgetstack, common *)
  econstructor; eauto with coqlib. 
  apply agree_set_reg; auto.

  Case "exec_Lsetstack".
  inv WTI. destruct sl.

  (* Lsetstack, local *)
  generalize (agree_set_local _ _ TRANSL _ _ _ _ _ (rs0 r) _ _ AG BOUND).
  intros [fr' [SET AG']].
  econstructor; split.
  apply step_weakstep; simpl; eapply exec_Msetstack; eauto.
  econstructor; eauto with coqlib.
  replace (rs (R r)) with (rs0 r). auto.
  symmetry. eapply agree_reg; eauto.
  (* Lsetstack, incoming *)
  contradiction.
  (* Lsetstack, outgoing *)
  generalize (agree_set_outgoing _ _ TRANSL _ _ _ _ _ (rs0 r) _ _ AG BOUND).
  intros [fr' [SET AG']].
  econstructor; split.
  apply step_weakstep; simpl; eapply exec_Msetstack; eauto.
  econstructor; eauto with coqlib.
  replace (rs (R r)) with (rs0 r). auto.
  symmetry. eapply agree_reg; eauto.

  Case "exec_Lop".
  eexists; split.
  eapply step_weakstep; simpl; apply exec_Mop. 
    apply shift_eval_operation; auto. 
  eby change mreg with RegEq.t; rewrite (agree_eval_regs _ _ _ _ _ _ args AG).
  econstructor; eauto with coqlib.
  auto using agree_set_reg, agree_undef_op.

  Case "exec_Lload".
  eexists; split. 
  apply step_weakstep; simpl; eapply exec_Mload; eauto.
  - apply shift_eval_addressing; auto.
    eby change mreg with RegEq.t; rewrite (agree_eval_regs _ _ _ _ _ _ args AG).
  econstructor; eauto with coqlib.
  auto using agree_set_reg, agree_undef_temps.

  Case "exec_Lstore".
  econstructor; split.
  apply step_weakstep; simpl. eapply exec_Mstore; eauto.
  - apply shift_eval_addressing; auto.
    eby change mreg with RegEq.t; rewrite (agree_eval_regs _ _ _ _ _ _ args AG).
  by rewrite (agree_eval_reg _ _ _ _ _ _ src AG).
  econstructor; eauto using agree_undef_temps with coqlib.

  Case "exec_Lcall".
  assert (WTF': wt_fundef f') by (eapply find_function_well_typed; eauto).
  exploit find_function_translated; eauto. 
  intros [tf' [FIND' TRANSL']].
  econstructor; split.
  apply step_weakstep; simpl; eapply exec_Mcall; eauto.
  econstructor; eauto. 
  econstructor; eauto with coqlib.
  exists rs0; auto.
  intro. symmetry. eapply agree_reg; eauto.
  intros.
  assert (slot_within_bounds f (function_bounds f) (Outgoing ofs ty)).
  red. simpl. generalize (loc_arguments_bounded _ _ _ H0). 
  generalize (loc_arguments_acceptable _ _ H0). unfold loc_argument_acceptable. 
  omega.
  unfold get_parent_slot, parent_size, parent_frame.
  change (4 * ofs)
    with (offset_of_index (make_env (function_bounds f)) (FI_arg ofs ty)).
  apply get_slot_index; simpl; auto. 
  eapply agree_outgoing; eauto.
  simpl. red; auto.

  Case "exec_Llabel".
  econstructor; split.
  apply step_weakstep; simpl; apply exec_Mlabel.
  econstructor; eauto with coqlib.

  Case "exec_Lgoto".
  econstructor; split.
  apply step_weakstep; simpl; apply exec_Mgoto.
  apply transl_find_label; eauto.
  econstructor; eauto. 
  eapply find_label_incl; eauto.

  Case "exec_Lcond_true".
  econstructor; split.
  apply step_weakstep; simpl; apply exec_Mcond_true.
  rewrite <- (agree_eval_regs _ _ _ _ _ _ args AG) in H; eauto.
  apply transl_find_label; eauto.
  econstructor; eauto using agree_undef_temps, find_label_incl.

  Case "exec_Lcond_false".
  econstructor; split.
  apply step_weakstep; simpl; apply exec_Mcond_false.
  rewrite <- (agree_eval_regs _ _ _ _ _ _ args AG) in H; auto.
  econstructor; eauto using agree_undef_temps with coqlib.

  Case "exec_Lreturn".
  exploit restore_callee_save_correct; eauto.
  intros [ls' [A [B C]]].
  econstructor; split.
  eapply taustar_weakstep; [eassumption|].
  eapply step_weakstep; simpl; econstructor; eauto. 
    destruct sp; simpl; try done.
    destruct p; simpl.
    by rewrite <- Int.neg_repr, Int.add_assoc, (Int.add_commut (Int.neg _)), Int.add_neg_zero, Int.add_zero.
  econstructor; eauto.
  intros. symmetry. eapply agree_return_regs; eauto.
  destruct s; [apply agree_callee_save_impl_regs|];
    apply agree_callee_save_return_regs.  

  Case "exec_Lthreadcreate".
  assert (Y0: slot_within_bounds f (function_bounds f) (Outgoing 0 Tint))
    by (constructor; try done; revert BOUND; clear; 
        change (size_arguments thread_create_sig) with 2; simpl; intros; omega).
  assert (Y1: slot_within_bounds f (function_bounds f) (Outgoing 1 Tint))
    by (constructor; try done; revert BOUND; clear; 
        change (size_arguments thread_create_sig) with 2; simpl; intros; omega).
  clear BOUND.

  eexists; split.
  1: eapply step_weakstep; simpl; econstructor; eauto.
  2: by econstructor; eauto with coqlib.
  exploit (get_slot_index _ _ TRANSL fr (FI_arg 0 Tint)); try edone; intro X0. 
  exploit (get_slot_index _ _ TRANSL fr (FI_arg 1 Tint)); try edone; intro X1. 
  rewrite <- H.
  unfold extcall_arguments.
  unfold extcall_args; simpl in *.
  change (4 * 0) with (offset_of_index (make_env (function_bounds f))  (FI_arg 0 Tint)).
  rewrite X0; simpl.
  change (4 * (0 + 1)) with (offset_of_index (make_env (function_bounds f))  (FI_arg 1 Tint)).
  rewrite X1; simpl.
  symmetry; f_equal; f_equal; [|f_equal]; eapply agree_outgoing; eauto.

  Case "exec_Latomic".
  eexists; split.
  - eapply step_weakstep; simpl; econstructor; eauto.
    eby change mreg with RegEq.t; rewrite (agree_eval_regs _ _ _ _ _ _ args AG).
  by econstructor; eauto using agree_set_reg, agree_undef_temps with coqlib.

  Case "exec_Lfence".
  eexists; split; [by eapply step_weakstep; simpl; vauto|].
  by econstructor; eauto using agree_set_reg, agree_undef_temps with coqlib.

  Case "exec_function_internal_empty".
  generalize TRANSL; clear TRANSL. 
  unfold transf_fundef, transf_partial_fundef.
  caseEq (transf_function f); simpl; try done. 
  intros tfn TRANSL EQ. inversion EQ; clear EQ; subst tf.
  inversion WTF as [|f' WTFN]. subst f'.
  set (tsp := shift_sp tfn None).
  set (fe := make_env (function_bounds f)).
  exploit save_callee_save_correct; eauto. 
  intros [fr [EXP AG]].
  econstructor; split.
  eapply step_taustar_weakstep; simpl.
  eapply exec_function_internal_empty; eauto;
    try by rewrite (unfold_transf_function f tfn TRANSL).
  replace (Mach.fn_code tfn) with
          (transl_body f (make_env (function_bounds f)) (framesize_of_fn f));
    [|by rewrite (unfold_transf_function f tfn TRANSL); simpl].
  unfold transl_body. eexact EXP.
  unfold tsp, shift_sp. 
  econstructor; eauto with coqlib.
  by destruct s; 
    eauto using agree_callee_save_regs_agree, agree_callee_save_impl_regs.

  Case "exec_function_internal_nonempty".
  generalize TRANSL; clear TRANSL. 
  unfold transf_fundef, transf_partial_fundef.
  caseEq (transf_function f); simpl; try congruence.
  intros tfn TRANSL EQ. inversion EQ; clear EQ; subst tf.
  inversion WTF as [|f' WTFN]. subst f'.
  set (tsp := shift_sp tfn (Some stk)).
  set (fe := make_env (function_bounds f)).
  exploit save_callee_save_correct; eauto. 
  intros [fr [EXP AG]].
  econstructor; split.
  eapply step_taustar_weakstep; simpl.
  eapply exec_function_internal_nonempty; eauto;
    try by rewrite (unfold_transf_function f tfn TRANSL).
  replace (Mach.fn_code tfn) with
          (transl_body f (make_env (function_bounds f)) (framesize_of_fn f));
    [|by rewrite (unfold_transf_function f tfn TRANSL); simpl].
  unfold transl_body. eexact EXP.
  replace (MPtr.sub_int stk (Int.repr (fn_framesize tfn)))
     with (MPtr.add stk (Int.repr (-fn_framesize tfn))).
  2: by destruct stk; simpl; rewrite Int.sub_add_opp, Int.neg_repr.
  econstructor; eauto with coqlib.
  by destruct s; 
    eauto using agree_callee_save_regs_agree, agree_callee_save_impl_regs.

  Case "exec_function_external_call".
  inv TRANSL.
  exploit transl_external_arguments; eauto. intro EXTARGS.
  econstructor; split.
   eby apply step_weakstep; simpl; eapply exec_function_external_call.
  econstructor; eauto.

  Case "exec_function_external_return".
  econstructor; split.
  apply step_weakstep; simpl; eapply exec_function_external_return; eauto.
  econstructor; try done.
  intros. unfold Regmap.set. case (RegEq.eq r (loc_result (efsig))); intro.
  rewrite e. rewrite Locmap.gss; auto. rewrite Locmap.gso; auto.
  red; auto.
  apply agree_parent_set_result; auto.

  Case "exec_return".
  inv STACKS. 
  econstructor; split.
  apply step_weakstep; simpl; apply exec_return. 
  econstructor; eauto. simpl in AG2.  
  eapply agree_frame_agree; eauto.

  Case "exec_return_exit".
  inv STACKS. 
  econstructor; split.
   by apply step_weakstep; simpl; apply exec_return_exit. 
  vauto. 
Qed.

Definition order: Linear.state -> Linear.state -> Prop := fun x y => False.

Lemma my_forward_sim:
  @forward_sim thread_labels lts tlts match_states order.
Proof.
  split. done.
  intros s t l s' ST MS.
  right; left. 
  apply (transf_step_correct s l s' ST t MS). 
Qed.

Lemma build_locs_other:
  forall args vals l
    (NI: ~ In l args),
    build_locs args vals l = Vundef.
Proof.
  induction args; intros. by destruct vals.
  destruct vals. done. 
  simpl. destruct Loc.eq as [<- | N]. by elim NI; left.
  apply IHargs. by intro IN; elim NI; right. 
Qed.

Lemma build_frame_rec_other:
  forall ofs t  l vs f (NI: Loc.notin (S (Outgoing ofs t)) l),
    build_frame_rec l vs f t (4 * ofs) = f t (4 * ofs). 
Proof.
  induction l as [|[|[]]]; intros; simpl; try destruct vs; try done;
    simpl in NI; destruct NI as [N NI]; rewrite IHl; try done.
  rewrite update_other. done.
  destruct N as [D|D]. destruct t; simpl in D |- *; omega.
  destruct t0; simpl in D |- *; omega.
Qed.

Lemma build_locs_in:
  forall args vals l
    (IN: In l args),
      In (build_locs args vals l) vals \/
      build_locs args vals l = Vundef.
Proof.
  induction args; intros. done. 
  destruct vals. by right.
  simpl in IN; destruct IN as [<- | IN].
    by simpl; destruct Loc.eq; vauto.
  simpl; destruct Loc.eq as [-> | N]. vauto. 
  by destruct (IHargs vals _ IN); vauto.
Qed.

Lemma in_conv_list_nil:
  forall v tys (IN: In v (Val.conv_list nil tys)), v = Vundef.
Proof.
  induction tys. done.
  simpl; intros [<-|IN]; auto. 
Qed.

Lemma init_sim_succ:
  forall {p vals tinit},
    ma_init tge p vals = Some tinit ->
    exists sinit, linear_init ge p vals = Some sinit /\ match_states sinit tinit.
Proof.
  intros p vals tinit INIT. unfold linear_init, ma_init in *. 
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  specialize (wt_ge p).
  repeat (destruct Genv.find_funct_ptr); try done; [].
  destruct f; destruct f0; try done; try (by simpl in MF; destruct (transf_function f)).
  assert (SG' : Linear.fn_sig f = fn_sig f0).
    destruct beq_nat; [|try done].
    destruct f; simpl in *.
    monadInv MF. unfold transf_function in EQ.
    repeat (destruct zle; [done|]).
    by inv EQ. 
  rewrite !SG'.
  destruct (beq_nat (length vals) (length (sig_args (fn_sig f0)))); [|done].
  inv INIT.
  eexists. split. edone. constructor; vauto. 
  - eby eapply wt_ge.
  - intros r. rewrite build_locs_other, Regmap.gi. done.
    by apply Loc.notin_not_in, loc_arguments_rec_notin_reg.
  - intros ofs ty IN. unfold get_parent_slot, build_frame. simpl.
    unfold get_slot.
    pose proof (loc_arguments_bounded _ _ _ IN) as BNDofs.
    pose proof (loc_arguments_acceptable _ _ IN) as ACCofs.
    assert (E4o: Int.signed (Int.repr (4 * ofs)) = 4 * ofs).
      rewrite Int.signed_repr. done.
      monadInv MF. destruct f; unfold transf_function in EQ.
      destruct zle as [_|_]; [done|]. destruct zle as [|SZ]; [done|]. 
      simpl in ACCofs. unfold Int.min_signed, Int.max_signed in *. 
      split. eapply Zle_trans with 0. by compute. omega.
      simpl in *; subst; pose proof (typesize_pos ty). 
      unfold fe_retaddrsize in *; omega.
    rewrite !E4o.
    destruct slot_valid_dec as [V | NV].
      f_equal. simpl in IN. rewrite SG' in IN.
      pose proof (loc_arguments_acceptable (fn_sig f0)) as ACC.
      pose proof (loc_arguments_norepet (fn_sig f0)) as NR.
      pose proof (loc_arguments_bounded (fn_sig f0)) as BND.
      pose proof (loc_arguments_length (fn_sig f0)) as SZ.
      remember (sig_args (fn_sig f0)) as sa. clear Heqsa.
      remember empty_frame as ef; clear Heqef.
      revert vals sa ef ACC NR BND SZ.
      induction (loc_arguments (fn_sig f0)); intros. done.
      destruct sa; [done|].
      simpl in IN |- *. inv SZ. 
      assert (forall r, In r l -> loc_argument_acceptable r)
       by (by intros; apply ACC; right).
      assert (forall ofs ty, In (S (Outgoing ofs ty)) l -> 
                             ofs + typesize ty <= size_arguments (fn_sig f0))
       by (by intros; apply BND; right).
      inv NR.
      pose proof (ACC _ (or_introl _ (refl_equal _))) as ACC'.
      destruct a as [|[]]; destruct vals; destruct Loc.eq as [E|N]; try done;
        try (by rewrite IHl; try done; by destruct IN);
        try (by inv E; rewrite build_frame_rec_other, update_same);
        by (simpl in IN; (destruct IN as [E' | IN]; [by inv E'|]); rewrite IHl).
    destruct NV. simpl in *. constructor. omega.
    rewrite <- SG'. destruct ty; simpl in BNDofs |- *; omega. apply aligned_4_4x.    
  - intros [|[]]; intros r INcs; try done; [].
    rewrite build_locs_other. done.
    intro IN. apply arguments_caller_save in IN.
    pose proof (float_callee_save_not_destroyed _ (or_intror _ IN)).
    pose proof (int_callee_save_not_destroyed _ (or_intror _ IN)).
    by destruct INcs.
Qed.

Lemma init_sim_fail:
  forall {p vals},
    ma_init tge p vals = None ->
    linear_init ge p vals = None.
Proof.
  intros p vals INIT. unfold linear_init, ma_init in *. 
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  destruct (Genv.find_funct_ptr tge p) as [[[]|]|]; try done;
    destruct (Genv.find_funct_ptr ge  p) as [[[]|]|]; try done; simpl in *;
      monadInv MF. 
  unfold transf_function in EQ. 
  repeat (destruct zle; [done|]). inv EQ.
  by destruct beq_nat.
Qed.

Definition bsim_rel := @bsr _ lts tlts match_states.
Definition bsim_order := @bsc _ tlts.

End PRESERVATION.

Definition stacking_match_prg (p  : linear_sem.(SEM_PRG))
                              (p' : ma_sem.(SEM_PRG)) : Prop := 
  Lineartyping.wt_program p /\
  transf_program p = OK p'.

Definition full_genv_rel (ge : Linear.genv) (tge : Mach.genv) :=
  genv_rel ge tge /\ 
  forall x f, Genv.find_funct_ptr ge x = Some f -> wt_fundef f.

(** The whole-system backward simulation for the [Stacking]
    phase. *)
Theorem stacking_sim Mm : Sim.sim Mm Mm linear_sem ma_sem stacking_match_prg.
Proof.
  eapply (MCsim.sim (false_pure_load_cond Mm) linear_sem ma_sem full_genv_rel 
    bsim_rel (fun _ => bsim_order)); intros; simpl in *.
  - destruct GENVR as [[GR FR] _]. rewrite GR.
    by rewrite (transform_partial_program_main _ _ (proj2 MP)).
  - destruct (Genv.exists_matching_genv_and_mem_rev
                  (transform_partial_program_match _ _ (proj2 MP)) INIT) 
      as [sge [INIT' GEM]].
    exists sge. split. done.
    split. done.
    intros p f. 
    destruct (Genv.find_funct_ptr sge p) as [fd|] _eqn : Efd; [|done].
    intro E; inv E.
    set (P f' := exists id, In (id, f') src_prog.(prog_funct)).
    assert (II: forall id' f', In (id', f') src_prog.(prog_funct) -> P f').
      intros id' f' IN. eby eexists.
    pose proof (Genv.find_funct_prop P (Vptr p) INIT' II Efd) as [id IN].
    by specialize (proj1 MP _ _ IN).
  - destruct (init_sim_succ _ _ (proj1 GENVR) (proj2 GENVR) INIT) 
      as [si [INIT' MS]].
    exists si. split. done.
    by apply fsr_in_bsr. 
  - eby destruct GENVR; eapply init_sim_fail.
  - eapply forward_to_backward_sim. 
          apply linear_sem.(SEM_receptive).
        apply ma_sem.(SEM_determinate).
      apply linear_sem.(SEM_progress_dec).
    by destruct GENR; apply my_forward_sim.
Qed.
