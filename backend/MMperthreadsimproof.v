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

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Pointers.
Require Import Values.
Require Import Mem.
Require Import Memeq.
Require Import Simulations.
Require Import Events.
Require Import Globalenvs.
Require Import Libtactics.
Require Import MMperthreadsimdef.

Require Import Stacklayout.
Require Machregs.
Require Op.
Require Import Mach.
Require Import Machabstr.
Require Import Machconcr.
Require Import Machtyping.
Require Import MMproofaux.
Require Asm.

(** Here we define a simulation relation between Machanstr and
    Machconcr thread states and show that it is indeed a simulation in
    the sense of the [MMperthreadsimdef] file. *)

Section SIM.
  
Variable (ge : Mach.genv).
Variable (wt_ge : wt_genv ge).

Let lts := (mklts thread_labels (ma_step ge)).
Let tlts := (mklts thread_labels (mc_step ge)).

Notation chunk_of_type := Asm.chunk_of_ty.
Notation modulus := Int.modulus.
Notation half_modulus := Int.half_modulus.

(** Lemmata about [lessdef] for register file *)

Definition regset_lessdef (rs rs': regset) : Prop :=
  forall r, Val.lessdef (rs r) (rs' r).

Lemma regset_get_list:
  forall rs rs' l,
  regset_lessdef rs rs' -> Val.lessdef_list (rs##l) (rs'##l).
Proof.
  induction l; simpl; intros; constructor; auto.
Qed.

Lemma regset_set:
  forall rs rs' v v' r,
  regset_lessdef rs rs' -> Val.lessdef v v' ->
  regset_lessdef (rs#r <- v) (rs'#r <- v').
Proof.
  by red; intros; destruct (Machregs.mreg_eq r0 r); 
    subst; rewrite ?Regmap.gss, ?Regmap.gso.
Qed.

Lemma regset_lessdef_undef_temps:
  forall rs rs' (RLD: regset_lessdef rs rs'),
    regset_lessdef (undef_temps rs) (undef_temps rs').
Proof.
  unfold undef_temps.
  induction (Conventions.int_temporaries ++ Conventions.float_temporaries).
  done. intros; simpl; eauto using regset_set.
Qed.
  
Lemma regset_lessdef_undef_op:
  forall rs rs' op (RLD: regset_lessdef rs rs'),
    regset_lessdef (undef_op op rs) (undef_op op rs').
Proof.
  intros. destruct op; simpl; auto using regset_lessdef_undef_temps.
Qed.

(** * Matching Machabstr frames with Machconcr memory *)

Section FRAME_MATCH.

Variable fsize : Z.
Hypothesis fsize_bnd : 0 <= fsize < modulus.

Inductive frame_match (fr: frame)
                      (sp: pointer) (ms: mem) : Prop :=
  frame_match_intro:
   forall
     (SMALL: Int.unsigned (Ptr.offset sp) + fsize <= modulus)
     (* RALLOC: range_allocated (sp, Int.repr fsize) MObjStack ms *)
     (LDREL: forall ty ofs (SV: slot_valid fsize ty ofs),
       exists v,
         load_ptr (chunk_of_type ty) 
                  ms 
                  (Ptr.add sp (Int.repr ofs)) = Some v /\
         Val.lessdef (fr ty ofs) v),
    frame_match fr sp ms.

Definition load_stack (m: mem) (sp: pointer) (ty: typ) (ofs: int) :=
  load_ptr (chunk_of_type ty) m (Ptr.add sp ofs).

Definition store_stack (m: mem) (sp: pointer) (ty: typ) (ofs: int) (v: val) :=
  store_ptr (chunk_of_type ty) m (Ptr.add sp ofs) v.

(*
Variable f: function.
Hypothesis wt_f: wt_function f.
*)

Lemma Zdivide_signed:
 forall x ofs,
   (x | Int.signed ofs) ->
   (x | modulus) ->
   (x | Int.unsigned ofs).
Proof.
  destruct ofs; unfold Int.signed; simpl; destruct zlt; intros; try done.
  replace intval with (intval - modulus + modulus); try omega.
  by apply Zdivide_plus_r.
Qed.

Lemma frame_match_load_stack:
  forall fr sp ms ty ofs
    (FM: frame_match fr sp ms)
    (SV: slot_valid fsize ty (Int.signed ofs)),
  exists v', 
    load_stack ms sp ty ofs = Some v' /\
    Val.lessdef (fr ty (Int.signed ofs)) v'.
Proof.
  intros; destruct FM.
  unfold load_stack. 

  exploit (LDREL ty (Int.signed ofs)). done.
  intros [v' (L & LD)].
  rewrite Int.repr_signed in L.
  vauto.
Qed.

Lemma frame_match_get_slot:
  forall {fr sp ms ty ofs v},
  frame_match fr sp ms ->
  load_stack ms sp ty ofs = Some v ->
  get_slot fsize fr ty (Int.signed ofs) = None 
  \/ 
  exists v', 
    get_slot fsize fr ty (Int.signed ofs) = Some v' /\
    Val.lessdef v' v.
Proof.
  inversion 1; unfold get_slot.
  destruct slot_valid_dec as [[]|]; [|by vauto].
  exploit frame_match_load_stack; try edone. 
  intros [v' (L & LD)] L'; clarify'; vauto.
Qed.

Lemma frame_match_get_slot_none:
  forall {fr sp ms ty ofs},
  frame_match fr sp ms ->
  load_stack ms sp ty ofs = None ->
  get_slot fsize fr ty (Int.signed ofs) = None.
Proof.
  inversion 1; unfold get_slot.
  destruct slot_valid_dec as [[]|]; [|by vauto].
  exploit frame_match_load_stack; try edone. 
  intros [v' (L & LD)] L'; clarify'; vauto.
Qed.

Lemma frame_match_ext_mem_arg_list:
  forall {fr sp tm rs rs'}
  (FM : frame_match fr sp tm)
  (RLD: regset_lessdef rs rs')
  {sg margs}
  (MFS: memarglist_from_sig rs' sp sg = margs),
  (* Either we can simulate... *)
  (exists vargs, exists vargs',
    mem_arglist tm margs = Some vargs'  /\
    extcall_arguments fsize rs fr sg vargs /\
    Val.lessdef_list vargs vargs') \/
  extcall_args fsize rs fr (Conventions.loc_arguments sg) = None.
Proof.
  destruct sg as [].
  unfold memarglist_from_sig, Conventions.loc_parameters, extcall_arguments.
  remember (Conventions.loc_arguments (mksignature sig_args sig_res)) as args; 
    clear Heqargs.
  induction args as [|h t IH]; intros; 
    unfold memarglist_from_sig in MFS; simpl in MFS; subst.
  (* Base case *)
  left. by exists nil; exists nil.
  (* Step case *) 
  destruct (IH _ (refl_equal _)) as [[vargs [vargs' (MAL & EA & LD)]] | FAIL]; 
    unfold mem_arglist, extcall_args in *.
    (* Success from the IH *)
    destruct h as [|[]]; try (by right).
      (* Register *)
      left. eexists. eexists. simpl. rewrite MAL.
      split. edone.
      split. rewrite EA. edone.
      constructor. apply (RLD m).
      edone.
    (* Memory *)
    destruct (load_stack tm sp t0 (Int.repr (4 * z))) as [v|] _eqn : L.
      (* Load succeeded *)
      destruct (frame_match_get_slot FM L) as [GS|[v' (GS & LD')]].
        (* getslot failed *)
        right. simpl in *. by rewrite GS.
      (* getslot success *)
      left. eexists. eexists.
      split. 
        unfold load_stack in L; simpl in *. eby rewrite L, MAL; simpl.
      split. simpl in *. eby rewrite GS, EA.
      vauto.
    (* Load failed *)
    pose proof (frame_match_get_slot_none FM L) as GS.
    right. simpl in *. by rewrite GS.
  (* Failure from the IH *)
  by right; unfold extcall_args in *; simpl; rewrite FAIL; simpl; destruct extcall_arg.
Qed.

Lemma frame_match_get_slot_bw:
  forall {fr sp ms ty ofs v},
  frame_match fr sp ms ->
  get_slot fsize fr ty (Int.signed ofs) = Some v ->
  exists v', 
    load_stack ms sp ty ofs = Some v' /\
    Val.lessdef v v'.
Proof.
  inversion 1; unfold get_slot.
  destruct slot_valid_dec as [[]|]; [|by vauto].
  exploit frame_match_load_stack; try edone. 
  intros [v' (L & LD)] L'; clarify'; vauto.
Qed.

Lemma Zmod_plus_signed:
  forall x ofs,
    (x + Int.unsigned ofs) mod modulus = (x + Int.signed ofs) mod modulus.
Proof.
  intros; unfold Int.signed.
  destruct zlt; try done.
  by rewrite (Zplus_mod _ (Zminus _ _)), Zminus_mod, Z_mod_same_full, Zminus_0_r, Zmod_mod, <- Zplus_mod.
Qed.

Lemma typesize_sizechunk:
  forall ty,
    typesize ty = size_chunk (chunk_of_type ty).
Proof. by destruct ty. Qed.

Lemma frame_match_store_stack:
  forall fr sp ms ty ofs v v',
  frame_match fr sp ms ->
  slot_valid fsize ty (Int.signed ofs) ->
  Val.has_type v ty ->
  Val.lessdef v' v ->
  exists ms',
    store_stack ms sp ty ofs v = Some ms' /\
    frame_match (update ty (Int.signed ofs) v' fr) sp ms'.
Proof.
  intros. inv H. (* inv wt_f. *)
  exploit frame_match_load_stack; try edone; []; intros [v'' (L & _)].
  unfold load_stack, store_stack in *.
  pose proof (load_chunk_allocated_spec (chunk_of_type ty) ms (sp + ofs)) as X; rewrite L in X.
  pose proof (store_chunk_allocated_spec (chunk_of_type ty) ms (sp + ofs) v) as X2.
  destruct (store_ptr (chunk_of_type ty) ms (sp + ofs) v) as [ms'|] _eqn: STO; try done; clear v'' L X2.
  eexists; split; [edone|].
  (* frame match *)
  constructor. done.
  intros; exploit LDREL; try edone; []; intros [v'' (L & LD)].
  unfold update.
  destruct (zeq (Int.signed ofs) ofs0); clarify.
    rewrite Int.repr_signed in L |- *. 
    destruct (typ_eq ty ty0); clarify.
      exists v.
      (* same *)
      erewrite load_store_similar; eauto.
      by destruct ty0; destruct v.
    (* mismatch *)
    erewrite load_store_mismatch; try edone. vauto.
    2: by destruct ty; destruct ty0.
    destruct sp.
      unfold range_of_chunk; simpl.
      eapply ranges_overlapI; try done;
      [destruct ty|destruct ty0]; simpl;
      change (4 mod modulus) with 4; 
      change (8 mod modulus) with 8; omega.
  (* disjoint \/ overlap *)
  assert (ofs0 < fsize) by (inv SV; destruct ty0; simpl in *; omega).
  assert (Int.signed ofs < fsize) by (inv H0; destruct ty; simpl in *; omega).
  assert (- Int.min_signed <= Int.max_unsigned) by done.
  pose proof (typesize_pos ty0).
  pose proof (Int.unsigned_range ofs).
  unfold Int.signed in *; simpl in *. inv H0. inv SV.
  destruct zlt; 
    [|destruct sp as [? [sp ?]];destruct ofs as [ofs ?]; simpl in *; omegaContradiction].
  destruct zle; [erewrite <- load_store_other; try edone; vauto|]. unfold range_of_chunk.
    destruct sp as [bsp osp]; simpl in *; pose proof (Int.unsigned_range osp).
    right. right. 
    rewrite size_chunk_repr, !Int.add_unsigned, <- typesize_sizechunk; 
      repeat rewrite !Int.unsigned_repr; unfold Int.max_unsigned; omega.
  destruct zle; [erewrite <- load_store_other; try edone; vauto|]. unfold range_of_chunk.
    destruct sp as [bsp osp]; simpl in *; pose proof (Int.unsigned_range osp).
    right. left. 
    rewrite size_chunk_repr, !Int.add_unsigned, <- typesize_sizechunk; 
      repeat rewrite !Int.unsigned_repr; unfold Int.max_unsigned; omega.
  erewrite load_store_mismatch; try edone; vauto.
  destruct sp as [bsp osp]; simpl in *.
  pose proof (Int.unsigned_range osp).
  eapply ranges_overlapI; try done;
    rewrite size_chunk_repr, !Int.add_unsigned, <- typesize_sizechunk; 
      repeat rewrite !Int.unsigned_repr; unfold Int.max_unsigned; try omega.
  destruct sp as [bsp osp]; simpl in *; pose proof (Int.unsigned_range osp).
  destruct ty0; destruct ty; unfold range_of_chunk; rewrite Int.add_unsigned;
    intro M; first [injection M | inv M]; repeat (rewrite !Zmod_small; try omega).
Qed.

Lemma frame_match_set_slot:
  forall {fr sp ms ty ofs v v' ms'},
  frame_match fr sp ms ->
  store_stack ms sp ty ofs v = Some ms' ->
  Val.has_type v ty ->
  Val.lessdef v' v ->
  set_slot fsize fr ty (Int.signed ofs) v' = None 
  \/
  exists fr',
    set_slot fsize fr ty (Int.signed ofs) v' = Some fr' /\
    frame_match fr' sp ms'.
Proof.
  inversion 1; unfold set_slot; intros STO. 
  destruct slot_valid_dec as [[]|]; vauto.
  right; eexists; split; try done.
  exploit frame_match_store_stack; try edone. 
  by rewrite STO; intros (? & ? & ?); clarify.
Qed.

Lemma frame_match_set_slot_none:
  forall {fr sp ms ty ofs v v'},
  frame_match fr sp ms ->
  store_stack ms sp ty ofs v = None ->
  Val.has_type v ty ->
  Val.lessdef v' v ->
  set_slot fsize fr ty (Int.signed ofs) v' = None.
Proof.
  inversion 1; unfold set_slot; intros STO. 
  destruct slot_valid_dec as [[]|]; vauto.
  intros; 
  exploit frame_match_store_stack; try edone. 
  by rewrite STO; intros (? & ? & ?); clarify.
Qed.

Lemma lb_hb_range_inside:
  forall ofs ty sp
    (SMALL : Int.unsigned (Ptr.offset sp) + fsize <= modulus)
    (SV :    slot_valid fsize ty ofs),
  range_inside (range_of_chunk (sp + Int.repr ofs) (chunk_of_type ty))
       (sp, Int.repr fsize).
Proof.
  intros. inv SV.
  destruct sp as [bsp osp]; simpl in SMALL.
  pose proof (typesize_pos ty).
  pose proof (Int.unsigned_range osp).
  split. done. right.
  rewrite !Int.add_unsigned, <- typesize_sizechunk.
  by repeat (rewrite Int.unsigned_repr; unfold Int.max_unsigned; try omega).
Qed.

(** Agreement is preserved by stores within blocks other than the
  one pointed to by [sp]. *)

Lemma frame_match_store_other:
  forall fr sp p ms chunk v ms'
    (FM: frame_match fr sp ms)
    (STO: store_ptr chunk ms p v = Some ms')
    (DISJ: ranges_disjoint (range_of_chunk p chunk) (sp, Int.repr fsize)),
  frame_match fr sp ms'.
Proof.
  intros; destruct FM; clarify.
  constructor. done.
  intros. 
  destruct (LDREL _ _ SV) as [v' (L & LD)].
  exists v'; split; [|done].
  rewrite <- (load_store_other STO). done.
  eapply disjoint_inside_disjoint_r. edone.
  by apply lb_hb_range_inside. 
Qed.

End FRAME_MATCH.


(** Lemmata about [eval_operation] and [eval_addressing]. *)

Lemma eval_addressing_none_some: forall F ge sp op vl v,
 @Op.eval_addressing F ge None op vl = Some v ->
 @Op.eval_addressing F ge (Some sp) op vl = Some v.
Proof.
  by intros; destruct op; try done; destruct vl.
Qed.

Lemma eval_operation_none_some: forall F ge sp op vl v,
 @Op.eval_operation F ge None op vl = Some v ->
 @Op.eval_operation F ge (Some sp) op vl = Some v.
Proof.
  by intros; destruct op; try done; destruct vl; 
    apply eval_addressing_none_some.
Qed.

Lemma eval_addressing_disj: forall {F} {ge: Genv.t F} {sp spo op rs args v1 rs'}
  (EVAL: @Op.eval_addressing F ge (Some sp) op (rs##args) = Some v1)
  (SPM: spo = None \/ spo = Some sp)
  (LESSDEF: regset_lessdef rs' rs),
  (exists v, Op.eval_addressing ge spo op (rs'##args) = Some v /\ Val.lessdef v v1)
  \/ Op.eval_addressing ge spo op (rs'##args) = None.
Proof.
  intros.
  eapply Op.eval_addressing_lessdef3 in EVAL; [|eby eapply regset_get_list].
  destruct EVAL as [|(? & ? & ?)]; destruct SPM; subst; vauto;
    destruct op; try done; destruct (rs'##args); vauto.
Qed.

Lemma eval_operation_disj: forall {F} {ge: Genv.t F} {sp spo op rs args v1 rs'}
  (EVAL: @Op.eval_operation F ge (Some sp) op (rs##args) = Some v1)
  (SPM: spo = None \/ spo = Some sp)
  (LESSDEF: regset_lessdef rs' rs),
  (exists v, Op.eval_operation ge spo op (rs'##args) = Some v /\ Val.lessdef v v1)
  \/ Op.eval_operation ge spo op (rs'##args) = None.
Proof.
  intros.
  eapply Op.eval_operation_lessdef3 in EVAL; [|eby eapply regset_get_list].
  destruct EVAL as [|(? & ? & ?)]; subst; vauto;
    destruct op; try destruct a; try done; destruct (rs'##args); vauto;
      destruct SPM as [-> | ->]; eauto.  
Qed.

Lemma atomic_statement_disj:
  forall op args args' p c v instr
  (ASME : Op.atomic_statement_mem_event op args v (MErmw p c v instr))
  (* HTv : Val.has_type v Tint *)
  (LDa : Val.lessdef_list args' args),
    Op.atomic_statement_mem_event op args' v (MErmw p c v instr) /\ args = args' 
    \/ forall v v' p' c' instr', 
       ~ Op.atomic_statement_mem_event op args' v (MErmw p' c' v' instr').
Proof.
  intros.
  inv ASME.
  
  (* CAS *)
  inv LDa. inv H2; [|by right; intros; intro A; inv A].
  inv H3. inv H2; [|by right; intros; intro A; inv A].
  inv H4. inv H2; [|by right; intros; intro A; inv A].
  inv H3.
  left. split. by constructor. done.
  (* lkinc *)
  inv LDa. inv H2; [|by right; intros; intro A; inv A].
  inv H3. 
  left. split. by constructor. done.
Qed.
    

Notation rasize := (Int.repr fe_retaddrsize).

Lemma unsigned_rasize:
  Int.unsigned rasize = fe_retaddrsize.
Proof. by compute.  Qed.

Lemma unsigned_rasize4:
  Int.unsigned rasize = 4.
Proof. by compute.  Qed.

(** [load_stkr_valid stkr m] is satisfied if all aligned loads from
   memory [m] in the stack range [stkr] succeed. *)
Definition load_stkr_valid stkr m :=
  forall p c
    (PCA: pointer_chunk_aligned p c)
    (CIN: range_inside (range_of_chunk p c) stkr),
    load_ptr c m p <> None.


(** Relation between Machconcr stack and Machabstr stack. The relation
    is parametrized by the Machconcr stack range [stkr], stack pointer [sp],
    Machconcr memory [tm] and Machabstr stack partition [spart]. *)
Inductive match_stacks (stkr : arange) (sp: pointer) (tm: mem)
                       (spart : list arange) : 
      list Machconcr.stackframe -> Machabstr.stackframes -> Prop :=
  | match_stacks_nil: forall fr sz
      (SZLB: 0 <= sz)
      (SZHB: sz + fe_retaddrsize < half_modulus)
      (RI:   range_inside (sp, Int.add rasize (Int.repr sz)) stkr)
      (RA:   load_ptr Mint32 tm sp = Some (Vptr nullptr))
      (FM:   frame_match sz fr (Ptr.add sp rasize) tm)
      (Espart: spart = nil),
      match_stacks stkr sp tm spart nil (Stackbase fr sz)
  | match_stacks_cons: forall fb spo sp' c fr s f ra ts spart' roffs
      (* The function in the frame is in the global environment... *)
      (GETF: Genv.find_funct_ptr ge fb = Some (Internal f))
      (* and it is well-typed *)
      (WTF:  wt_function f)
      (* the values in the frame match *)
      (FM:   frame_match f.(fn_framesize) fr (Ptr.add sp rasize) tm)
      (* the slot for the return address indeed contains the return 
         address *)
      (LDra: load_ptr Mint32 tm sp = Some (Vptr ra))
      (RA:   Asmgenretaddr.return_address_offset f c roffs)
      (Era:  ra = Ptr (Int.unsigned (Ptr.offset fb)) roffs)
      (* the Machabstr partition contains Machabstr's stack
         (if it is non-empty) *)
      (Espart: spart = 
        if Int.eq_dec f.(fn_stacksize) Int.zero then spart'
        else (Ptr.add sp  (Int.repr (fe_retaddrsize + f.(fn_framesize))), 
                           f.(fn_stacksize))::spart')
      (SPM: f.(fn_stacksize) = Int.zero /\ spo = None
         \/ f.(fn_stacksize) <> Int.zero /\ spo = Some (Ptr.add sp rasize))
      (* the frame region is inside the stack space *)
      (RI :  range_inside (sp, parent_offset f) stkr)
      (* The rest of the stack valid in the properly adjusted 
         stack pointer *)
      (EQsp': sp' = Ptr.add sp (parent_offset f))
      (MS: match_stacks stkr sp' tm spart' ts s),
      match_stacks stkr sp tm spart
        (Machconcr.Stackframe fb (Ptr.add sp rasize) ra c :: ts)
        (Machabstr.Stackframe f spo c fr s).

(** ** Invariant between states. *)

(** The [match_state] predicate relates a Machabstr state with
  a Machconcr state.  In addition to [match_stacks] between the
  stacks, we ask that
- The Machabstr frame is properly stored in the activation record,
  as characterized by [frame_match].
- Registers are related.
- The partitionings are consistent with the state and with respect 
  to each other (each partition of Machabstr must be inside the
  Machconcr stack).
- Stack pointer is 16-aligned and it is inside the stack. *)

Inductive match_state :
      Machconcr.state ->    (**r target state *)
      list arange ->        (**r allocated ranges in target *)
      mem ->                (**r target (local) memory *)
      Machabstr.state ->    (**r source state *)
      list arange ->        (**r allocated ranges in source
                                 (these can be shared) *)
      Prop :=
  | match_states_normal:
      forall fb spo sp' c fr ss f ts spart spart' rs rs' stkr tm sp
      (* The function in the frame is in the global environment... *)
      (GETF: Genv.find_funct_ptr ge fb = Some (Internal f))
      (* and it is well-typed *)
      (WTF:  wt_function f)
      (WTS:  wt_state (Machabstr.State ss f spo c rs' fr))
      (* the values in the frame match *)
      (FM:   frame_match f.(fn_framesize) fr sp tm)
      (* Machabstr registers are less-defined than the Machconcr ones. *)
      (REGS: regset_lessdef rs' rs)
      (* the Machabstr partition contains Machabstr's stack
         (if it is non-empty) *)
      (Espart: spart = 
        if Int.eq_dec f.(fn_stacksize) Int.zero then spart'
        else (Ptr.add sp  (Int.repr f.(fn_framesize)), f.(fn_stacksize))::spart')
      (SPM: f.(fn_stacksize) = Int.zero /\ spo = None
         \/ f.(fn_stacksize) <> Int.zero /\ spo = Some sp)
      (* the frame region is inside the stack space *)
      (RI :  range_inside (sp, total_framesize f)
                          stkr)
      (* stkr is valid region *)
      (VAR:  valid_alloc_range stkr)
      (SRWF: valid_erange stkr)
      (* all loads from stkr are defined *)
      (LSV:  load_stkr_valid stkr tm)
      (* stack pointer is properly aligned *)
      (ALG:  (16 | Int.unsigned (Ptr.offset sp)))
      (* The rest of the stack valid in the properly adjusted 
         stack pointer *)
      (EQsp': sp' = Ptr.add sp (total_framesize f))
      (MS: match_stacks stkr sp' tm spart' ts ss),
    match_state 
      (Machconcr.State ts fb sp c stkr rs) (stkr :: nil) tm
      (Machabstr.State ss f spo c rs' fr) spart
  | match_states_call:
      forall ss f rs rs' ts fb sp stkr spart tm
        (STACKS: match_stacks stkr sp tm spart ts ss)
        (VAR:  valid_alloc_range stkr)
        (SRWF: valid_erange stkr)
        (LSV:  load_stkr_valid stkr tm)
        (ALG:  (16 | Int.unsigned (Ptr.offset sp) + fe_retaddrsize))
        (REGS: regset_lessdef rs' rs)
        (WTF: wt_fundef f)
        (WTS: wt_state (Machabstr.Callstate ss f rs'))
        (FIND: Genv.find_funct_ptr ge fb = Some f),
      match_state
        (Machconcr.Callstate ts fb sp stkr rs) (stkr :: nil) tm
        (Machabstr.Callstate ss f rs') spart
  | match_states_return:
      forall ts ss rs rs' sp stkr spart tm
        (STACKS: match_stacks stkr sp tm spart ts ss)
        (VAR:  valid_alloc_range stkr)
        (SRWF: valid_erange stkr)
        (LSV:  load_stkr_valid stkr tm)
        (ALG:  (16 | Int.unsigned (Ptr.offset sp) + fe_retaddrsize))
        (WTS: wt_state (Machabstr.Returnstate ss rs'))
        (REGS: regset_lessdef rs' rs),
      match_state
        (Machconcr.Returnstate ts sp stkr rs) (stkr :: nil) tm 
        (Machabstr.Returnstate ss rs') spart
  | match_states_blocked:
      forall ts ss rs rs' sig sp stkr spart tm 
        (STACKS: match_stacks stkr sp tm spart ts ss)
        (VAR:  valid_alloc_range stkr)
        (SRWF: valid_erange stkr)
        (LSV:  load_stkr_valid stkr tm)
        (ALG:  (16 | Int.unsigned (Ptr.offset sp) + fe_retaddrsize))
        (WTS: wt_state (Machabstr.Blockedstate ss rs' sig))
        (REGS: regset_lessdef rs' rs),
      match_state 
        (Machconcr.Blockedstate ts sp stkr rs sig) (stkr::nil) tm
        (Machabstr.Blockedstate ss rs' sig) spart
  | match_states_init:
      forall fb f tm vs ms vs'
        (FIND: Genv.find_funct_ptr ge fb = Some f)
        (Els:  length (funsig f).(sig_args) = length vs)
        (LD:   Val.lessdef_list vs vs')
        (WT:   Val.has_type_list vs' (funsig f).(sig_args))
        (Ems: ms = Machabstr.Callstate 
          (Stackbase (build_frame (funsig f) vs) (4 * Conventions.size_arguments (funsig f))) f 
          (Regmap.init Vundef))
        (WTS: wt_state ms),
      match_state
        (Machconcr.Initstate fb vs') nil tm
        (Machabstr.Callstate 
          (Stackbase (build_frame (funsig f) vs) (4 * Conventions.size_arguments (funsig f))) f 
          (Regmap.init Vundef)) nil
  | match_states_initargsstate:
      forall fb sp stkr tm f ms locs1 locs2 vs1 vs2 vs2' sz
        (FIND: Genv.find_funct_ptr ge fb = Some f)
        (El2:  length locs2 = length vs2')
        (El1:  length locs1 = length vs1)
        (SG:   Conventions.loc_arguments (funsig f) = locs1 ++ locs2)
        (WT:   Val.has_type_list vs2' (map Locations.Loc.type locs2))
        (Esz:  sz = 4 * Conventions.size_arguments (funsig f))
        (LD:   Val.lessdef_list vs2 vs2')
        (RI:   range_inside (sp, Int.repr (fe_retaddrsize + sz)) stkr)
        (VAR:  valid_alloc_range stkr)
        (SRWF: valid_erange stkr)
        (FM:   frame_match sz (build_frame_rec locs1 vs1 empty_frame) (Ptr.add sp rasize) tm)
        (Ems:  ms = Machabstr.Callstate 
          (Stackbase (build_frame (funsig f) (vs1 ++ vs2)) sz) f 
          (Regmap.init Vundef))
        (WTS:  wt_state ms)
        (LSV:  load_stkr_valid stkr tm)
        (ALG:  (16 | Int.unsigned (Ptr.offset sp) + fe_retaddrsize)),
      match_state
        (Machconcr.Initargsstate fb vs2' (map Conventions.parameter_of_argument locs2)  
                                 sp stkr (Regmap.init Vundef)) (stkr::nil) tm
        (Machabstr.Callstate 
          (Stackbase (build_frame (funsig f) (vs1 ++ vs2)) sz) f 
          (Regmap.init Vundef)) nil
  | match_states_freestack:
      forall rs stkr tm fr sz,
      match_state
        (Machconcr.Freestackstate stkr) (stkr::nil) tm
        (Machabstr.Returnstate (Stackbase fr sz) rs) nil
  | match_states_exit:
      forall rs tm fr sz,
      match_state
        (Machconcr.Exitstate) nil tm
        (Machabstr.Returnstate (Stackbase fr sz) rs) nil
.

Tactic Notation "match_state_cases" tactic(first) tactic(c) :=
    first; [
      c "match_states_normal" |
      c "match_states_call" |
      c "match_states_return" |
      c "match_states_blocked" |
      c "match_states_init" |
      c "match_states_initargsstate" |
      c "match_states_freestack" |
      c "match_states_exit"].

(*
Lemma unsigned_zero_eq:
  Int.unsigned Int.zero = 0.
Proof. by compute. Qed. 
*)

Definition measure s :=
  match s with 
    | Machconcr.Initstate p args => (S (S (length args)))
    | Machconcr.Initargsstate p args locs sp stkr rs => (S (length args))
    | Machconcr.Returnstate _ _ _ _ => 2%nat
    | Machconcr.Freestackstate _ => 1 %nat
    | _ => 0%nat
  end.

(** * Auxiliary lemmas for simulation proof. *)
Lemma div_mul_bounds:
  forall a b (POS: b > 0),
    a - b < a / b * b <= a.
Proof.
  intros.
  pose proof (Zmod_eq a b POS).
  pose proof (Z_mod_lt a b POS).
  omega.
Qed.

(** Initial stack frame is inside the allocated stack space. *)
Lemma aligned_stack_inside:
  forall sa stkp
    (SApos : sa >= 0)
    (VAR: valid_alloc_range (stkp, Int.repr thread_stack_size))
    (SZ: 4 * sa + fe_retaddrsize + 15 <= thread_stack_size),
   range_inside
     (Ptr.sub_int (Asm.align_stack
                       (stkp +
                         Int.repr (thread_stack_size - 4 * sa))) 
                    (Int.repr 4),
        Int.repr (4 * sa + fe_retaddrsize))
     (stkp, Int.repr thread_stack_size).
Proof.
  intros sa [bp [n N]] POS (L & S & H & ALG) SZ.
  split. done.
  right.
  unfold Int.sub, Int.add, Int.repr, Int.unsigned, Int.intval,
    fe_retaddrsize in *.
  assert (E1: 4 mod modulus = 4) by (by compute). rewrite E1 in *.
  assert (E2: thread_stack_size mod modulus = thread_stack_size) by (by compute). rewrite E2 in *.
  assert (E3: (thread_stack_size - 4 * sa) mod modulus = thread_stack_size - 4 * sa).
    rewrite Zmod_small. done. omega.
  rewrite E3 in *.
  assert (POS2: 0 <= n + (thread_stack_size - 4 * sa)). omega.
  assert (LE: n + (thread_stack_size - 4 * sa) <= modulus) by omega.
  pose proof (div_mul_bounds (n + (thread_stack_size - 4 * sa)) 16 (refl_equal _)).
  replace ((4 * sa + 4) mod modulus) with (4 * sa + 4) by (rewrite Zmod_small; omega).  
  destruct (Z_le_lt_eq_dec _ _ LE) as [LT | E4].
    replace ((n + (thread_stack_size - 4 * sa)) mod modulus) 
      with (n + (thread_stack_size - 4 * sa)) by (rewrite Zmod_small; omega).
    replace (((n + (thread_stack_size - 4 * sa)) / 16 * 16) mod modulus)
      with ((n + (thread_stack_size - 4 * sa)) / 16 * 16) by (rewrite Zmod_small; omega).
    replace (((n + (thread_stack_size - 4 * sa)) / 16 * 16 - 4) mod modulus) with
             ((n + (thread_stack_size - 4 * sa)) / 16 * 16 - 4)
      by (rewrite Zmod_small; omega).   
    omega.
  rewrite !E4.
  replace ((modulus mod modulus / 16 * 16) mod modulus) with 0 by (by compute).
  replace ((0 - 4) mod modulus) with (modulus - 4) by (by compute).
  omega.
Qed.  

(** Initial stack pointer is aligned. *)
Lemma align_stack_aligned: 
  forall p,
    (16 | Int.unsigned (Ptr.offset (Asm.align_stack p))).
Proof.
  intros [b ofs]. 
  simpl.
  apply Zmod_divide. done.
  rewrite <- Zmod_div_mod, Z_mod_mult; try done.
  by apply Zmod_divide.
Qed.

Lemma align_stack_aligned2:
  forall p, 
    (16
      | Int.unsigned (Ptr.offset (Ptr.sub_int
             (Asm.align_stack p) rasize)) +  fe_retaddrsize).
Proof.
  intros [b ofs]. simpl.
  apply Zmod_divide. done.
  rewrite Zplus_mod. rewrite <- Zmod_div_mod; try done.
  rewrite Zminus_mod. rewrite <- Zmod_div_mod, Z_mod_mult; try done;
    by apply Zmod_divide.
  by apply Zmod_divide.
Qed.

(** Return address is properly aligned. *)
Lemma ra_aligned:
  forall sp
    (ALG: (16 | Int.unsigned (Ptr.offset sp))),
    pointer_chunk_aligned (Ptr.sub_int sp rasize) Mint32.   
Proof.
  intros [bsp osp] ALG.
  simpl in *.
  apply Zmod_divide. by compute.
  replace (fe_retaddrsize mod modulus) with 4 by (by compute).
  rewrite <-Zmod_div_mod; try done; [|by apply Zmod_divide; compute].
  rewrite Zminus_mod.
  replace (4 mod 4) with 0 by (by compute).
  rewrite Zminus_0_r, Zmod_mod.
  apply Zdivide_mod. 
  eapply Zdivide_trans, ALG.
  by apply Zmod_divide; compute.
Qed.

(** Various sizes of stack frame are small enough. This is needed 
    to reason about module-arithmetic on those sizes. *)
Lemma stacksize_small:
  forall f (WT : wt_function f),
    0 <= f.(fn_paddedstacksize) < half_modulus.
Proof.
  intros. inv WT. 
  pose proof (Int.unsigned_range (fn_stacksize f)).
  omega.
Qed.

Lemma framesize_small:
  forall f (WT : wt_function f),
    0 <= f.(fn_framesize) < half_modulus.
Proof.
  intros. pose proof (stacksize_small _ WT).
  inv WT. omega.
Qed.

Lemma framesize_small2:
  forall f (WT : wt_function f),
    0 <= f.(fn_framesize) < modulus.
Proof.
  intros. pose proof (framesize_small _ WT) as S.
  split. omega. eapply Zlt_trans. eexact (proj2 S).
  by compute.
Qed.

Lemma unsigned_fsize:
  forall f (WT : wt_function f),
    Int.unsigned (Int.repr f.(fn_framesize)) = f.(fn_framesize).
Proof.
  intros. pose proof (framesize_small2 _ WT).
  rewrite Int.unsigned_repr. done.
  unfold Int.max_unsigned; omega.
Qed.

Lemma unsigned_total_fsize:
  forall f (WT : wt_function f),
    Int.unsigned (total_framesize f) =
      f.(fn_paddedstacksize) + f.(fn_framesize).
Proof.
  intros. inv WT.
  unfold total_framesize.
  rewrite Int.unsigned_repr. done.
  pose proof (Int.unsigned_range (fn_stacksize f)).
  unfold Int.max_unsigned, fe_retaddrsize in *.
  split. omega.
  eapply Zle_trans with half_modulus. 
  omega. by compute.
Qed.

Lemma fsize_le_total_fsize:
  forall f (WT : wt_function f),
    f.(fn_framesize) <= Int.unsigned (total_framesize f).
Proof.
  intros. rewrite (unsigned_total_fsize _ WT).
  inv WT.
  pose proof (Int.unsigned_range (fn_stacksize f)).
  omega.  
Qed.

Lemma frame_inside_tframe:
  forall f sp (WT : wt_function f),
    range_inside (sp, Int.repr f.(fn_framesize))
                 (sp, total_framesize f).
Proof.
  intros.
  destruct sp. split. done. 
  pose proof (fsize_le_total_fsize _ WT).
  rewrite Int.unsigned_repr. omega.
  pose proof (framesize_small2 _ WT).
  unfold Int.max_unsigned; omega.
Qed.  

Lemma stkr_valid_erange:
  forall p
    (VAR: valid_alloc_range (p, Int.repr thread_stack_size)),
    valid_erange (p, Int.repr thread_stack_size).
Proof.
  intros.
  destruct p as [b ofs].
  unfold valid_alloc_range in VAR.
  split. rewrite Int.unsigned_repr; by compute.
  unfold Punsigned; destruct zeq; omega.
Qed.

(* Parent offset must be at least 4-byte away (because there must be 
   at least a return address in-between. *)
Lemma parent_offset_ge_4:
  forall f (WT: wt_function f),
    4 <= Int.unsigned (parent_offset f).
Proof.
  intros. inversion WT; subst.
  unfold parent_offset.
  pose proof (framesize_small2 _ WT).
  pose proof (stacksize_small _ WT).
  rewrite Int.unsigned_repr. unfold fe_retaddrsize; omega.
  split. omega.
  eapply Zle_trans with half_modulus. omega.
  by compute.
Qed.

Lemma parent_offset_pos:
  forall f (WT: wt_function f),
    0 < Int.unsigned (parent_offset f).
Proof.
  intros; pose proof (parent_offset_ge_4 _ WT); omega.
Qed.

Lemma unsigned_parent_offset:
  forall f (WT: wt_function f),
    Int.unsigned (parent_offset f) =
      fn_paddedstacksize f + fn_framesize f + fe_retaddrsize.
Proof.
  intros; inv WT. unfold parent_offset. 
  rewrite Int.unsigned_repr. done.
  split. omega.
  eapply Zle_trans with half_modulus. omega.
  by compute.
Qed.

Lemma unsigned_repr_ra_plus_fs:
  forall f (WT : wt_function f),
    Int.unsigned (Int.add rasize (Int.repr f.(fn_framesize))) = 
    fe_retaddrsize + fn_framesize f.
Proof.
  intros.
  pose proof (framesize_small2 _ WT). 
  pose proof (stacksize_small _ WT). 
  inv WT;  unfold fe_retaddrsize in *.
  rewrite Int.add_unsigned;
    repeat (rewrite Int.unsigned_repr; unfold Int.max_unsigned; try omega). 
      by compute.
    split. omega. 
    eapply Zle_trans with half_modulus. omega.
    by compute.
  by compute.
Qed.

(** All the space occupied by a matching stack is in the part of the
    allocated stack space that is above the stack pointer. *)
Lemma match_stack_inside:
  forall {stkr sp spart ts ss tm}
    (VE: valid_erange stkr)
    (MS: match_stacks stkr sp tm spart ts ss), 
  range_list_in_range spart (range_sp stkr sp).
Proof.
  intros.
  induction MS; subst. done.

  assert (RLIR: range_list_in_range spart' (range_sp stkr sp)).
    intros r IN. eapply range_inside_trans. by apply IHMS.
    eby eapply range_sp_inside_range_sp_add2. 
  destruct Int.eq_dec. done.
  intros r IN. destruct IN as [<- | IN]; eauto.
  assert (E: Int.unsigned (Int.repr (fe_retaddrsize + f.(fn_framesize))) = 
             fe_retaddrsize + fn_framesize f).
    rewrite Int.unsigned_repr. omega.
    inv WTF. split. omega.
    pose proof (Int.unsigned_range (fn_stacksize f)).
    apply Zle_trans with half_modulus. omega.
    by compute.
  eapply range_inside_trans, range_inside_range_sp2; try edone.
  destruct sp as [bsp osp]; destruct stkr as [[bstkr ostkr] nstkr].
  destruct RI as [-> [(Eofs & En & ABOVE) | (LT1 & LT2)]].
    by pose proof (parent_offset_pos _ WTF); omegaContradiction.
  split. done.
  right. 
  assert (Efr: Int.unsigned (Int.add osp (Int.repr (fe_retaddrsize + fn_framesize f))) = 
               Int.unsigned osp + fe_retaddrsize + fn_framesize f).
    pose proof (framesize_small2 _ WTF).
    rewrite Int.add_unsigned, E, Int.unsigned_repr;
      unfold Ptr.offset, fe_retaddrsize. omega.
    pose proof (Int.unsigned_range osp). split. omega. 
    rewrite (unsigned_parent_offset _ WTF) in LT2.
    pose proof (valid_erange_modulus VE).
    assert (Int.unsigned (fn_stacksize f) <> 0).
      intro E'. elim n. 
      by rewrite <- (Int.repr_unsigned (fn_stacksize f)), E'.
    pose proof (Int.unsigned_range (fn_stacksize f)).
    unfold fe_retaddrsize in LT2.
    inv WTF. unfold Int.max_unsigned; omega.
  rewrite Efr.
  split.  
    unfold fe_retaddrsize, Ptr.offset. inv WTF. omega. 
  rewrite (unsigned_parent_offset _ WTF). inv WTF. omega.
Qed.

Lemma stacksize_half_mod:
  forall f (WT : wt_function f),
    Int.unsigned (fn_stacksize f) < half_modulus.
Proof. intros; inv WT; omega. Qed.

Lemma type_of_chunk_inv:
  forall ty,
    type_of_chunk (chunk_of_type ty) = ty.
Proof. by intros []. Qed.

(** Machinery for threading through well-typedness of MachAbstr state. *)
Lemma taustar_wt_state:
  forall ss ss'
    (WTS: wt_state ss)
    (WS:  taustar lts ss ss'),
    wt_state ss'.
Proof.
  intros.
  induction WS. done.
  eby eapply IHWS, subject_reduction.
Qed.

Lemma sim_wt_aux:
  forall ss l ts tp tm sp
    (WTS: wt_state ss)
    (SP: exists ss',
       taustep lts ss l ss' /\
       forall (WTS' : wt_state ss'),
          match_state ts tp tm ss' sp),
    (exists ss',
       taustep lts ss l ss' /\
       match_state ts tp tm ss' sp).
Proof.
  intros. destruct SP as [ss' [WS IMP]].
  pose proof WS as [ss1 [TAU1 ST]].
  exists ss'. 
  split. done.
  apply IMP. 
  eapply subject_reduction. edone. edone.
  eby eapply taustar_wt_state. 
Qed.

(** Helpers for proving that 'Int.unsigned (Int.repr x) = x' for
     various x'es. *)
Lemma unsigned_sz:
  forall sz
  (SZLB : 0 <= sz)
  (SZHB : sz + fe_retaddrsize < half_modulus),
    Int.unsigned (Int.repr sz) = sz.
Proof.
  intros.
  rewrite Int.unsigned_repr. done.
  split. done. apply Zle_trans with half_modulus. 
  unfold fe_retaddrsize in SZHB; omega. by compute.
Qed.
  
Lemma unsigned_4: Int.unsigned (Int.repr 4) = 4.
Proof.
  by (by rewrite Int.unsigned_repr; compute).
Qed.

Lemma unsigned_4sz:
  forall sz
    (SZLB : 0 <= sz)
    (SZHB : sz + fe_retaddrsize < half_modulus),
      Int.unsigned (Int.add (Int.repr 4) (Int.repr sz)) = 4 + sz.
Proof.
  intros.
  unfold fe_retaddrsize in SZHB.
  rewrite Int.add_unsigned, !(unsigned_sz sz), unsigned_4, !Int.unsigned_repr; try omega.
  split. omega. apply Zle_trans with half_modulus. omega. by compute.
  done.
Qed.

Lemma repr_plus:
  forall x y, Int.repr (x + y) = Int.add (Int.repr x) (Int.repr y).
Proof.
  intros. unfold Int.add, Int.repr. 
  apply Int.mkint_eq. simpl. by rewrite Zplus_mod.
Qed.

Lemma match_stack_other:
  forall p chunk v stkr sp tm tm' spart ts ss
    (VE:   valid_erange stkr)
    (MS:   match_stacks stkr sp tm spart ts ss)
    (STO:  store_ptr chunk tm p v = Some tm')
    (DISJ: ranges_disjoint (range_of_chunk p chunk) 
                           (range_sp stkr sp)),
  match_stacks stkr sp tm' spart ts ss.
Proof.
  intros.
  induction MS.

  (* Base case *)
  constructor; try done.
  - rewrite <- (load_store_other STO). done.
    eapply disjoint_inside_disjoint_r. edone.
    eapply range_inside_trans, range_inside_range_sp2; try edone.
    unfold range_of_chunk.
    eapply range_inside_smaller.
      eby eapply range_inside_valide.
    unfold size_chunk.
    unfold fe_retaddrsize in *.
    rewrite Int.add_unsigned, (unsigned_sz sz), !Int.unsigned_repr; try omega; try done.
    split. omega. apply Zle_trans with half_modulus. omega. by compute.
  - eapply frame_match_store_other; try edone.
      split. done. unfold fe_retaddrsize in SZHB.
      apply Zlt_trans with half_modulus. omega. by compute.
    eapply disjoint_inside_disjoint_r. edone.
    eapply range_inside_trans, range_inside_range_sp2; try edone.
    eapply range_inside_subrange.
      eby eapply range_inside_valide. 
      unfold fe_retaddrsize. 
      rewrite unsigned_4sz, (unsigned_sz sz), unsigned_4; try done; omega.

  (* Step case *)
  pose proof (framesize_small2 _ WTF).
  pose proof (stacksize_small _ WTF).
  specialize (IHMS STO).
  econstructor; try edone.
  - eapply frame_match_store_other; try edone.  
    eapply disjoint_inside_disjoint_r. edone.
    eapply range_inside_trans, range_inside_range_sp2; try edone.
    eapply range_inside_subrange.
      eby eapply range_inside_valide.
    rewrite unsigned_parent_offset.
    rewrite !Int.unsigned_repr. omega. by unfold Int.max_unsigned; omega.
    by compute. done.
  - rewrite <- (load_store_other STO). done.
    eapply disjoint_inside_disjoint_r. edone.
    eapply range_inside_trans, range_inside_range_sp2; try edone.
    unfold range_of_chunk.
    eapply range_inside_smaller.
      eby eapply range_inside_valide.
    rewrite unsigned_parent_offset, !Int.unsigned_repr. 
    simpl. unfold fe_retaddrsize; omega. by compute. done.
  - apply IHMS. subst.
    eapply disjoint_inside_disjoint_r. edone.
    by apply range_sp_inside_range_sp_add2.
Qed.

(** Valid slot is inside frame (for function frames). *)
Lemma slot_valid_inside:
  forall {f ty ofs sp stkr}
  (SRWF : valid_erange stkr) 
  (RI : range_inside (sp, total_framesize f) stkr)
  (WT : wt_function f)
  (SV : slot_valid (fn_framesize f) ty (Int.signed ofs)),
    range_inside (range_of_chunk (sp + ofs) (chunk_of_type ty))  
                 (sp, Int.repr (fn_framesize f)).
Proof.
  intros.
  inv SV.
  assert (FSS := framesize_small2 _ WT).
  replace ofs with (Int.repr (Int.signed ofs)) 
    by (by rewrite Int.repr_signed).
  apply (lb_hb_range_inside _ (framesize_small2 _ WT)); try edone.
  destruct sp; simpl in *.
  destruct stkr as [[stkrb stkrofs] stkrn].
  pose proof (valid_erange_modulus SRWF).
  destruct RI as [_ [(-> & _) | RI2]]. omega.
  pose proof (fsize_le_total_fsize _ WT). omega.
Qed.

(** Valid slot is inside frame (for the top-level frame). *)
Lemma slot_valid_inside_base:
  forall {sz ty ofs sp stkr}
  (SRWF : valid_erange stkr) 
  (RI : range_inside (sp, Int.repr sz) stkr)
  (Lsz: 0 <= sz)
  (Hsz: sz + 4 < half_modulus)
  (SV : slot_valid sz ty (Int.signed ofs)),
    range_inside (range_of_chunk (sp + ofs) (chunk_of_type ty))  
                 (sp, Int.repr sz).
Proof.
  intros.
  inv SV.
  assert (SZ: 0 <= sz < modulus). 
    split. done.
    eapply Zlt_trans with half_modulus. omega. by compute.
  replace ofs with (Int.repr (Int.signed ofs)) 
    by (by rewrite Int.repr_signed).
  apply (lb_hb_range_inside _ SZ); try edone.
  destruct sp; simpl in *.
  destruct stkr as [[stkrb stkrofs] stkrn].
  pose proof (valid_erange_modulus SRWF).
  destruct RI as [_ [(-> & _) | RI2]]. omega. 
  rewrite Int.unsigned_repr in RI2. omega.
  by unfold Int.max_unsigned; omega.
Qed.

(** Valid slot is inside the stack space. *)
Lemma chunk_inside_stkr:
  forall {f ty ofs sp stkr}
  (SRWF : valid_erange stkr) 
  (RI : range_inside (sp, total_framesize f) stkr)
  (WT : wt_function f)
  (SV : slot_valid (fn_framesize f) ty (Int.signed ofs)),
  chunk_inside_range_list (sp + ofs) (chunk_of_type ty) (stkr :: nil).
Proof.
  intros.
  assert (RIc := slot_valid_inside SRWF RI WT SV).
  simpl. destruct range_inside_dec as [|n]; try done; elim n.
  eapply range_inside_trans. edone.
  eapply range_inside_trans, RI.
  by apply frame_inside_tframe.
Qed.

(** Chunk inside current frames does not overlap
    with the frames higher in the stack. *)
Lemma chunk_not_inside_spart:
  forall {f p c sp stkr spart tm s ss}
  (SRWF : valid_erange stkr) 
  (RI : range_inside (sp, total_framesize f) stkr)
  (WT : wt_function f)
  (RIc: range_inside (range_of_chunk p c)
                     (sp, Int.repr (fn_framesize f)))
  (MS : match_stacks stkr (sp + total_framesize f) tm spart s ss),
  range_not_in (range_of_chunk p c)
     (if Int.eq_dec (fn_stacksize f) Int.zero
      then spart
      else
       ((sp + Int.repr (fn_framesize f))%pointer, fn_stacksize f)
       :: spart).
Proof.
  intros.
  assert (FRin := frame_inside_tframe _ sp WT). 
  assert (RNI': range_not_in (range_of_chunk p c) spart).
    intros r IN.
    eapply disjoint_inside_disjoint_r, match_stack_inside; try edone.
    eapply disjoint_inside_disjoint_l. 
      eby eapply ranges_disjoint_range_sp_add2.
    eby eapply range_inside_trans. 
  destruct Int.eq_dec. edone.
  intros r IN. simpl in IN. destruct IN as [<- | IN]; [|by eauto].
  eapply disjoint_inside_disjoint_l, RIc. 
  eapply ranges_disjoint_add.
  eapply range_inside_valide. eby eapply range_inside_trans. edone.
  eby eapply stacksize_half_mod.
Qed.

Lemma slot_chunk_not_inside_spart:
  forall {f ty ofs sp stkr spart tm s ss}
  (SRWF : valid_erange stkr) 
  (RI : range_inside (sp, total_framesize f) stkr)
  (WT : wt_function f)
  (SV : slot_valid (fn_framesize f) ty (Int.signed ofs))
  (MS : match_stacks stkr (sp + total_framesize f) tm spart s ss),
  range_not_in (range_of_chunk (sp + ofs) (chunk_of_type ty))
     (if Int.eq_dec (fn_stacksize f) Int.zero
      then spart
      else
       ((sp + Int.repr (fn_framesize f))%pointer, fn_stacksize f)
       :: spart).
Proof.
  intros.
  assert (RIc := slot_valid_inside SRWF RI WT SV).
  eby eapply chunk_not_inside_spart.
Qed.

(** Ranges [(p, n)] and [(p + n, n')] are disjoint (if they are both
    contained in a well-formed stack space. *)
Lemma range_disjoint_inside_stkr:
  forall stkr p n n'
    (VE:  valid_erange stkr)
    (RI1: range_inside (p, n) stkr)
    (RI2: range_inside (Ptr.add p n, n') stkr),
      ranges_disjoint (p, n) (Ptr.add p n, n').
Proof.
  intros.
  eapply disjoint_inside_disjoint_r.
  eby eapply ranges_disjoint_range_sp_add2. 
  eby eapply range_inside_range_sp2.
Qed.

Lemma load_stkr_valid_store:
  forall stkr tm c p v tm'
  (L: load_stkr_valid stkr tm)
  (S: store_ptr c tm p v = Some tm'),
    load_stkr_valid stkr tm'.
Proof.
  intros. intros p' c' PCI RI.
  specialize (L p' c' PCI RI).
  pose proof (load_chunk_allocated_spec c' tm p') as LS.
  pose proof (load_chunk_allocated_spec c' tm' p') as LS'.
  destruct load_ptr; destruct load_ptr; try done.
  elim LS'.
  eapply chunk_allocated_and_aligned_arange. 
    eby eapply arange_eq_sym, arange_eq_store.
  edone.
Qed.

(** * Simulations of individual Machconcr transitions. *) 
Lemma mgetparam_sim:
  forall fb f sp0 ofs ty v rs chunk ptr tm sp tp rs' stkr c s ss dst
  (FF : Genv.find_funct_ptr ge fb = Some (Internal f))
  (Eptr : ptr = (sp0 + parent_offset f + ofs)%pointer)
  (Echunk : chunk = chunk_of_type ty)
  (Ers' : rs' = Regmap.set dst v rs)
  (HT : Val.has_type v (type_of_chunk chunk))
  (MS : match_state (State s fb sp0 (Mgetparam ofs ty dst :: c) stkr rs) tp tm
         ss sp),
   read_simulation Machabstr.state state (ma_step ge) match_state 
     (ltof state measure) ss
     (State s fb sp0 (Mgetparam ofs ty dst :: c) stkr rs)
     (State s fb sp0 c stkr rs') tm sp tp ptr chunk v.
Proof.
  intros.
  inv MS. rewrite FF in GETF. inv GETF.
  inversion MS0.
    (* Reading from the program arguments. *)
    unfold fe_retaddrsize in *.
    assert (Esptf: ((sp0 + total_framesize f0) + Int.repr 4)%pointer =
                   (sp0 + parent_offset f0)%pointer) by
      (by destruct sp0; unfold Ptr.add; rewrite Int.add_assoc; f_equal; f_equal;
       unfold parent_offset, Int.add; rewrite (unsigned_total_fsize _ WTF);
       rewrite Int.unsigned_repr; [|compute]).
    rewrite Esptf in *.
    assert (FSS: 0 <= sz < modulus).
      split. omega.
      eapply Zlt_trans with half_modulus. omega. by compute.
    destruct (load_ptr (Asm.chunk_of_ty ty) tm 
                       ((Ptr.add sp0 (parent_offset f0)) + ofs)) as [v'|] _eqn : L.
      (* Load success *)
      destruct (frame_match_get_slot _ FM0 L) 
        as [GS | [v'' (GS & LD')]]; pose proof GS as GS'; 
          unfold get_slot in GS; destruct slot_valid_dec as [SV | SNV]; try done.
        (* Get slot failure *)
        left. left. (* ... then Machabstr must be stuck: *)
        intros s' l ST'; inv ST'.
        by unfold get_slot in GS0; destruct slot_valid_dec.
      (* Get slot success *)
      right. left.
      assert (V := range_inside_valide _ _ RI0 SRWF).
      assert (B: Int.unsigned (Int.repr 4) + Int.unsigned (Int.repr sz) <=
                 Int.unsigned (Int.add (Int.repr 4) (Int.repr sz))).
        rewrite Int.add_unsigned,
          (Int.unsigned_repr (Int.unsigned (Int.repr 4) + Int.unsigned (Int.repr sz))).
        omega. rewrite unsigned_4, (unsigned_sz sz); try done. split. omega.
        eapply Zle_trans with half_modulus. omega. by compute.
      assert (RI1 := range_inside_subrange _ _ _ _ V B).
      rewrite Esptf in RI1. pose proof (range_inside_trans _ _ _ RI1 RI0) as RI2.
      assert (RIc := slot_valid_inside_base SRWF RI2 SZLB SZHB SV).        
      split. (* chunk inside stkr *)
        simpl. destruct range_inside_dec. done. elim n.
        eapply range_inside_trans, RI2. edone. 
      split. (* chunk not inside source partition *)
        subst spart'. destruct Int.eq_dec. done.
        intros r IN. simpl in IN. destruct IN as [<- | IN]; [|done].
        eapply disjoint_inside_disjoint_l, RIc. rewrite <- Esptf.
        eapply disjoint_inside_disjoint_l with 
          ((sp0 + total_framesize f0)%pointer,
           Int.add (Int.repr 4) (Int.repr sz));
          [|by eapply range_inside_subrange, B; 
               eapply range_inside_valide, SRWF].
        eapply ranges_disjoint_comm, disjoint_inside_disjoint_l 
          with (sp0, total_framesize f0).
        eapply range_disjoint_inside_stkr. 2 : edone. edone. edone.
        eapply range_inside_subrange. eby eapply range_inside_valide.
        rewrite (unsigned_total_fsize _ WTF), (unsigned_fsize _ WTF).
        inversion WTF. omega.
      rewrite L.
      split. done. 
      intro L'. inv L'. left.
      eapply sim_wt_aux. done.
      eexists. split.
        apply step_taustep. simpl.
        eapply Machabstr.exec_Mgetparam. apply GS'.
      intro; econstructor; try edone; [].
      by apply regset_set.
    (* Load failure *)
    left. left. (* ... then Machabstr must be stuck: *)
    intros s' l ST'; inv ST'. simpl in GS.
    by rewrite (frame_match_get_slot_none _ FM0 L) in GS.
  (* Reading from parent function stackframe *)
  unfold fe_retaddrsize in *.
  assert (Esptf: ((sp0 + total_framesize f0) + Int.repr 4)%pointer =
                 (sp0 + parent_offset f0)%pointer) by
    (by destruct sp0; unfold Ptr.add; rewrite Int.add_assoc; f_equal; f_equal;
     unfold parent_offset, Int.add; rewrite (unsigned_total_fsize _ WTF);
     rewrite Int.unsigned_repr; [|compute]).
  rewrite Esptf in *.
  assert (FSS := framesize_small2 _ WTF0).
  destruct (load_ptr (Asm.chunk_of_ty ty) tm 
                     ((Ptr.add sp0 (parent_offset f0)) + ofs)) as [v'|] _eqn : L.
    (* Load success *)
    destruct (frame_match_get_slot _ FM0 L) 
      as [GS | [v'' (GS & LD')]]; pose proof GS as GS'; 
        unfold get_slot in GS; destruct slot_valid_dec as [SV | SNV]; try done.
      (* Get slot failure *)
      left. left. (* ... then Machabstr must be stuck: *)
      intros s' l ST'; inv ST'.
      by unfold get_slot in GS0; destruct slot_valid_dec.
    (* Get slot success *)
    right. left.
    assert (RI1: range_inside ((sp0 + parent_offset f0)%pointer, 
                               total_framesize f) stkr).
      eapply range_inside_trans, RI0.
      rewrite <- Esptf.
      eapply range_inside_subrange. eby eapply range_inside_valide.
      pose proof (stacksize_small _ WTF0).
      rewrite (unsigned_parent_offset _ WTF0), unsigned_4, (unsigned_total_fsize _ WTF0). 
      unfold fe_retaddrsize. omega.
    split. (* chunk inside stkr *)
      eby eapply chunk_inside_stkr.
    split. (* chunk not inside source partition *)
      subst. unfold total_framesize, parent_offset in MS.
      rewrite (repr_plus _ fe_retaddrsize), Int.add_commut in MS.
      rewrite Ptr.add_add_r, <- (Ptr.add_add_r _ _ rasize),
        <- (repr_plus _ fe_retaddrsize) in MS.
      pose proof (slot_chunk_not_inside_spart SRWF RI1 WTF0 SV MS) as RNIsp'.
      assert (Ef: (sp0 + parent_offset f0 + Int.repr (fn_framesize f) = 
                   sp0 + total_framesize f0 + Int.repr (4 + fn_framesize f)) 
                      % pointer).
        rewrite (repr_plus 4), Ptr.add_add_r, <- (Ptr.add_add_r _ _ (Int.repr 4)).
        unfold parent_offset, fe_retaddrsize. by rewrite repr_plus.
      rewrite Ef in RNIsp'.
      destruct (Int.eq_dec (fn_stacksize f0) Int.zero). done.       
      intros r IN. apply in_inv in IN.
      destruct IN as [<- | IN]; [|by auto].
      assert (RIc := slot_valid_inside SRWF RI1 WTF0 SV).  
      assert (Efs4:  Int.unsigned (Int.add (Int.repr 4) 
                                           (Int.repr (fn_framesize f))) = 
                     4 + fn_framesize f).
        rewrite Int.add_unsigned, unsigned_4, (unsigned_fsize _ WTF0), Int.unsigned_repr.
        done.
        pose proof (stacksize_small _ WTF0).
        inv WTF0. unfold fe_retaddrsize in wt_function_instrs.
        unfold Int.max_unsigned. split. omega.
        eapply Zle_trans with half_modulus. omega. by compute.
      assert (RI2: range_inside
        ((sp0 + total_framesize f0)%pointer,
          Int.add (Int.repr 4) (Int.repr (fn_framesize f))) stkr).
        eapply range_inside_trans, RI0.
        apply range_inside_smaller. eby eapply range_inside_valide.
        rewrite Efs4.
        pose proof (stacksize_small _ WTF0).
        rewrite (unsigned_parent_offset _ WTF0). 
        unfold fe_retaddrsize. omega.
      eapply disjoint_inside_disjoint_l, RIc. rewrite <- Esptf.
      eapply disjoint_inside_disjoint_l with 
        ((sp0 + total_framesize f0)%pointer,
         Int.add (Int.repr 4) (Int.repr f.(fn_framesize)));
        [|eapply range_inside_subrange; [eby eapply range_inside_valide|];
          rewrite Efs4, unsigned_4, (unsigned_fsize _ WTF0); omega].
      eapply ranges_disjoint_comm, disjoint_inside_disjoint_l 
        with (sp0, total_framesize f0).
      eapply range_disjoint_inside_stkr. 2 : edone. edone. edone.
      eapply range_inside_subrange. eby eapply range_inside_valide.
      rewrite (unsigned_total_fsize _ WTF), (unsigned_fsize _ WTF).
      inversion WTF. omega.
    rewrite L.
    split. done. 
    intro L'. inv L'. left.
    eapply sim_wt_aux. done.
    eexists. split.
      apply step_taustep. simpl.
      eapply Machabstr.exec_Mgetparam. apply GS'.
    intro; econstructor; try edone; [].
    by apply regset_set.
  (* Load failure *)
  left. left. (* ... then Machabstr must be stuck: *)
  intros s' l ST'; inv ST'. simpl in GS.
  by rewrite (frame_match_get_slot_none _ FM0 L) in GS.          
Qed.

Lemma find_function_find_function_ptr:
  forall ros rs fb',
    find_function_ptr ge ros rs = Some fb' ->
    find_function ge ros rs = Genv.find_funct_ptr ge fb'.
Proof.
  intros; destruct ros; simpl in *.
    by destruct (rs m); vauto.
  by destruct (Genv.find_symbol ge i); vauto.
Qed.

Lemma find_function_ptr_lessdef:
  forall {tge ros rs x rs'},
  find_function_ptr tge ros rs = Some x ->
  regset_lessdef rs rs' ->
  find_function_ptr tge ros rs' = Some x.
Proof.
  intros.
  destruct ros as [r|i]; simpl in *; try done.
  specialize (H0 r); destruct (rs r); try done; inv H0; done.
Qed.

Lemma find_function_lessdef:
  forall {tge ros rs x rs'},
  find_function tge ros rs = Some x ->
  regset_lessdef rs rs' ->
  find_function tge ros rs' = Some x.
Proof.
  intros.
  destruct ros as [r|i]; simpl in *; try done.
  specialize (H0 r); destruct (rs r); try done; inv H0; done.
Qed.

Lemma tframe_inside_po:
  forall sp f,
  valid_erange (sp, parent_offset f) ->
  wt_function f ->
  range_inside ((sp + rasize)%pointer, total_framesize f)
               (sp, parent_offset f).
Proof.
  intros.
  eapply range_inside_subrange. done.
  rewrite unsigned_parent_offset, unsigned_total_fsize, unsigned_rasize;
    try done; omega.
Qed.

Hint Resolve range_inside_trans 
             range_inside_valide 
             range_inside_bottom
             range_inside_top
             range_sp_inside_range_sp_add2
             range_inside_range_sp2
             frame_inside_tframe
             tframe_inside_po : ri.

Ltac ri_res := eby eauto with ri.

Lemma mcall_sim:
  forall ros f' fb f c roffs s sp0 sig stkr rs tp tm ss sp
  (FF : find_function_ptr ge ros rs = Some f')
  (GFF : Genv.find_funct_ptr ge fb = Some (Internal f))
  (RA : Asmgenretaddr.return_address_offset f c roffs)
  (MS : match_state (State s fb sp0 (Mcall sig ros :: c) stkr rs) tp tm ss sp)
  (RI : range_inside (Ptr.sub_int sp0 rasize, Int.zero) stkr),
   write_simulation Machabstr.state state (ma_step ge) match_state
     (ltof state measure) ss (State s fb sp0 (Mcall sig ros :: c) stkr rs)
     (Callstate
        (Stackframe fb sp0 (Ptr (Int.unsigned (Ptr.offset fb)) roffs) c :: s)
        f' (Ptr.sub_int sp0 rasize) stkr rs) tm sp tp
     (Ptr.sub_int sp0 rasize) Mint32
     (Vptr (Ptr (Int.unsigned (Ptr.offset fb)) roffs)).
Proof.
  intros.
  inv MS.
  destruct (find_function ge ros rs') as [f''|] _eqn : FF'';
    [| left; left; intros s' l ST'; inv ST'; clarify']. 
  assert (RI1: range_inside (Ptr.sub_int sp0 rasize, rasize)
                       stkr).
    eapply range_inside_endpoints_sub2; ri_res.
  right; left. 
  split. (* the store is inside Machconcr stack space *)
    simpl. destruct range_inside_dec. done. by elim n.
  split. (* the store is outside Machabstr stack *)
    assert(RLIR := match_stack_inside SRWF MS0).
    assert(RLIR1 : range_list_in_range spart' (range_sp stkr sp0)).
      intros r IN; ri_res. 
    assert(RLIR2: range_list_in_range
      (if Int.eq_dec (fn_stacksize f0) Int.zero
       then spart'
       else
        ((sp0 + Int.repr (fn_framesize f0))%pointer, fn_stacksize f0)
        :: spart')
         (range_sp stkr sp0)).
      destruct Int.eq_dec. done.
      intros r IN. destruct (in_inv IN) as [<- | IN'].
        eapply range_inside_trans; [|eby eapply range_inside_range_sp2]. 
        eapply range_inside_subrange. ri_res. 
        rewrite (unsigned_fsize _ WTF), (unsigned_total_fsize _ WTF).
        inv WTF. omega.
      apply (RLIR1 r IN').
    intros r IN.
    eapply disjoint_inside_disjoint_r, (RLIR2 r IN).
    unfold range_of_chunk.
    eapply ranges_disjoint_range_sp_sub; ri_res.
  pose proof (LSV _ _ (ra_aligned _ ALG) RI1) as L.
  pose proof (load_chunk_allocated_spec Mint32 tm (Ptr.sub_int sp0 rasize)).
  pose proof (store_chunk_allocated_spec Mint32 tm (Ptr.sub_int sp0 rasize)
    (Vptr (Ptr (Int.unsigned (Ptr.offset fb)) roffs))).
  destruct load_ptr; [|done].
  destruct (store_ptr Mint32 tm (Ptr.sub_int sp0 rasize)
       (Vptr (Ptr (Int.unsigned (Ptr.offset fb)) roffs))) as [tm'|] _eqn:S;
   [|done].
  exists tm'. split. done.
  left.
  apply sim_wt_aux. done.
  eexists. split.
    apply step_taustep. simpl.
    eby eapply Machabstr.exec_Mcall.
  intro WTS'.
  pose proof (find_function_lessdef FF'' REGS) as FFX.
  rewrite (find_function_find_function_ptr _ _ _ FF) in FFX.
  econstructor; try done.
  (* Stack match *)
  assert (Esp0: sp0 = Ptr.add (Ptr.sub_int sp0 rasize) rasize)
    by (by rewrite Ptr.add_sub_l, Int.sub_idem, Ptr.add_zero_r).
  rewrite Esp0 at 2; clear Esp0.
  assert (Epo : parent_offset f0 = Int.add (total_framesize f0) rasize).
    rewrite Int.add_unsigned, (unsigned_total_fsize _ WTF). 
    unfold parent_offset. by rewrite Int.unsigned_repr; [|compute].  
  assert (RI2 : range_inside (Ptr.sub_int sp0 rasize, parent_offset f0) stkr).
    rewrite Epo.
    eapply range_inside_sub_add2.
    rewrite (unsigned_total_fsize _ WTF). inv WTF. rewrite Int.unsigned_repr; [|by compute].
    omega. edone. edone.       
  eapply match_stacks_cons; try edone.
  - rewrite Ptr.add_sub_l, Int.sub_idem, Ptr.add_zero_r. 
    eapply frame_match_store_other. apply (framesize_small2 _ WTF).
    edone. edone.
    eapply disjoint_inside_disjoint_r, (frame_inside_tframe _ sp0 WTF).
    eapply disjoint_inside_disjoint_r; [| eby eapply range_inside_range_sp2].
    eapply ranges_disjoint_range_sp_sub; ri_res. 
  - erewrite load_store_similar; try edone. by simpl.
  - by clarify'. 
  - replace (Int.repr (fe_retaddrsize + fn_framesize f0)) with
            (Int.add rasize (Int.repr (fn_framesize f0))).
      eby rewrite Ptr.add_sub_l, Int.sub_add_l, Int.sub_idem, 
        Int.add_commut, Int.add_zero.
    unfold Int.add. rewrite unsigned_rasize. 
    by rewrite (unsigned_fsize _ WTF).
  - by rewrite Ptr.add_sub_l, Int.sub_idem, Ptr.add_zero_r.
  - eapply match_stack_other; try edone. 
    by rewrite Epo, Ptr.add_sub_l, Int.add_commut, Int.sub_add_l, 
      Int.sub_idem, Int.add_commut, Int.add_zero. 
    eapply disjoint_inside_disjoint_l.
    eapply ranges_disjoint_range_sp_add2. edone. edone. 
    eapply range_inside_smaller. eby eapply range_inside_valide.
    pose proof (parent_offset_ge_4 _ WTF).
    by rewrite Int.unsigned_repr; [|compute].
  - eby eapply load_stkr_valid_store.
    apply Zmod_divide. done. destruct sp0; simpl.
    rewrite Zplus_mod. rewrite <- Zmod_div_mod; try done.
    rewrite Zminus_mod. rewrite <- Zmod_div_mod; try done.
    apply Zdivide_mod in ALG. simpl in ALG. rewrite ALG.
    by compute. 
    by apply Zmod_divide; compute.
    by apply Zmod_divide; compute.
  - eapply wt_ge.
    by instantiate (1 := Vptr f'). 
Qed.

Lemma align_mreturn:
  forall sp f (WT : wt_function f)
   (ALG : (16 | Int.unsigned (Ptr.offset sp))),
   (16 | Int.unsigned (Ptr.offset (sp + total_framesize f)%pointer) +
     fe_retaddrsize).
Proof.
  intros [b ofs] ? ? ?.
  simpl in *. assert (16 | modulus) by (by apply Zmod_divide; compute).
  apply Zmod_divide. done. apply Zdivide_mod in ALG.
  rewrite Zplus_mod. rewrite <- Zmod_div_mod; try done.
  rewrite (Zplus_mod (Int.unsigned ofs)).
  rewrite ALG, Zplus_0_l, Zmod_mod, <- Zmod_div_mod; try done.
  rewrite <- Zplus_mod. apply Zdivide_mod. by inv WT.
Qed.

Lemma align_call:
  forall sp f (WT : wt_function f)
  (ALG : (16 | Int.unsigned (Ptr.offset sp) + fe_retaddrsize)),
   (16 | Int.unsigned (Ptr.offset (Ptr.sub_int sp (total_framesize f)))).
Proof.
  intros [b ofs] ? ? ?.
  simpl in *. assert (16 | modulus) by (by apply Zmod_divide; compute).
  apply Zmod_divide. done. apply Zdivide_mod in ALG.
  inv WT. apply Zdivide_mod in wt_function_framesize_aligned.
  rewrite <- Zmod_div_mod; try done.
  rewrite Zminus_mod. rewrite <- Zmod_div_mod; try done.
  replace (fn_paddedstacksize f + fn_framesize f) with
    ((fn_paddedstacksize f + fn_framesize f + fe_retaddrsize) - fe_retaddrsize) 
    by omega.
  rewrite (Zminus_mod _ fe_retaddrsize), wt_function_framesize_aligned.
  assert (E0 : 0 = (0 mod 16)) by (by compute). rewrite E0 at 1.
  rewrite <- Zminus_mod. rewrite <- E0, Zminus_minus_zero.
  replace (fe_retaddrsize mod 16) with fe_retaddrsize by (by compute).
  done.
Qed.  

Lemma slot_aligned:
  forall p f ty ofs
  (ALG' : (16 | Int.unsigned (Ptr.offset p)))
  (SV : slot_valid f ty ofs),
   pointer_chunk_aligned (Ptr.add p (Int.repr ofs)) (chunk_of_type ty).
Proof.
  intros. inv SV. destruct p; simpl in *. 
  apply Zdivide_mod in ALG'. apply Zdivide_mod in ALG.
  replace (align_chunk (chunk_of_type ty)) with 4 by (by destruct ty; compute).
  apply Zmod_divide. done.
  assert (4 | modulus) by (by apply Zmod_divide; compute).
  rewrite <- Zmod_div_mod; try done.
  rewrite Zplus_mod. rewrite <- Zmod_div_mod; try done.
  assert (D4_16: (4 | 16)) by (by apply Zmod_divide; compute).
  rewrite (Zmod_div_mod 4 16 (Int.unsigned i) (refl_equal _) (refl_equal _) D4_16).
  rewrite ALG', ALG. by compute.
Qed.

Lemma align_size_div_16:
  forall sz, (align_size sz | 16).
Proof.
  intros.
  unfold align_size. 
  by repeat (destruct zlt); apply Zmod_divide; compute.
Qed.

Lemma valid_alloc_range_inside:
  forall stkr f sp
  (VAR : valid_alloc_range stkr)
  (SRWF: valid_erange stkr)
  (RIS : range_inside (sp, total_framesize f) stkr)
  (WT  : wt_function f)
  (ALG : (16 | Int.unsigned (Ptr.offset sp)))
  (NZ  : fn_stacksize f <> Int.zero),
    valid_alloc_range (Ptr.add sp (Int.repr (fn_framesize f)), fn_stacksize f).
Proof.
  intros. destruct stkr as [[bs os] ns].
  destruct sp.
  pose proof (framesize_small2 _ WT).
  pose proof (Int.unsigned_range (fn_stacksize f)).
  assert (Int.unsigned (fn_stacksize f) <> 0). 
    intro E; elim NZ.
    apply Int.unsigned_eq. rewrite unsigned_zero. omega.
  destruct RIS as [-> [(E1 & E2 & E3) | (LB & HB)]].
    rewrite (unsigned_total_fsize _ WT) in E2.
    inv WT. omegaContradiction.
  rewrite (unsigned_total_fsize _ WT) in *.
  simpl in *.
  rewrite !Zmod_small; try omega.
    inv WT; repeat (split; [omega|]).
    apply Zdivide_plus_r. eapply Zdivide_trans, ALG. apply align_size_div_16.
    done.
  rewrite Zmod_small; [|omega].
  inv WT. omega.
Qed.

Lemma function_internal_sim:
  forall fb f sp0 sp' stkr rs tp tm ss sp s
    (GFF : Genv.find_funct_ptr ge fb = Some (Internal f))
    (Esp': sp' = Ptr.sub_int sp0 (total_framesize f))
    (RI':  range_inside (sp', Int.zero) stkr)
    (MS:   match_state (Callstate s fb sp0 stkr rs) tp tm ss sp),
  tau_simulation Machabstr.state state (ma_step ge) match_state
    (ltof state measure) ss (Callstate s fb sp0 stkr rs)
    (State s fb sp' (fn_code f) stkr rs) tm sp tp.
Proof.
  intros.
  inv MS. rewrite FIND in GFF; inv GFF.
  inversion WTF as [|f' WT E]. subst.
  assert(RIS: range_inside (Ptr.sub_int sp0 (total_framesize f),
                            total_framesize f) stkr).
    eapply range_inside_endpoints_sub2; try done.
      inv STACKS; eby eapply range_inside_bottom.
    rewrite (unsigned_total_fsize _ WT).
    inv WT. unfold fe_retaddrsize in *. omega.
  assert (MM: Int.unsigned (Ptr.offset (Ptr.sub_int sp0 (total_framesize f))) +
              fn_framesize f <= modulus).
    unfold Ptr.offset, Ptr.sub_int.
    destruct sp0. destruct stkr as [[bs os] ns]. 
    destruct RIS as [-> [(E1 & E2 & E3) | ?]].
      unfold Ptr.offset, Ptr.sub_int. rewrite E1. 
      pose proof (framesize_small2 _ WT). omega.
    pose proof (valid_erange_modulus SRWF).
    assert (fn_framesize f <= Int.unsigned (total_framesize f)).
      rewrite (unsigned_total_fsize _ WT).
      pose proof (stacksize_small _ WT). omega.
    omega.
  assert (ALG' := align_call _ _ WT ALG).
  destruct (Int.eq_dec (fn_stacksize f) Int.zero).
    (* Empty Machabstr stack *)
    right; left.
    eapply sim_wt_aux. done.
    eexists. split.
      apply step_taustep. simpl. 
      eby eapply Machabstr.exec_function_internal_empty; eauto. 
    intro; econstructor; eauto.
    - (* Frame match *)
      constructor. done.
      intros ty ofs SV. 
      destruct (load_ptr (chunk_of_type ty) tm
        (Ptr.sub_int sp0 (total_framesize f) + Int.repr ofs)) as [] _eqn:L.
        eby eexists.
      pose proof (lb_hb_range_inside _ (framesize_small2 _ WT) _ _ _ MM SV).
      exploit (LSV (Ptr.add (Ptr.sub_int sp0 (total_framesize f)) (Int.repr ofs))
                   (chunk_of_type ty)).
        eby eapply slot_aligned.
      eapply range_inside_trans. 
        apply (lb_hb_range_inside _ (framesize_small2 _ WT) _ _ _ MM SV).
      eapply range_inside_trans, RIS.
      eby eapply frame_inside_tframe.
      done. done.
    - (* stack partition does not change *)
      destruct Int.eq_dec. reflexivity. done.
    - (* match stacks *)
      eby rewrite Ptr.add_sub_l, Int.sub_idem, Ptr.add_zero_r.
  (* stacksize not zero (need to free in Machabstr *)
  right. right. right. left.
  exists (Ptr.add (Ptr.sub_int sp0 (total_framesize f)) (Int.repr (fn_framesize f))). 
  exists (fn_stacksize f).
  split. (* valid allocation range *)
    eby eapply valid_alloc_range_inside.
  split. (* Inside stkr *)
    exists stkr. split.
    eapply range_inside_trans, RIS.
    eapply range_inside_subrange. eby eapply range_inside_valide.
    rewrite (unsigned_total_fsize _ WT), (unsigned_fsize _ WT).
    inv WT; omega.
    split. by left.
    pose proof (match_stack_inside SRWF STACKS) as RLIR.
    intros r' IN'. specialize (RLIR _ IN').
    eapply disjoint_inside_disjoint_r, RLIR.
    assert (RI1: range_inside ((Ptr.sub_int sp0 
      (total_framesize f) + Int.repr (fn_framesize f))%pointer,
        fn_stacksize f) 
      (Ptr.sub_int sp0 (total_framesize f), total_framesize f)).
      eapply range_inside_subrange. ri_res.
      rewrite (unsigned_total_fsize _ WT), (unsigned_fsize _ WT).
      by inv WT; omega.
    eapply disjoint_inside_disjoint_l, RI1.
    assert (Esp0 : sp0 = (Ptr.add (Ptr.sub_int sp0 (total_framesize f))
                               (total_framesize f))).
      by rewrite <- Ptr.add_sub_r, Int.sub_idem, Ptr.add_zero_r.
    rewrite Esp0 at 2.
    eby eapply ranges_disjoint_range_sp_add2. 
  eapply sim_wt_aux. done.
  eexists. split.
    apply step_taustep. simpl. 
    eby eapply Machabstr.exec_function_internal_nonempty; eauto. 
  intro; econstructor; eauto.
  - (* Frame match *)
    constructor. done.
    intros ty ofs SV. 
    destruct (load_ptr (chunk_of_type ty) tm
      (Ptr.sub_int sp0 (total_framesize f) + Int.repr ofs)) as [] _eqn:L.
      eby eexists.
    pose proof (lb_hb_range_inside _ (framesize_small2 _ WT) _ _ _ MM SV).
    exploit (LSV (Ptr.add (Ptr.sub_int sp0 (total_framesize f)) (Int.repr ofs))
                 (chunk_of_type ty)).
      eby eapply slot_aligned.
    eapply range_inside_trans. 
      apply (lb_hb_range_inside _ (framesize_small2 _ WT) _ _ _ MM SV).
    eapply range_inside_trans, RIS.
    eby eapply frame_inside_tframe.
    done. done.
  - (* stack partition does not change *)
    destruct Int.eq_dec; [contradiction|reflexivity].
  - right. split. done.
    by rewrite !Ptr.sub_add_l, Int.sub_idem, Ptr.add_zero_r.
  - (* match stacks *)
    eby rewrite Ptr.add_sub_l, Int.sub_idem, Ptr.add_zero_r.
Qed.

Lemma ra_inside_ret:
  forall {f sp stkr}
    (WTF: wt_function f)
    (SRWF : valid_erange stkr)
    (RI : range_inside (sp, parent_offset f) stkr),
      range_inside (range_of_chunk sp Mint32) stkr.
Proof.
  intros.
  eapply range_inside_trans, RI.
  eapply range_inside_smaller. eby eapply range_inside_valide.
  rewrite (unsigned_parent_offset _ WTF).
  pose proof (stacksize_small _ WTF); pose proof (framesize_small2 _ WTF).
  simpl. unfold fe_retaddrsize; replace (4 mod modulus) with 4 by (by compute).
  omega.
Qed.

Lemma return_range_not_in:
  forall stkr f0 sp0 tm spart' s s0
  (SRWF : valid_erange stkr)
  (WTF : wt_function f0)
  (RI : range_inside (sp0, parent_offset f0) stkr)
  (MS : match_stacks stkr (sp0 + parent_offset f0) tm spart' s s0),
   range_not_in (range_of_chunk sp0 Mint32)
     (if Int.eq_dec (fn_stacksize f0) Int.zero
      then spart'
      else
       ((sp0 + Int.repr (fe_retaddrsize + fn_framesize f0))%pointer,
       fn_stacksize f0) :: spart').
Proof.
  intros.
  assert(RLIR := match_stack_inside SRWF MS).
  assert(RI': range_inside (Ptr.add sp0 rasize, total_framesize f0) 
                           (sp0, parent_offset f0)).
    eapply range_inside_subrange. ri_res. 
    rewrite unsigned_rasize, (unsigned_total_fsize _ WTF), 
      (unsigned_parent_offset _ WTF). omega.
  assert(RLIR1 : range_list_in_range spart' 
    (range_sp stkr (Ptr.add sp0 rasize))).
    intros r IN. 
    eapply range_inside_trans. apply (RLIR r IN).
    replace (Ptr.add sp0 (parent_offset f0)) 
       with (Ptr.add (Ptr.add sp0 rasize) (total_framesize f0)).
      eapply range_sp_inside_range_sp_add2; ri_res.
    rewrite !Ptr.add_add_l, Int.add_unsigned, (unsigned_total_fsize _ WTF).
    unfold parent_offset; f_equal; f_equal; rewrite unsigned_rasize; omega.
  assert(RLIR2: range_list_in_range
    (if Int.eq_dec (fn_stacksize f0) Int.zero
     then spart'
     else
      ((sp0 + Int.repr (fe_retaddrsize + fn_framesize f0))%pointer, 
        fn_stacksize f0)
      :: spart')
       (range_sp stkr (Ptr.add sp0 rasize))).
    destruct Int.eq_dec. done.
    intros r IN. destruct (in_inv IN) as [<- | IN']; eauto.
    replace (Int.repr (fe_retaddrsize + fn_framesize f0)) with
            (Int.add rasize (Int.repr f0.(fn_framesize))) by
      (by rewrite Int.add_unsigned, unsigned_rasize, (unsigned_fsize _ WTF)).
    rewrite <- Ptr.add_add_l.
    eapply range_inside_trans with (sp0 + rasize, total_framesize f0)%pointer.
      eapply range_inside_subrange. ri_res.
      rewrite (unsigned_fsize _ WTF), (unsigned_total_fsize _ WTF).
      inv WTF; omega.
    eapply range_inside_range_sp2; ri_res.
  intros r IN.
  eapply disjoint_inside_disjoint_r, (RLIR2 r IN).
  unfold range_of_chunk. 
  assert (RIra := ra_inside_ret WTF SRWF RI).
  eapply ranges_disjoint_range_sp_add; ri_res.
Qed.

Lemma return_sim:
  forall sp' sp0 f ra c s stkr rs tp tm ss sp
  (Esp': sp' = (sp0 + rasize)%pointer)
  (MS : match_state (Returnstate (Stackframe f sp' ra c :: s) sp0 stkr rs) tp
         tm ss sp),
   read_simulation Machabstr.state state (ma_step ge) match_state 
     (ltof state measure) ss
     (Returnstate (Stackframe f sp' ra c :: s) sp0 stkr rs)
     (State s f sp' c stkr rs) tm sp tp sp0 Mint32 
     (Vptr ra).
Proof.
  intros.
  inv MS.
  inv STACKS.
  right; left.
  assert (RIra := ra_inside_ret WTF SRWF RI).
  split. (* chunk in stkr *)
    simpl. destruct range_inside_dec as [|n]. done. by elim n. 
  split. (* ... but not in the machabstr stack *)
    eby eapply return_range_not_in.
  split. (* the load succeeds *)
    by rewrite LDra.
  intro L. (* The simulation *)
  left. eapply sim_wt_aux. done.
  eexists. split.
    apply step_taustep. simpl. 
    eby eapply Machabstr.exec_return; eauto. 
  intro; econstructor; try edone. 
  - rewrite Ptr.add_add_l.
    unfold Int.add. rewrite (unsigned_fsize _ WTF).
    eby rewrite Int.unsigned_repr; [|by compute].
  - eapply range_inside_trans, RI.
    eapply range_inside_subrange. eby eapply range_inside_valide.
    rewrite (unsigned_total_fsize _ WTF), (unsigned_parent_offset _ WTF).
    rewrite Int.unsigned_repr; [|by compute]. omega.
  - apply Zmod_divide; try done; apply Zdivide_mod in ALG; try done.
    destruct sp0; simpl in ALG |- *.
    assert (16 | modulus) by (by apply Zmod_divide; compute).
    by rewrite <- Zmod_div_mod.
  - by rewrite Ptr.add_add_l, Int.add_commut, Int.add_unsigned, 
      (unsigned_total_fsize _ WTF), Int.unsigned_repr; [|by compute].
Qed. 

Lemma ra_inside_ret_exit:
  forall {sz sp0 stkr}
    (SRWF : valid_erange stkr)
    (SZLB : 0 <= sz)
    (SZHB : sz + 4 < half_modulus)
    (RI : range_inside (sp0, Int.add rasize (Int.repr sz)) stkr),
      range_inside (range_of_chunk sp0 Mint32) stkr.
Proof.
  intros.
  assert (half_modulus < Int.max_unsigned) by (by compute).
  unfold fe_retaddrsize in SZHB.
  eapply range_inside_trans, RI.
  eapply range_inside_smaller. ri_res. rewrite size_chunk_repr.
  rewrite Int.add_unsigned, (unsigned_sz sz), unsigned_rasize4, 
    Int.unsigned_repr; try done.
    unfold size_chunk; omega.
  omega.
Qed.

Lemma return_exit_sim:
  forall sp0 stkr rs tp tm ss sp
    (MS : match_state (Returnstate nil sp0 stkr rs) tp tm ss sp),
   read_simulation Machabstr.state state (ma_step ge) match_state 
     (ltof state measure) ss
     (Returnstate nil sp0 stkr rs)
     (Freestackstate stkr) tm sp tp sp0 Mint32 (Vptr nullptr).
Proof.
  intros.
  inv MS.
  inv STACKS.
  right; left.
  assert (RIra := ra_inside_ret_exit SRWF SZLB SZHB RI).
  split. (* chunk in stkr *)
    simpl. destruct range_inside_dec as [|n]. done. by elim n. 
  split. (* ... but not in the machabstr stack *)
    done.
  split. (* the load succeeds *)
    by rewrite RA.
  intro L. (* The simulation *)
  right. left. 
  split. constructor. done.
Qed.

Lemma return_fail_sim:
  forall ra s sp0 stkr rs tp tm ss sp
    (RA: ra <> Vptr (get_ra s))
    (SF: match s with
       | nil => True
       | Stackframe _ sp' _ _ :: _ => sp' = (sp0 + rasize)%pointer
       end)
    (TY: Val.has_type ra Tint)
    (MS : match_state (Returnstate s sp0 stkr rs) tp tm ss sp),
   read_simulation Machabstr.state state (ma_step ge) match_state
     (ltof state measure) ss (Returnstate s sp0 stkr rs) Errorstate tm sp tp
     sp0 Mint32 ra.
Proof.
  intros. right; left.
  inv MS.
  inv STACKS.
    (* Stack base *)
    assert (RIra := ra_inside_ret_exit SRWF SZLB SZHB RI).
    split. 
      simpl. destruct range_inside_dec as [|n]. done. by elim n. 
    split. done.
    split. by rewrite RA0.
    simpl in *. intro E; rewrite E in RA0. by inv RA0.
  (* Standard stackframe *)
  assert (RIra := ra_inside_ret WTF SRWF RI).
  split. (* chunk in stkr *)
    simpl. destruct range_inside_dec as [|n]. done. by elim n. 
  split. (* ... but not in the machabstr stack *)
    eby eapply return_range_not_in.
  split. (* the load succeeds *)
    by rewrite LDra.
  intro L. rewrite LDra in L. by inv L. 
Qed.  

Lemma cast_value_to_chunk_has_type:
  forall {v ty}
  (HT : Val.has_type v ty),
  cast_value_to_chunk (chunk_of_type ty) v = v.
Proof.
  intros. by destruct ty; destruct v.
Qed.

Lemma msetstack_sim:
  forall ptr sp0 ofs ty rs src chunk v s f c stkr tp tm ss sp
    (Eptr : ptr = (sp0 + ofs)%pointer)
    (Echunk : chunk = chunk_of_type ty)
    (Ev : v = Val.conv (rs src) (type_of_chunk chunk))
    (HT : Val.has_type v (type_of_chunk chunk))
    (MS : match_state (State s f sp0 (Msetstack src ofs ty :: c) stkr rs) tp tm
         ss sp),
   write_simulation Machabstr.state state (ma_step ge) match_state
     (ltof state measure) ss
     (State s f sp0 (Msetstack src ofs ty :: c) stkr rs)
     (State s f sp0 c stkr rs) tm sp tp ptr chunk 
     (cast_value_to_chunk chunk v).
Proof.
  intros.
    destruct (store_ptr (Asm.chunk_of_ty ty) tm (sp0 + ofs) 
                        (cast_value_to_chunk (Asm.chunk_of_ty ty) v)) 
      as [tm'|] _eqn : S; inv MS;
      assert (FSS := framesize_small2 _ WTF).
      rewrite type_of_chunk_inv in *.
      (* Store success *)
      exploit frame_match_set_slot.
        apply FSS. apply FM. apply S. by destruct ty; destruct (rs src).
        apply cast_value_to_chunk_lessdef; apply Val.conv_lessdef; apply REGS.
      intros [SS' | [fr' (SS' & FM')]]; pose proof SS' as SS''; 
        unfold set_slot in SS'; destruct slot_valid_dec as [SV | SNV]; try done.
        (* Set slot failure *)
        left. left. (* ... then Machabstr must be stuck: *)
        intros s' l ST'; inv ST'.
        by unfold set_slot in SS; destruct slot_valid_dec.
      (* Set slot success *)
      right. left.
      assert (RIc := slot_valid_inside SRWF RI WTF SV).
      assert (FRin := frame_inside_tframe _ sp0 WTF). 
      split. eby eapply chunk_inside_stkr.  
      split. eby eapply chunk_not_inside_spart.
      exists tm'. split. done. left.
      inversion WTS. subst. specialize (WTRS src).
      apply is_tail_in in TAIL. inv WTF. 
      pose proof (wt_function_instrs _ TAIL) as WI. inv WI.
      rewrite (Val.conv_wt2 _ _ WTRS) in *.
      rewrite (cast_value_to_chunk_has_type WTRS) in *.
      apply sim_wt_aux. done.
      eexists. split.
        apply step_taustep. simpl.
        eapply Machabstr.exec_Msetstack. apply SS''.
      intro; econstructor; try edone.
        eby eapply load_stkr_valid_store.
      eapply match_stack_other; try edone. 
      eapply disjoint_inside_disjoint_l, RIc. 
      eapply disjoint_inside_disjoint_l, FRin. 
      eby eapply ranges_disjoint_range_sp_add2.
    (* Store failure *)
    left. left. (* ... then Machabstr must be stuck: *)
    intros s' l ST'; inv ST'. rewrite type_of_chunk_inv in *.
    exploit frame_match_set_slot_none.
      apply FSS. apply FM. apply S. by destruct ty; destruct (rs src). 
      apply cast_value_to_chunk_lessdef; apply Val.conv_lessdef. apply REGS.
    inversion WTS. subst. specialize (WTRS src).
    apply is_tail_in in TAIL. inv WTF. 
    pose proof (wt_function_instrs _ TAIL) as WI. inv WI.
    rewrite (Val.conv_wt2 _ _ WTRS), (cast_value_to_chunk_has_type WTRS) in *.
    rewrite SS. done.
Qed.

Lemma initretaddr_sim:
  forall pfn sp0 stkr rs tp tm ss sp
  (MS : match_state (Initargsstate pfn nil nil sp0 stkr rs) tp tm ss sp),
   write_simulation Machabstr.state state (ma_step ge) match_state
     (ltof state measure) ss (Initargsstate pfn nil nil sp0 stkr rs)
     (Callstate nil pfn sp0 stkr rs) tm sp tp sp0 Mint32 
     (Vptr nullptr).
Proof.
  intros.
  inv MS.
  pose proof (store_chunk_allocated_spec Mint32 tm sp0 (Vptr nullptr)) as SCA.
  pose proof (load_chunk_allocated_spec Mint32 tm sp0) as LCA.
  assert (L := LSV sp0 Mint32).
  destruct locs2; try done.
  inv LD.
  pose proof (Conventions.size_arguments_above (funsig f)) as SApos.
  assert (BND: 4 * Conventions.size_arguments (funsig f) + fe_retaddrsize < 
               half_modulus).
    inv WTS. inv H3. unfold fe_retaddrsize in *.
    simpl; omega.
  assert (Eusa: 4 * Conventions.size_arguments (funsig f) =
                Int.unsigned (Int.repr (4 * Conventions.size_arguments (funsig f)))). 
    rewrite Int.unsigned_repr. done. 
    split. omega.
    eapply Zle_trans with half_modulus; [|by compute].
    unfold fe_retaddrsize in *. omega.
  assert (Eusra: Int.unsigned
     (Int.repr (fe_retaddrsize + 4 * Conventions.size_arguments (funsig f))) =
     fe_retaddrsize + 4 * Conventions.size_arguments (funsig f)).
      unfold fe_retaddrsize in *.
      rewrite Int.unsigned_repr. omega.
      split. omega.
      eapply Zle_trans with half_modulus; [|by compute].
      unfold fe_retaddrsize in *; rewrite Zplus_comm; omega.
  destruct (store_ptr Mint32 tm sp0 (Vptr nullptr)) as [tm'|] _eqn:S;
    destruct load_ptr; try done.
    right. left.
    split. 
      unfold chunk_inside_range_list.
      destruct range_inside_dec. done.
      elim n. eapply range_inside_trans, RI. 
      apply range_inside_smaller. ri_res. 
      rewrite size_chunk_repr, Eusra.
      unfold size_chunk, fe_retaddrsize; omega.
    split. done.
    exists tm'. split. done.
    right. (* Stutter *)
    split; [|done].
    apply match_states_call; try done.
      apply match_stacks_nil;
        try rewrite Ptr.sub_add_l, Int.sub_idem, Ptr.add_zero_r; try done.
      - omega.
      - replace  (Int.add rasize (Int.repr (4 * Conventions.size_arguments (funsig f))))
           with (Int.repr (fe_retaddrsize + 4 * Conventions.size_arguments (funsig f))). done.
        unfold Int.add. by rewrite <- Eusa, unsigned_rasize. 
      - by rewrite (load_store_similar S).
      - rewrite <- app_nil_end.
        eapply frame_match_store_other.
              by rewrite Eusa; apply Int.unsigned_range.
            rewrite <- app_nil_end in SG. rewrite <- SG in FM. unfold build_frame.
          edone. edone.
        eapply range_disjoint_inside_stkr; try edone;
          eapply range_inside_trans, RI.
          apply range_inside_smaller. ri_res.
          rewrite Eusra, unsigned_rasize; omega.
        apply range_inside_subrange. ri_res.
        rewrite Eusra, unsigned_rasize; omega.
    eby eapply load_stkr_valid_store.
    by specialize (wt_ge (Vptr pfn) _ FIND).
  left.
  exploit L. destruct sp0; simpl in *.
    assert (D4_16: (4 | 16)) by (by apply Zmod_divide; compute).
    assert (D4 := Zdivide_trans _ _ _ D4_16 ALG).
    apply Zdivide_mod in D4. rewrite Zplus_mod in D4.
    replace (fe_retaddrsize mod 4) with 0 in D4 by (by compute). 
    rewrite Zplus_0_r, Zmod_mod in D4. by apply Zmod_divide. 
    eapply range_inside_trans, RI.
    apply range_inside_smaller. ri_res. 
    rewrite size_chunk_repr, Eusra.
    unfold size_chunk, fe_retaddrsize; omega.
    done. 
  done.
Qed.

Lemma mgetstack_sim:
  forall ptr sp0 ofs ty rs' rs dst v chunk s f c stkr tp tm ss sp
  (Eptr : ptr = (sp0 + ofs)%pointer)
  (Echunk : chunk = chunk_of_type ty)
  (Ers' : rs' = Regmap.set dst v rs)
  (HT : Val.has_type v (type_of_chunk chunk))
  (MS : match_state (State s f sp0 (Mgetstack ofs ty dst :: c) stkr rs) tp tm
         ss sp),
   read_simulation Machabstr.state state (ma_step ge) match_state
     (ltof state measure) ss
     (State s f sp0 (Mgetstack ofs ty dst :: c) stkr rs)
     (State s f sp0 c stkr rs') tm sp tp ptr chunk v.
Proof.
  intros.
  inv MS.
  assert (FSS := framesize_small2 _ WTF).
  destruct (load_ptr (Asm.chunk_of_ty ty) tm (sp0 + ofs)) as [v'|] _eqn : L.
    (* Load success *)
    destruct (frame_match_get_slot _ FM L) 
      as [GS | [v'' (GS & LD')]]; pose proof GS as GS'; 
        unfold get_slot in GS; destruct slot_valid_dec as [SV | SNV]; try done.
      (* Get slot failure *)
      left. left. (* ... then Machabstr must be stuck: *)
      intros s' l ST'; inv ST'.
      by unfold get_slot in GS0; destruct slot_valid_dec.
    (* Get slot success *)
    right. left.
    split. eby eapply chunk_inside_stkr.  
    split. eby eapply slot_chunk_not_inside_spart.
    rewrite L.
    split. done.
    intros L'; inv L'. left.
    eapply sim_wt_aux. done.
    eexists. split.
      apply step_taustep. simpl.
      eapply Machabstr.exec_Mgetstack. apply GS'.
    intro; econstructor; try edone; [].
    by apply regset_set.
  (* Load failure *)
  left. left. (* ... then Machabstr must be stuck: *)
  intros s' l ST'; inv ST'.
  by rewrite (frame_match_get_slot_none _ FM L) in GS.
Qed.

Lemma lessdef_val_of_eval:
  forall l l'
  (LD : Val.lessdef_list l l'),
  (l = l' /\ (exists el, map val_of_eval el = l)) \/
  forall el, map val_of_eval el <> l.
Proof.
  intros; induction LD. left; split; auto; by exists nil.
  destruct IHLD as [[-> [el E]] | N].
    destruct v1; try (by right; intros [|[]]).
    inv H. left. split. done. by exists (EVint i :: el). 
    inv H. left. split. done. by exists (EVfloat f :: el). 
  right. 
  intros el M. destruct el. done.
  simpl in M. inv M. eby eapply N. 
Qed.

Lemma extcall_args_inside:
  forall f stkr sg sp rs fr rs'
  (SRWF : valid_erange stkr) 
  (RI : range_inside (sp, total_framesize f) stkr)
  (WT : wt_function f)
  p c l vargs'
  (*MA : mem_arglist tm (map val_of_eval_memarg extmemargs) = Some vargs'*)
  (EA : extcall_arguments f.(fn_framesize) rs' fr sg vargs')
  (MVE : memarglist_from_sig rs sp sg = l)
  (IN : In (inl val (p, c)) l),
    range_inside (range_of_chunk p c) (sp, Int.repr f.(fn_framesize)).
Proof.
  intros until p; revert p.
  unfold memarglist_from_sig, extcall_arguments, Conventions.loc_parameters, extcall_args.
  remember (Conventions.loc_arguments sg) as args; clear Heqargs sg.
  induction args as [|a args IH]; intros;
    destruct l as [|ea eas]; simpl in MVE; try done.
  injection MVE; intros ME1 ME2.
  simpl in EA. destruct (extcall_arg f.(fn_framesize) rs' fr a) as [] _eqn :EAa; [|done]. simpl in EA.
  destruct (Coqlib.map_olist (extcall_arg f.(fn_framesize) rs' fr) args) as [vargs''|]; [|done].
  simpl in EA. inv EA.
  simpl in IN. destruct IN as [E | IN]; [|eby eapply IH].
  destruct a as [|[]]; try done.
  unfold extcall_arg, get_slot in EAa.
  destruct slot_valid_dec as [SV |]; [|done].
  simpl in E. inv E.
  eby eapply slot_valid_inside.
Qed.

Lemma extcall_args_inside_base:
  forall sz stkr sg sp rs fr rs'
  (SRWF : valid_erange stkr) 
  (RI : range_inside (sp, Int.repr sz) stkr)
  (Lsz: 0 <= sz)
  (Hsz: sz + 4 < half_modulus)
  p c extmemargs vargs'
  (*MA : mem_arglist tm (map val_of_eval_memarg extmemargs) = Some vargs'*)
  (EA : extcall_arguments sz rs' fr sg vargs')
  (MVE : memarglist_from_sig rs sp sg =
         map val_of_eval_memarg extmemargs)
  (IN : In (inl eventval (p, c)) extmemargs),
    range_inside (range_of_chunk p c) (sp, Int.repr sz).
Proof.
  intros until p; revert p.
  unfold memarglist_from_sig, extcall_arguments, Conventions.loc_parameters, extcall_args.
  remember (Conventions.loc_arguments sg) as args; clear Heqargs sg.
  induction args as [|a args IH]; intros; 
    destruct extmemargs as [|ea eas]; simpl in MVE; try done.
  injection MVE; intros ME1 ME2.
  simpl in EA. destruct (extcall_arg sz rs' fr a) as [] _eqn :EAa; [|done]. simpl in EA.
  destruct (Coqlib.map_olist (extcall_arg sz rs' fr) args) as [vargs''|]; [|done].
  simpl in EA. inv EA.
  simpl in IN. destruct IN as [-> | IN]; [|eby eapply IH].
  destruct a as [|[]]; try done.
  unfold extcall_arg, get_slot in EAa.
  destruct slot_valid_dec as [SV |]; [|done].
  eby inv ME2; eapply slot_valid_inside_base.
Qed.

Lemma start_sim:
  forall fn args s f sp0 c stkr rs tp tm ss sp
  (MAS: memarglist_from_sig rs sp0 thread_create_sig = fn :: args)
  (MS : match_state (State s f sp0 (Mthreadcreate :: c) stkr rs) tp tm ss sp),
   startmem_simulation Machabstr.state state (ma_step ge) match_state ss
     (State s f sp0 c stkr rs) tm sp tp fn args.
Proof.
  intros. 
  inv MS. 
  destruct (frame_match_ext_mem_arg_list (fn_framesize f0) FM REGS MAS)
    as [[vargs [vargs' (MA & EA & LD)]] | FAIL].
    (* Successfully obtained the arguments *)
    destruct args as [|arg []]; try done.
    pose proof MA as MA'. unfold mem_arglist in MA'. simpl in MA'.
    destruct (mem_arg tm fn) as [fnc|] _eqn:Efnc; [|done]; simpl in MA'.
    destruct (mem_arg tm arg) as [argc|] _eqn:Eargc; [|done]; simpl in MA'.
    inv MA'. destruct vargs as [|fn' args']; inversion LD as [|? ? ? ? LDfn LDargs]; subst.
    inversion LDargs as [|arg' ? ? ? LDarg X]; subst. inv X.
    assert (P: (exists pfn', fn' = Vptr pfn') \/ forall pfn', fn' <> Vptr pfn').
      destruct fn'; try (by right). left. eby eexists.
    destruct P as [[pfn' ->] | NP].
      inv LDfn. 
      right. exists (Vptr pfn' :: argc :: nil). exists pfn'. exists (arg' :: nil).
      split.
        intros p' c' IN.
        pose proof (stacksize_small _ WTF).
        assert(RI1: range_inside (range_of_chunk p' c') 
                                 (sp0, Int.repr f0.(fn_framesize))).
          eby eapply extcall_args_inside.
        split. (* Chunk inside the target region *)
          simpl. destruct range_inside_dec. done. 
          elim n. eapply range_inside_trans. edone.
          eapply range_inside_trans. eby eapply frame_inside_tframe. edone.
        (* but outside the Machabstr stack region... *)
        replace (Int.repr (fe_retaddrsize + f0.(fn_framesize))) with
                (Int.add rasize (Int.repr f0.(fn_framesize)))
          by (by rewrite <- (unsigned_repr_ra_plus_fs _ WTF), Int.repr_unsigned).
        eby eapply chunk_not_inside_spart.
      split. done.
      split. by vauto.
      eapply sim_wt_aux. done.
        eexists. split.
        apply step_taustep. simpl. 
        by eapply Machabstr.exec_Mthreadcreate.
      intro WS.
      by econstructor; vauto.
    left; left; intros s' l ST'; inv ST'; clarify'.
    unfold extcall_arguments in *. rewrite EA in ARG. inv ARG. 
    eby eapply NP.
  left; left; intros s' l ST'; inv ST'; clarify'.
  unfold extcall_arguments in *. by rewrite FAIL in ARG. 
Qed.

Lemma extcall_sim:
  forall fb ef rs sp0 memargs extmemargs s stkr tp tm ss sp
    (FF:  Genv.find_funct_ptr ge fb = Some (External ef))
    (MAL: memarglist_from_sig rs (sp0 + rasize) (ef_sig ef) = memargs)
    (MVE: map val_of_eval_memarg extmemargs = memargs)
    (MS:  match_state (Callstate s fb sp0 stkr rs) tp tm ss sp),
     extcallmem_simulation Machabstr.state state (ma_step ge) match_state ss
       (Blockedstate s sp0 stkr rs (ef_sig ef)) tm sp tp 
       (ef_id ef) extmemargs.
Proof.
  intros. 
  inv MS. rewrite FIND in FF; inv FF.
  inv STACKS.
    (* Reading from base frame *)
    apply sym_eq in MVE.
    destruct (frame_match_ext_mem_arg_list sz FM REGS MVE)
      as [[vargs [vargs' (MA & EA & LD)]] | FAIL].
      (* Successfully obtained the arguments *)
      destruct (lessdef_val_of_eval _ _ LD) as [[-> [el E]] | F].
        (* The arguments have no undefs => they can go external *)
        right. exists vargs'. exists el.
        split.
          intros p c IN.
          assert (RIsp4: range_inside ((sp0 + rasize)%pointer, Int.repr sz) stkr).
            eapply range_inside_trans, RI. 
            eapply range_inside_subrange. ri_res.
            unfold fe_retaddrsize; rewrite (unsigned_4sz sz), unsigned_4, (unsigned_sz sz); 
              try done; omega.
          assert (RI1: range_inside (range_of_chunk p c) (Ptr.add sp0 rasize, Int.repr sz)).
            eby eapply extcall_args_inside_base.
          split. 
            simpl. destruct range_inside_dec. done. 
            elim n. by eapply range_inside_trans, RIsp4. 
          done.
        repeat (split; [done|]).
        eapply sim_wt_aux. done.
          eexists. split.
          apply step_taustep. simpl. 
          eby eapply Machabstr.exec_function_external_call.
        intro WS.
        by econstructor; vauto.
      (* The arguments have some undef in them. *)
      left; left; intros s' l ST'; inv ST'; clarify'.
      unfold extcall_arguments in *. simpl in EARG. 
      rewrite EA in EARG; clarify. eby eapply F.
    (* Failed to obtain the arguments. *)
    left; left; intros s' l ST'; inv ST'; clarify'.
    unfold extcall_arguments in *. simpl in EARG. 
    rewrite FAIL in EARG; clarify.
  (* Reading from a function frame *)
  apply sym_eq in MVE.
  destruct (frame_match_ext_mem_arg_list (fn_framesize f) FM REGS MVE)
    as [[vargs [vargs' (MA & EA & LD)]] | FAIL].
    (* Successfully obtained the arguments *)
    destruct (lessdef_val_of_eval _ _ LD) as [[-> [el E]] | F].
      (* The arguments have no undefs => they can go external *)
      right. exists vargs'. exists el.
      split.
        intros p' c' IN.
        pose proof (stacksize_small _ WTF0).
        assert (RIpo: range_inside ((sp0 + rasize)%pointer, Int.repr (fn_framesize f))
                                   (sp0, parent_offset f)).
          eapply range_inside_subrange. ri_res.
          rewrite (unsigned_parent_offset _ WTF0), (unsigned_fsize _ WTF0), 
            unsigned_rasize; omega.
        assert(RIf: range_inside ((sp0 + rasize)%pointer, Int.repr (fn_framesize f)) stkr).
          by eapply range_inside_trans, RI.
        assert(RI1: range_inside (range_of_chunk p' c') 
                                 (Ptr.add sp0 rasize, Int.repr f.(fn_framesize))).
          eapply extcall_args_inside_base; try edone.
          by inv WTF0; omega.
          by inv WTF0; unfold fe_retaddrsize in *; omega.
        split. (* Chunk inside the target region *)
          simpl. destruct range_inside_dec. done. 
          elim n. by eapply range_inside_trans, RIf.
        (* but outside the Machabstr stack region... *)
        replace (Int.repr (fe_retaddrsize + f.(fn_framesize))) with
                (Int.add rasize (Int.repr f.(fn_framesize)))
          by (by rewrite <- (unsigned_repr_ra_plus_fs _ WTF0), Int.repr_unsigned).
        rewrite <- Ptr.add_add_l.
        eapply chunk_not_inside_spart; try edone.
          eapply range_inside_trans, RI.
          eapply range_inside_subrange. ri_res.
          rewrite (unsigned_parent_offset _ WTF0), (unsigned_total_fsize _ WTF0), 
            unsigned_rasize; omega.
          rewrite Ptr.add_add_l.
          replace (Int.add rasize (total_framesize f)) with
            (parent_offset f). edone.
          unfold parent_offset, Int.add. 
          rewrite (unsigned_total_fsize _ WTF0), unsigned_rasize.
          f_equal. omega.
      repeat (split; [done|]).
      eapply sim_wt_aux. done.
        eexists. split.
        apply step_taustep. simpl. 
        eby eapply Machabstr.exec_function_external_call.
      intro WS.
      by econstructor; vauto.
    (* The arguments have some undef in them. *)
    left; left; intros s' l ST'; inv ST'; clarify'.
    unfold extcall_arguments in *. simpl in EARG. 
    rewrite EA in EARG; clarify. eby eapply F.
  (* Failed to obtain the arguments. *)
  left; left; intros s' l ST'; inv ST'; clarify'.
  unfold extcall_arguments in *. simpl in EARG. 
  rewrite FAIL in EARG; clarify.
Qed.
 

Lemma loctype_eq:
  forall sg,
    map Locations.Loc.type (Conventions.loc_arguments sg) = (sig_args sg).
Proof.
  intro. unfold Conventions.loc_arguments.
  remember 0 as z; clear Heqz; revert z.
  by induction (sig_args sg) as [|[] l IH]; intros; 
    try done; simpl; rewrite IH.
Qed. 


Lemma has_type_list_lessdef:
  forall vs' vs tys 
    (LD: Val.lessdef_list vs' vs)
    (HT: Val.has_type_list vs tys),
      Val.has_type_list vs' tys.
Proof.
  induction vs'; intros; simpl; inv LD; destruct tys; try done.
  simpl in HT.
  apply <- andb_true_iff. apply andb_true_iff in HT.
  destruct HT. split. eby eapply Val.has_type_lessdef.
  eby eapply IHvs'. 
Qed.

Lemma type_list_build_frame:
  forall sig vs
   (WT : Val.has_type_list vs sig.(sig_args)),
   wt_frame
     (build_frame_rec (Conventions.loc_arguments sig) vs empty_frame).
Proof.
  intros sig vs.
  unfold Conventions.loc_arguments in *; remember 0 as z1; clear Heqz1.
  remember (sig_args sig) as sa; clear Heqsa sig.
  assert (WTef: wt_frame empty_frame) by done.
  remember empty_frame as ef; clear Heqef.
  revert z1 sa ef (* BND *) (* ACC NR *) WTef.
  induction vs; intros; intros ty ofs; destruct sa as [|[] sa]; try done;
    simpl in WT |- *; apply andb_true_iff in WT; destruct WT as [WT WT']; 
      eapply IHvs; try done;
        intros ty' ofs'; unfold update; 
          (destruct zeq; [destruct typ_eq as [<-|] | 
                          repeat destruct zle]); auto.
Qed.

Ltac int_mod_tac :=
  unfold Int.max_unsigned, fe_retaddrsize in *; pose proof Int.half_modulus_pos; rewrite ?Int.half_modulus_modulus in *; omega.

Opaque Zmult.


Lemma wt_stackframes_bnd_sz:
  forall {fs vs}
    (WTS: wt_stackframes
           (Stackbase (build_frame fs vs) (4 * Conventions.size_arguments fs))),
    0 <= 4 * Conventions.size_arguments fs + fe_retaddrsize < half_modulus.
Proof. intros. by inv WTS. Qed.

Lemma wt_stackframes_bnd_sz2:
  forall {fs vs}
    (WTS: wt_stackframes
           (Stackbase (build_frame fs vs) (4 * Conventions.size_arguments fs))),
    0 <= 4 * Conventions.size_arguments fs + fe_retaddrsize < modulus.
Proof. intros. inv WTS. int_mod_tac. Qed.

Lemma wt_stackframes_eq_sz:
  forall {fs vs}
    (WTS: wt_stackframes
           (Stackbase (build_frame fs vs) (4 * Conventions.size_arguments fs))),
    Int.unsigned (Int.repr (4 * Conventions.size_arguments fs + fe_retaddrsize)) =
    4 * Conventions.size_arguments fs + fe_retaddrsize.
Proof.
  intros. pose proof (wt_stackframes_bnd_sz WTS).
  unfold fe_retaddrsize in *.
  rewrite Int.unsigned_repr. omega.
  split. omega.
  eapply Zle_trans with half_modulus; int_mod_tac.
Qed.

Lemma wt_stackframes_eq_arg_sz:
  forall {fs vs}
    (WTS: wt_stackframes
           (Stackbase (build_frame fs vs) (4 * Conventions.size_arguments fs))),
    Int.unsigned (Int.repr (4 * Conventions.size_arguments fs)) =
    4 * Conventions.size_arguments fs.
Proof.
  intros. pose proof (wt_stackframes_bnd_sz WTS).
  unfold fe_retaddrsize in *.
  rewrite Int.unsigned_repr. omega.
  split. pose proof (Conventions.size_arguments_above fs); omega.
  eapply Zle_trans with half_modulus; int_mod_tac.
Qed.

Lemma initalloc_sim:
  forall ss tm sp tp pfn args fn stkp size sp0
  (FF : Genv.find_funct_ptr ge pfn = Some fn)
  (Esz : size = 4 * Conventions.size_arguments (funsig fn))
  (SZ : size + 15 + fe_retaddrsize <= thread_stack_size)
  (Esp : sp0 = Asm.align_stack (stkp + Int.repr (thread_stack_size - size)))
  (MS : match_state (Initstate pfn args) tp tm ss sp),
   alloc_simulation Machabstr.state state (ma_step ge) match_state
     (ltof state measure) ss (Initstate pfn args)
     (Initargsstate pfn args (Conventions.loc_parameters (funsig fn))
        (Ptr.sub_int sp0 rasize) (stkp, Int.repr thread_stack_size)
        (Regmap.init Vundef)) tm sp tp stkp (Int.repr thread_stack_size)
     MObjStack.
Proof.
  intros; right; right. (* Stutter *)
  split; [|done]. (* Measure decreases *)
  inv MS. rewrite FF in FIND; inv FIND.
  replace vs with (nil ++ vs) by done.
  destruct (alloc_someD A) as (_ & VAR & _).
  replace (4 * Conventions.size_arguments (funsig f) + 15 + fe_retaddrsize) with 
            (4 * Conventions.size_arguments (funsig f) + fe_retaddrsize + 15) in SZ by omega.
  pose proof (aligned_stack_inside _ _ 
    (Conventions.size_arguments_above (funsig f)) VAR SZ) as RI.
  pose proof (stkr_valid_erange _ VAR) as VE.
  pose proof (Conventions.size_arguments_above (funsig f)) as SApos. inversion WTS; subst.
  pose proof (wt_stackframes_bnd_sz H2) as (_ & BND).
  pose proof (wt_stackframes_eq_sz H2) as Eusra.
  pose proof (wt_stackframes_eq_arg_sz H2) as Eusa.
  rewrite Zplus_comm in Eusra at 2.
  eapply match_states_initargsstate.
  - edone.
  - rewrite <- (Val.lessdef_list_length LD), <- Els.
    unfold Conventions.loc_parameters, Conventions.loc_arguments.
    remember 0 as z. clear Els WT Heqz SApos. revert z.
    by induction (sig_args (funsig f)) as [|[] l IH]; intros; try done;
      simpl; rewrite IH.
  - by instantiate (1 := nil).
  - done.
  - by rewrite loctype_eq.
  - done.
  - done.
  - by rewrite Zplus_comm. 
  - done.
  - by apply stkr_valid_erange. 
  - unfold build_frame_rec. constructor.
      remember (Asm.align_stack (stkp + Int.repr
           (thread_stack_size - 4 * Conventions.size_arguments (funsig f)))) as p.  
      assert(RI': range_inside (p, Int.repr (4 * Conventions.size_arguments (funsig f)))
                 (stkp, Int.repr thread_stack_size)).
        eapply range_inside_trans, RI.
        assert (Ep: p = Ptr.add (Ptr.sub_int p (Int.repr 4)) (Int.repr 4)).
          by rewrite <- Ptr.add_sub_r, Int.sub_idem, Ptr.add_zero_r.
        rewrite Ep at 1; clear Ep.
        apply range_inside_subrange. ri_res.
        rewrite Eusra, unsigned_4, Eusa.
        by unfold fe_retaddrsize; omega.
      pose proof (range_inside_valide _ _ RI' VE) as VE'.
      rewrite <- Ptr.add_sub_r, Int.sub_idem, Ptr.add_zero_r.
      destruct p; apply valid_erange_modulus in VE'. by rewrite <- Eusa.
    intros ty ofs SV. 
    eexists. 
    rewrite (load_alloc_inside A). split. edone. by constructor.
      eapply range_inside_trans, RI.
      rewrite <- Ptr.add_add_r.
      apply range_inside_subrange. ri_res.
      inv SV.
      rewrite Eusra, size_chunk_repr.
      pose proof (Int.unsigned_range (Int.repr (4 * Conventions.size_arguments (funsig f) + fe_retaddrsize))).  
      unfold fe_retaddrsize in *.
      assert (Eofs: Int.unsigned (Int.repr ofs) = ofs).
        rewrite Int.unsigned_repr. done.
        rewrite <- Eusa in HB. unfold Int.max_unsigned. unfold typesize in HB. destruct ty; omega.
      unfold Int.add. rewrite unsigned_4, Eofs, Int.unsigned_repr. 
        destruct ty; unfold typesize, size_chunk, chunk_of_type in *; omega. 
      rewrite Eusra in H. unfold Int.max_unsigned. split. omega. 
      destruct ty; unfold typesize in HB; omega.
    rewrite <- Ptr.add_sub_r, Int.sub_idem, Ptr.add_zero_r.
    eapply slot_aligned. apply align_stack_aligned. edone.
  - edone.
  - constructor.
    (* wt_stackframes *)      
    constructor. unfold fe_retaddrsize in *. omega.
    eby eapply type_list_build_frame, has_type_list_lessdef. 
    (* wt_fundef *)
    eapply wt_ge. by instantiate (1 := Vptr pfn). 
    (* wt_regset *)
    done.
  - intros p c PCA RI'. by rewrite (load_alloc_inside A).
  - apply align_stack_aligned2.
Qed.

Lemma build_frame_rec_app:
  forall l1 l2 v1 v2 f
  (El1: length l1 = length v1)
  (Al1: forall l, In l l1 -> Conventions.loc_argument_acceptable l),
  build_frame_rec (l1 ++ l2) (v1 ++ v2) f =
  build_frame_rec l2 v2 (build_frame_rec l1 v1 f).
Proof.
  induction l1 as [|lo l1 IH]; intros. by destruct v1.
  destruct v1 as [|v v1]; [done|]. inv El1.
  pose proof (Al1 _ (in_eq _ _)).
  by destruct lo as [|[]]; try done; 
    simpl; rewrite IH; auto; intros; apply Al1; right.
Qed.

Lemma initargmem_sim:
  forall ss tm sp tp pfn arg args ofs argp ty locs sp0 stkr rs
  (Eargp : argp = (sp0 + Int.repr (4 * ofs + fe_retaddrsize))%pointer)
  (MS : match_state
         (Initargsstate pfn (arg :: args)
            (Locations.S (Locations.Incoming ofs ty) :: locs) sp0 stkr rs) tp
         tm ss sp),
   write_simulation Machabstr.state state (ma_step ge) match_state
     (ltof state measure) ss
     (Initargsstate pfn (arg :: args)
        (Locations.S (Locations.Incoming ofs ty) :: locs) sp0 stkr rs)
     (Initargsstate pfn args locs sp0 stkr rs) tm sp tp argp
     (chunk_of_type ty) arg.
Proof.
  intros.
  inv MS. inversion LD as [|v v' vrest vrest' LDv LDr]; subst.
  inversion WTS; subst.
  pose proof (wt_stackframes_bnd_sz H3) as (_ & BND).
  pose proof (wt_stackframes_bnd_sz2 H3) as BND2.
  pose proof (wt_stackframes_eq_sz H3) as Eusra.
  pose proof (wt_stackframes_eq_arg_sz H3) as Eusa.
  destruct locs2 as [|l locs2]; [done|].
  inv H2. simpl in WT. apply andb_true_iff in WT. destruct WT as [WTa WTr].
  pose proof (Val.has_type_lessdef _ _ _ LDv WTa) as WTv.
  pose proof (Conventions.loc_arguments_acceptable (funsig f)) as LA.
  pose proof (Conventions.loc_arguments_bounded (funsig f)) as BA.
  rewrite SG in LA, BA.
  assert (IN: In l (locs1 ++ l :: locs2)).
    eby apply in_or_app; right; left. 
  destruct l as [|[]]; pose proof (LA _ IN) as LAl; try done; simpl in LAl.
  pose proof (BA _ _ IN) as BAl. inv H0. simpl in WTa, WTv.
  assert (SV :  slot_valid (4 * Conventions.size_arguments (funsig f)) ty
   (Int.signed (Int.repr (4 * ofs)))).
      rewrite Int.signed_repr.
        constructor. omega.
        destruct ty; simpl in BAl |- *; omega.
        apply Zdivide_factor_r.
      split. pose proof Int.min_signed_neg; omega.
      unfold Int.max_signed; destruct ty; simpl in BAl; int_mod_tac.
  exploit frame_match_store_stack. 2 : edone.
  - pose proof (Conventions.size_arguments_above (funsig f)); int_mod_tac.
  - edone.
  - apply WTa.
  - edone.
  intros [tm' (S & FM')]. 
  right. left.
  assert (RI1: range_inside (Ptr.add sp0 rasize, 
                             Int.repr (4 * Conventions.size_arguments (funsig f)))     
                            stkr).
    eapply range_inside_trans, RI.
    eapply range_inside_subrange. ri_res.
    rewrite Eusa. rewrite Zplus_comm. rewrite unsigned_rasize, <-Eusra, Zplus_comm. omega.
  exploit @slot_valid_inside_base; [edone|apply RI1| | |apply SV|].
  - pose proof (Conventions.size_arguments_above (funsig f)); omega.
  - done.
  intro RIchunk.
  
  split.
    simpl. destruct range_inside_dec as [|n]; try done; elim n.
    rewrite Zplus_comm, repr_plus, Ptr.add_add_r.
    eby eapply range_inside_trans. 
  split. done.  
  exists tm'. split. 
    unfold store_stack in S. 
    eby rewrite Zplus_comm, repr_plus, Ptr.add_add_r. 
  right.
  split. 
  replace (vs1 ++ v :: vrest) with ((vs1 ++ v :: nil) ++ vrest)
    by (by rewrite app_ass).
  econstructor; try done.
  - by inv El2.
  - instantiate (1 := locs1 ++ Locations.S (Locations.Outgoing ofs ty) :: nil).
    by rewrite !app_length, El1.
  - by rewrite app_ass.
  - rewrite build_frame_rec_app. simpl.
        rewrite Int.signed_repr in FM'. done.
        split. pose proof Int.min_signed_neg; omega.
        unfold Int.max_signed; destruct ty; simpl in BAl; int_mod_tac.
      done.
    intros. apply LA. by apply in_or_app; left.
  - by rewrite app_ass.
  - eby eapply load_stkr_valid_store.
  - done.
Qed.

Lemma initargreg_sim:
  forall ss tm sp tp pfn arg args r locs sp0 stkr rs
  (MS : match_state
         (Initargsstate pfn (arg :: args) (Locations.R r :: locs) sp0 stkr rs)
         tp tm ss sp),
   tau_simulation Machabstr.state state (ma_step ge) match_state
     (ltof state measure) ss
     (Initargsstate pfn (arg :: args) (Locations.R r :: locs) sp0 stkr rs)
     (Initargsstate pfn args locs sp0 stkr (Regmap.set r arg rs)) tm sp tp.
Proof.
  intros.
  inv MS. inversion LD as [|v v' vrest vrest' LDv LDr]; subst.
  destruct locs2 as [|[|[]] locs2]; inv H2; try done; [].
  (* Make it x86 specific: arguments only come in memory.
     For the general case we would need to update the simulation relation
     (and Machconcr initialisation). *)
  byContradiction.
  assert (NR: forall fs, In (Locations.R r) (Conventions.loc_arguments fs) -> False).
    intro; unfold Conventions.loc_arguments. 
    remember 0 as z; clear Heqz; revert z.
    by induction (sig_args fs) as [|[] fsr IH]; intro; try done;
      simpl; (intros [|]; [done| eauto]).
  eapply (NR (funsig f)). 
  rewrite SG. apply in_or_app; right. by left.
Qed.

(** The main simulation theorem. *)
Theorem mc_ma_perthread_sim:
  local_intro_simulation Machabstr.state  Machconcr.state 
                         (ma_step ge)     (mc_step ge)
                         match_state      (ltof _ measure).
Proof.
  intros ss ts ts' tm sp tp l STEP MS.

  (mc_step_cases (destruct STEP) Case).
  
  Case "exec_Initalloc".
    eby eapply initalloc_sim.

  Case "exec_Initalloc_oom".
    (* Out of memory is trivial *)
    done.

  Case "exec_Initargmem".
    eby eapply initargmem_sim. 
 
  Case "exec_Initargreg".
    eby eapply initargreg_sim.

  Case "exec_Initretaddr".
    eby eapply initretaddr_sim.
    
  Case "exec_Mlabel".
    inv MS.
    right. left. (* tau step *)
    eapply sim_wt_aux. done.
    eexists; split.
      apply step_taustep. simpl.
      eapply Machabstr.exec_Mlabel.
    eby intro; eapply match_states_normal.
    
  Case "exec_Mgetstack".
    eby eapply mgetstack_sim.

  Case "exec_Msetstack".
    eby eapply msetstack_sim.

  Case "exec_Mgetparam".      
    eby eapply mgetparam_sim.

  Case "exec_Mop".
    inv MS.
    assert (Espo: spo = None \/ spo = Some sp0) by tauto.
    destruct (eval_operation_disj EVAL Espo REGS) as [(? & EVAL' & LDEF')|EVAL'].
    - right. left. (* Success *)
      apply sim_wt_aux. done.
      eexists. split.
        apply step_taustep. simpl. eby apply Machabstr.exec_Mop.
      econstructor; try edone.
      eauto using regset_set, regset_lessdef_undef_op.
    - left. left. (* Fail => we are stuck *)
      intros s' l ST'; inv ST'. clarify'.

  Case "exec_Mload".
    inv MS.
    assert (Espo: spo = None \/ spo = Some sp0) by tauto.
    destruct (eval_addressing_disj EVAL Espo REGS) as [(? & EVAL' & LDEF')|EVAL'];
      [inv LDEF'|]; try (by left; left; intros s' l ST'; inv ST'; clarify').
    right. right. (* Success *)
    intros v' LD.
    apply sim_wt_aux. done.
    eexists. split.
      apply step_taustep. simpl. 
      by eapply Machabstr.exec_Mload; eauto using Val.has_type_lessdef.
    econstructor; try edone.
    eauto using regset_set, regset_lessdef_undef_temps.

  Case "exec_Mstore".
    inv MS.
    assert (Espo: spo = None \/ spo = Some sp0) by tauto.
    destruct (eval_addressing_disj EVAL Espo REGS) as [(? & EVAL' & LDEF')|EVAL'];
      [inv LDEF'|]; try (by left; left; intros s' l ST'; inv ST'; clarify').
    right. right. (* Success *)
    eexists. split. apply cast_value_to_chunk_lessdef, Val.conv_lessdef. apply (REGS src).
    apply sim_wt_aux. done.
    eexists. split.
      apply step_taustep. simpl. 
      by eapply Machabstr.exec_Mstore; eauto. 
    econstructor; try edone.
    eauto using regset_set, regset_lessdef_undef_temps.

  Case "exec_Mcall".
    subst. eby eapply mcall_sim.

  Case "exec_Mcall_oom".    
    done.
  
  Case "exec_Mgoto".
    inv MS. rewrite GFF in GETF. inv GETF.
    right. left.
    apply sim_wt_aux. done.
    eexists. split.
      apply step_taustep. simpl. 
      by eapply Machabstr.exec_Mgoto; eauto. 
    eby econstructor. 

  Case "exec_Mcond_true".
    inv MS. rewrite GETF in H0. inv H0.
    eapply Op.eval_condition_lessdef3 in H; 
      [|eby eapply regset_get_list]; destruct H.
      left; left; intros s' l ST'; inv ST'; clarify'.
    right. left.
    apply sim_wt_aux. done.
    eexists. split.
      apply step_taustep. simpl. 
      eby eapply Machabstr.exec_Mcond_true; eauto. 
    intro; econstructor; try edone.
    by apply regset_lessdef_undef_temps.

  Case "exec_Mcond_false".
    inv MS.
    eapply Op.eval_condition_lessdef3 in H; 
      [|eby eapply regset_get_list]; destruct H.
      left; left; intros s' l ST'; inv ST'; clarify'.
    right. left.
    apply sim_wt_aux. done.
    eexists. split.
      apply step_taustep. simpl. 
      eby eapply Machabstr.exec_Mcond_false; eauto. 
    intro; econstructor; try edone.
    by apply regset_lessdef_undef_temps.

  Case "exec_Mreturn".
    inv MS. rewrite GETF in GFF; inv GFF.
    destruct SPM as [[Z ->] | [NZ ->]].
      (* Machabstr frame is empty => do tau transition *)
      right; left.
      apply sim_wt_aux. done.
      eexists. split.
        apply step_taustep. simpl. 
        eby eapply Machabstr.exec_Mreturn; eauto.
      intro. econstructor; try edone.
      by destruct Int.eq_dec.
      (* Alignment *)
      eby eapply align_mreturn. 
    (* Machabstr frame non-empty - we need to free in Machabstr. *)
    right. right. right. right.
    eexists. eexists. eexists.
    split. 
      destruct Int.eq_dec; [done|].
      reflexivity.
    eapply sim_wt_aux. done.
    eexists. split.
      apply step_taustep. simpl. 
      eby eapply Machabstr.exec_Mreturn; eauto. 
    intro; econstructor; try edone.
    eby eapply align_mreturn. 
   
  Case "exec_Mthreadcreate".
    eby eapply start_sim.    

  Case "exec_Matomic".
    inv MS.
    assert (LDa := regset_get_list _ _ args REGS).
    assert (E: exists p', exists instr', lab = MErmw p' Mint32 v instr').
      destruct lab; inv ASME; eexists; eexists; eexists; edone.
    destruct E as [p' [instr' ->]].
    unfold rmw_simulation.
    destruct (atomic_statement_disj _ _ _ _ _ _ _ ASME LDa) as
      [(ASME' & E) | ASMEF].
      right. intros v' LDv'.
      pose proof (Op.atomic_statement_lessdef_res ASME' LDv') as ASME''.
      eapply sim_wt_aux. done.
      eexists. split.
        apply step_taustep. simpl. 
        eapply Machabstr.exec_Matomic; try edone. 
        eby eapply Val.has_type_lessdef.
      intro; econstructor; try edone.
      eauto using regset_set, regset_lessdef_undef_temps.
    left; left; intros s' l ST'; inv ST'; clarify'.
    destruct lab; try (by inv ASME0).
    eby eapply ASMEF.

  Case "exec_Mfence".
    inv MS.
    right.
    eapply sim_wt_aux. done.
    eexists. split.
      apply step_taustep. simpl. 
      eby eapply Machabstr.exec_Mfence; eauto. 
    eby intro; econstructor.
  
  Case "exec_function_internal".
    eby eapply function_internal_sim.
     
  Case "exec_function_internal_oom".
    done.
  
  Case "exec_function_external_call".
    eby eapply extcall_sim.

  Case "exec_function_external_return".
    inv MS.
    right.
    eapply sim_wt_aux. done.
    eexists. split.
      apply step_taustep. simpl. 
      eby eapply Machabstr.exec_function_external_return; eauto. 
    intro; econstructor; try edone.
    eapply regset_set. done.
    constructor.

  Case "exec_return".
    eby eapply return_sim.
     
  Case "exec_return_exit_read_ra".
    eby eapply return_exit_sim.

  Case "exec_return_fail".
    eby eapply return_fail_sim.

  Case "exec_exit_free".
    inv MS.
    right.
    exists n. exists nil. split. done.
    intros tm' F.
    split. done.
    right. split. constructor. done.

  Case "exec_exit".
    inv MS. right.
    eexists. split.
      apply step_taustep. simpl. 
      eby eapply Machabstr.exec_return_exit; eauto.
    done.
Qed.

(** Auxiliary lemmas for non-interference of changing non-local memory. *)
Lemma frame_match_agrees:
  forall sz fr sp tm tm'
  (SM: 0 <= sz < modulus)
  (VE: valid_erange (sp, Int.repr sz))
  (AG: forall p c, range_inside (range_of_chunk p c) (sp, Int.repr sz) ->
    match load_ptr c tm p, load_ptr c tm' p with
      | Some sv, Some tv => sv = tv 
      | None, None => True
      | _, _ => False
    end)
  (FM: frame_match sz fr sp tm),
    frame_match sz fr sp tm'.
Proof.
  intros. inv FM.
  constructor. done.
  intros ty ofs SV. destruct (LDREL ty ofs SV) as [v (L & LD)].
  eexists; split; [|edone].
  exploit AG. 
    eby eapply lb_hb_range_inside.
  rewrite L; clear L.
  destruct load_ptr; try done. by intros <-.
Qed.

Lemma range_not_in_inside:
  forall r r' l,
    range_not_in r l ->
    range_inside r' r ->
    range_not_in r' l.
Proof.
  intros r r' l RNI RI r'' IN.
  eapply disjoint_inside_disjoint_l, RI.
  auto.
Qed.

Lemma range_not_in_app:
  forall r l l',
    range_not_in r l ->
    range_not_in r l' ->
    range_not_in r (l ++ l').
Proof.
  intros r l l' RNI RNI' r' IN.
  apply in_app_or in IN.
  destruct IN; auto.
Qed.

(** Non-interference for matchin stacks. *)
Lemma match_stack_agrees:
  forall sp tm tm' ts ss stkr spart spp
  (VE: valid_erange stkr)
  (AG: mem_agrees_on_local tm tm' (stkr::nil) (spp ++ spart))
  (SD: range_not_in (range_sp stkr sp) spp)
  (MS: match_stacks stkr sp tm spart ts ss),
    match_stacks stkr sp tm' spart ts ss.
Proof.
  intros. revert spp AG SD.
  induction MS; intros.
  (* Base case *)
  assert (RIr: range_inside (range_of_chunk sp Mint32) stkr).
    eapply range_inside_trans, RI.
    eapply ra_inside_ret_exit; try edone. ri_res.
    apply range_inside_refl.
  eapply match_stacks_nil; try edone.
    (* load of return address *)
    specialize (AG sp Mint32).
    exploit AG. 
      simpl. by destruct range_inside_dec.
    rewrite RA. 
    destruct (load_ptr Mint32 tm' sp); [|done].
    intro E; rewrite <- E. done.
    subst; rewrite <- app_nil_end.
    by eapply range_not_in_inside, range_inside_range_sp2; eauto. 
  (* frame_match *)
  assert (RIf: range_inside ((sp + rasize)%pointer, Int.repr sz)
                            (sp, Int.add rasize (Int.repr sz))).
    eapply range_inside_subrange. ri_res.
    rewrite unsigned_4sz, unsigned_rasize4, unsigned_sz; try done; omega.
  eapply frame_match_agrees; try (apply FM).
      split. done. 
      eapply Zlt_trans with half_modulus. 
        by unfold fe_retaddrsize in *; omega. int_mod_tac.
      eapply range_inside_valide; [|edone]; ri_res.
    intros p c RI'. specialize (AG p c).
    exploit AG. simpl. destruct range_inside_dec; try done.
    elim n. ri_res. 
    destruct (load_ptr c tm p); destruct (load_ptr c tm' p); try done.
    intro E; apply E. 
    subst; rewrite <- app_nil_end. 
    eapply range_not_in_inside; ri_res. 
  (* Step case *)
  econstructor; try edone.
  (* frame matching *)
  eapply frame_match_agrees; try (apply FM).
    eby eapply framesize_small2.
    eapply range_inside_valide, VE.
    eapply range_inside_trans; ri_res.
    intros p' c' RI'. specialize (AG p' c').
    exploit AG. simpl. destruct range_inside_dec; try done.
    elim n. eapply range_inside_trans, RI.
    eapply range_inside_trans. edone. ri_res.
    destruct (load_ptr c' tm p'); destruct (load_ptr c' tm' p'); try done.
    intro E; apply E. subst.
    replace (Int.repr (fe_retaddrsize + f.(fn_framesize))) with
            (Int.add rasize (Int.repr f.(fn_framesize)))
      by (by rewrite <- (unsigned_repr_ra_plus_fs _ WTF), Int.repr_unsigned).
    rewrite <- Ptr.add_add_l.
    apply range_not_in_app.
    eapply range_not_in_inside. edone.
    eapply range_inside_trans. edone.
    eapply range_inside_trans. eby eapply frame_inside_tframe.
    eapply range_inside_trans. eapply tframe_inside_po; ri_res.
    eby eapply range_inside_range_sp2.
    eapply chunk_not_inside_spart; try edone. ri_res.
    replace ((sp + rasize) + total_framesize f)%pointer with 
            (sp + parent_offset f)%pointer. edone.
    rewrite Ptr.add_add_l. 
    f_equal. unfold parent_offset, Int.add. f_equal.
    rewrite unsigned_total_fsize, unsigned_rasize; try done; omega.
  (* return address *)
  specialize (AG sp Mint32).
  exploit AG. 
    simpl. destruct range_inside_dec; try done.
    elim n. eapply range_inside_trans, RI.
    eapply ra_inside_ret; try edone. ri_res.
    apply range_inside_refl.
  rewrite LDra. 
  destruct (load_ptr Mint32 tm' sp); [|done].
  intro E; rewrite <- E. done. 
  apply range_not_in_app.
  eapply range_not_in_inside. edone.
  eapply range_inside_trans. 
    eapply ra_inside_ret, range_inside_refl; ri_res.
  eby eapply range_inside_range_sp2.
  subst; eapply return_range_not_in; try edone.
  (* IH *)
  specialize (IHMS (if Int.eq_dec (fn_stacksize f) Int.zero 
                    then spp else  spp ++ ((sp + Int.repr (fe_retaddrsize + 
                      fn_framesize f))%pointer, fn_stacksize f)::nil)).
  eapply IHMS. 
  - subst. destruct Int.eq_dec. done. by rewrite app_ass.
  - assert (RNI: range_not_in (range_sp stkr sp') spp). 
      eapply range_not_in_inside. edone.
      subst sp'. eby eapply  range_sp_inside_range_sp_add2.
    destruct Int.eq_dec. done.
    apply range_not_in_app. done.
    intros r IN. destruct IN as [<-|]; [|done].
    eapply disjoint_inside_disjoint_r with (sp, parent_offset f).
      subst sp'. 
      eapply ranges_disjoint_comm, ranges_disjoint_range_sp_add2; ri_res.
    eapply range_inside_trans; [|eapply tframe_inside_po; ri_res].
    rewrite repr_plus, <- Ptr.add_add_l.
    eapply range_inside_subrange. ri_res.
    rewrite unsigned_total_fsize, unsigned_fsize; try done.
    inv WTF. omega.
Qed.

Lemma mem_eq_preserves_stkr_valid:
  forall stkr tm tm' sp
  (MA:  mem_agrees_on_local tm tm' (stkr :: nil) sp)
  (LSV: load_stkr_valid stkr tm),
     load_stkr_valid stkr tm'.
Proof.
  intros.
  intros p c PCA RI.
  specialize (LSV p c PCA RI).
  exploit (MA p c). simpl. by destruct range_inside_dec; [|elim n].
  intros MA' L. rewrite L in MA'. by destruct (load_ptr c tm p).
Qed.

(** Non-interference theorem (preserving values of local variables 
    in memory preserves the simulation relation). *)
Theorem mem_eq_preserves_simrel:
  simulation_local_invariant Machabstr.state  Machconcr.state match_state. 
Proof.
  intros ts tp tm tm' ss sp MA MS.
  (match_state_cases (destruct MS) Case); 
  try (eby econstructor; try edone; first [
        eapply match_stack_agrees with (spp := nil) |
        eapply mem_eq_preserves_stkr_valid]).

  Case "match_states_normal".
    eapply match_states_normal with (spart' := spart'); try done; subst.
    - eapply frame_match_agrees with tm; try done. 
      by apply framesize_small2. ri_res.
      intros p' c' RI'.
      exploit (MA p' c').
        simpl. destruct range_inside_dec; [|elim n]; ri_res.
      intro MA'.
      destruct load_ptr; destruct load_ptr; try done.
      eby eapply MA', chunk_not_inside_spart.
      eby eapply mem_eq_preserves_stkr_valid.
      destruct Int.eq_dec; eapply match_stack_agrees; try edone.
          by instantiate (1 := nil). done.
        by instantiate (1 := 
          ((sp + Int.repr (fn_framesize f))%pointer, fn_stacksize f) :: nil).
      intros r' [IN'|IN']; [rewrite <- IN'|done].
      eapply ranges_disjoint_comm, disjoint_inside_disjoint_l.
        eby eapply ranges_disjoint_range_sp_add2.
      eapply range_inside_subrange. ri_res.
      rewrite unsigned_total_fsize, unsigned_fsize; try done; inv WTF; omega.

  Case "match_states_initargsstate".
    inversion WTS; subst; try done; inv H2.
    pose proof (wt_stackframes_bnd_sz2 H) as BND.
    pose proof (wt_stackframes_eq_sz H) as Eusra.
    pose proof (wt_stackframes_eq_arg_sz H) as Eusa.
    assert (RI2: range_inside ((sp + rasize)%pointer,
     Int.repr (4 * Conventions.size_arguments (funsig f))) stkr).
      eapply range_inside_trans, RI.
      eapply range_inside_subrange. ri_res.
      rewrite Zplus_comm in Eusra.
      by rewrite unsigned_rasize, Eusa, Eusra; omega.
    eapply match_states_initargsstate with (locs1 := locs1); subst; try done.
      eapply frame_match_agrees with tm; try done.
      - pose proof (Conventions.size_arguments_above (funsig f)); int_mod_tac.
      - eby eapply range_inside_valide, SRWF.
      - intros p' c' RI'.
        exploit (MA p' c').
          simpl. destruct range_inside_dec; [|elim n]; ri_res.
        intro MA'.
        destruct load_ptr; destruct load_ptr; try done.
        eby eapply MA'.
    eby eapply mem_eq_preserves_stkr_valid.
Qed.

Lemma find_function_find_function_ptr_bw:
  forall ros rs f',
  find_function ge ros rs = Some f' ->
  exists fb', Genv.find_funct_ptr ge fb' = Some f' /\ find_function_ptr ge ros rs = Some fb'.
Proof.
  intros until f'. destruct ros; simpl.
    by destruct (rs m); vauto.
  by destruct (Genv.find_symbol ge i); vauto.
Qed.

Lemma exists_ema:
  forall rs sp sig,
    exists ema,
      map val_of_eval_memarg ema =
      memarglist_from_sig rs sp sig.
Proof.
  intros.
  unfold memarglist_from_sig, Conventions.loc_parameters,
    Conventions.loc_arguments.
  destruct sig. simpl.
  generalize 0.
  induction sig_args; intros.
  (* Base case *)
  eby exists nil. 
  (* Step case *)
  destruct a. 
  simpl; destruct (IHsig_args (z + 1)) as [ema' E].
  rewrite <- E. 
  by exists (inl eventval (Ptr.add sp (Int.repr (4*z)), Mint32) :: ema').
  simpl; destruct (IHsig_args (z + 2)) as [ema' E].
  rewrite <- E. 
  by exists (inl eventval (Ptr.add sp (Int.repr (4*z)), Mfloat64) :: ema').
Qed.

Require Import Asmgenretaddr.

(** Stuckness simulation. *)
Lemma stuck_sim:
  forall t tp tm s sp l s'
  (MS: match_state t tp tm s sp)
  (ST: ma_step ge s l s'),
    exists t', exists l', mc_step ge t l' t'.
Proof.
  intros.
  (ma_step_cases (destruct ST) Case).

  Case "exec_Mlabel".
    by inv MS; eexists; eexists; vauto.

  Case "exec_Mgetstack".    
    inv MS.
    destruct (frame_match_get_slot_bw _ FM GS) as [v' (L & LD)].
    eexists. eexists.
    eapply exec_Mgetstack with (v := v'); try edone.
    unfold load_stack, load_ptr, load in L.
    destruct (Ptr.add sp1 ofs). destruct in_block; [|done].
    inv L.
    apply Val.load_result_wt.
 
  Case "exec_Msetstack".
    inv MS. eexists; eexists. 
    by eapply exec_Msetstack; try edone; apply Val.conv_wt.

  Case "exec_Mgetparam".
    inv MS. inv MS0;
    (by destruct (frame_match_get_slot_bw _ FM0 GS) as [v' (L & LD)];
      eexists; eexists; eapply exec_Mgetparam with (v := v'); try edone;
        unfold load_stack, load_ptr, load in L;
          destruct sp1; simpl in L; destruct in_block; [|done]; inv L;
            apply Val.load_result_wt).

  Case "exec_Mop".
    inv MS.
    pose proof (Op.eval_operation_lessdef _ _ _ (regset_get_list _ _ _ REGS) EVAL) as (? & ? & ?).
    eexists; eexists; eapply exec_Mop; try edone.
    destruct SPM as [[_ ->] | [_ ->]].
    eby apply eval_operation_none_some.
    edone.
  
  Case "exec_Mload".
    inv MS.
    pose proof (Op.eval_addressing_lessdef _ _ _ 
      (regset_get_list _ _ _ REGS) EVALA).
    eexists; eexists; eapply exec_Mload; try edone.
    destruct SPM as [[_ ->] | [_ ->]].
    eby apply eval_addressing_none_some.
    edone.

  Case "exec_Mstore".
    inv MS.
    pose proof (Op.eval_addressing_lessdef _ _ _ 
      (regset_get_list _ _ _ REGS) EVALA).
    eexists; eexists; eapply exec_Mstore; try edone.
    destruct SPM as [[_ ->] | [_ ->]].
    eby apply eval_addressing_none_some.
    edone.

  Case "exec_Mcall".
    inv MS.
    destruct (find_function_find_function_ptr_bw _ _ _ FF) as (? & ? & ?).
    inv WTS. destruct (return_address_exists _ _ (is_tail_cons_left TAIL)). 
    destruct (range_inside_dec (Ptr.sub_int sp1 rasize, Int.zero) stkr).
      eexists; eexists; eapply exec_Mcall; try edone.
      eby eapply find_function_ptr_lessdef.
    eexists; eexists; eapply exec_Mcall_oom; try edone.
    eby eapply find_function_ptr_lessdef.

  Case "exec_Mgoto".
    by inv MS; eexists; eexists; vauto.
   
  Case "exec_Mcond_true".    
    inv MS; eexists; eexists; eapply exec_Mcond_true;
      eauto using regset_get_list, Op.eval_condition_lessdef.

  Case "exec_Mcond_false".    
    inv MS; eexists; eexists; eapply exec_Mcond_false;
      eauto using regset_get_list, Op.eval_condition_lessdef.

  Case "exec_Mreturn".
    inv MS; eexists; eexists; eapply exec_Mreturn; try edone.
    by eapply range_inside_top; ri_res.

  Case "exec_Mthreadcreate".
    inv MS; eexists; eexists; eapply exec_Mthreadcreate; try edone.
    unfold memarglist_from_sig. simpl. edone.

  Case "exec_Matomic".
    inv MS; eexists; eexists; eapply exec_Matomic; try edone.
    rewrite (Op.atomic_statement_lessdef_arg ASME). edone.
    by apply regset_get_list.

  Case "exec_Mfence".
    by inv MS; eexists; eexists; vauto.

  Case "exec_function_internal_empty".
    inv MS.
    (* Standard call *)
    destruct (range_inside_dec (Ptr.sub_int sp0 (total_framesize f), Int.zero) 
                           stkr).
      eby eexists; eexists; eapply exec_function_internal.
    eby eexists; eexists; eapply exec_function_internal_oom.
    (* Initialisation alloc *)
    destruct (Z_le_dec (4 * Conventions.size_arguments (funsig (Internal f)) + 
                        15 + fe_retaddrsize) thread_stack_size).
      eby eexists; eexists; eapply exec_Initalloc with (stkp := Ptr 0 Int.zero). 
    eby eexists; eexists; eapply exec_Initalloc_oom; try edone; omega. 
    (* Init arguments *)
    destruct locs2 as [|[] locs2]; destruct vs2'; try done.
        (* No arguments left *)
        eby eexists; eexists; eapply exec_Initretaddr.
      (* Register argument *)
      eby eexists; eexists; eapply exec_Initargreg.
    (* Memory argument *)
    assert (AC: Conventions.loc_argument_acceptable (Locations.S s)).
      eapply Conventions.loc_arguments_acceptable with (funsig (Internal f)).
      rewrite SG. apply in_or_app. right. by left.
    destruct s; try done.
    eby eexists; eexists; eapply exec_Initargmem.

  Case "exec_function_internal_nonempty".
    inv MS.
    (* Standard call *)
    destruct (range_inside_dec (Ptr.sub_int sp0 (total_framesize f), Int.zero) 
                           stkr).
      eby eexists; eexists; eapply exec_function_internal.
    eby eexists; eexists; eapply exec_function_internal_oom.
    (* Initialisation alloc *)
    destruct (Z_le_dec (4 * Conventions.size_arguments (funsig (Internal f)) + 
                        15 + fe_retaddrsize) thread_stack_size).
      eby eexists; eexists; eapply exec_Initalloc with (stkp := Ptr 0 Int.zero). 
    eby eexists; eexists; eapply exec_Initalloc_oom; try edone; omega. 
    (* Init arguments *)
    destruct locs2 as [|[] locs2]; destruct vs2'; try done.
        (* No arguments left *)
        eby eexists; eexists; eapply exec_Initretaddr.
      (* Register argument *)
      eby eexists; eexists; eapply exec_Initargreg.
    (* Memory argument *)
    assert (AC: Conventions.loc_argument_acceptable (Locations.S s)).
      eapply Conventions.loc_arguments_acceptable with (funsig (Internal f)).
      rewrite SG. apply in_or_app. right. by left.
    destruct s; try done.
    eby eexists; eexists; eapply exec_Initargmem.

  Case "exec_function_external_call".
    inv MS.
    destruct (exists_ema rs (Ptr.add sp0 rasize) (ef_sig ef)).
    eby eexists; eexists; eapply exec_function_external_call.
    (* Initialisation alloc *)
    destruct (Z_le_dec (4 * Conventions.size_arguments (funsig (External ef)) + 
                        15 + fe_retaddrsize) thread_stack_size).
      eby eexists; eexists; eapply exec_Initalloc with (stkp := Ptr 0 Int.zero). 
    eby eexists; eexists; eapply exec_Initalloc_oom; try edone; omega. 
    (* Init arguments *)
    destruct locs2 as [|[] locs2]; destruct vs2'; try done.
        (* No arguments left *)
        eby eexists; eexists; eapply exec_Initretaddr.
      (* Register argument *)
      eby eexists; eexists; eapply exec_Initargreg.
    (* Memory argument *)
    assert (AC: Conventions.loc_argument_acceptable (Locations.S s)).
      eapply Conventions.loc_arguments_acceptable with (funsig (External ef)).
      rewrite SG. apply in_or_app. right. by left.
    destruct s; try done.
    eby eexists; eexists; eapply exec_Initargmem.

  Case "exec_function_external_return".
    by inv MS; eexists; eexists; vauto.

  Case "exec_return".
    inv MS. inv STACKS.
    eexists; eexists. eby eapply exec_return. 

  Case "exec_return_exit".
    inv MS.
    - by inv STACKS; eexists; eexists; constructor.
    - destruct stkr. eexists; eexists; constructor. 
    - eexists; eexists; constructor.
Qed.

Theorem mc_ma_perthread_stuck_sim:
  stuck_simulation Machabstr.state  Machconcr.state 
                   (ma_step ge)     (mc_step ge)
                   match_state.
Proof.
  intro; intros.
  eby eapply stuck_sim.
Qed.

End SIM.

(** Initialisation simulation. *)
Theorem thread_init_related:
  forall {ge tgt_init fnp args args'}
    (GENVR : wt_genv ge)
    (INIT :  mc_init ge fnp args = Some tgt_init)
    (LD    : Val.lessdef_list args' args),
    exists src_init,
      ma_init ge fnp args' = Some src_init /\
      forall m, match_state ge tgt_init nil m src_init nil.
Proof.
  intros.
  unfold mc_init, ma_init in *. 
  destruct (Genv.find_funct_ptr ge fnp) as [] _eqn : GFF; [|done].
  destruct f; [|done].
  rewrite (Val.lessdef_list_length LD).
  destruct beq_nat; try done. inv INIT.
  eexists. split. edone.
  intro m. replace (fn_sig f) with (funsig (Internal f)) by done.
  eapply match_states_init; try done; simpl. 
  - clear LD; revert args'. 
    induction (sig_args (fn_sig f)); intros. done.
    by destruct args'; simpl; rewrite <- IHl. 
  - by apply Val.conv_list_lessdef.
  - by apply Val.conv_list_wt.
  - constructor.
    (* wt_stackframes *)
    constructor. pose proof (GENVR (Vptr fnp) _ GFF) as WTf.
      inv WTf. inv H0. 
      split; unfold fe_retaddrsize, funsig in *.
        pose proof (Conventions.size_arguments_above (fn_sig f)). omega.
      by rewrite Zmult_comm.
    unfold build_frame. apply type_list_build_frame.
    apply Val.conv_list_wt.    
    (* wt_function *)
    exact (GENVR (Vptr fnp) _ GFF).
    (* wt_regset *)
    done.
Qed.
  
Theorem thread_init_related_none:
  forall {ge fnp args args'}
    (*GENVR : genv_rel sge tge*)
    (INITF : mc_init ge fnp args = None)
    (LD    : Val.lessdef_list args' args),
    ma_init ge fnp args' = None.
Proof.
  intros.
  unfold mc_init, ma_init in *. 
  destruct (Genv.find_funct_ptr ge fnp) as [] _eqn : GFF; [|done].
  destruct f; [|done].
  rewrite (Val.lessdef_list_length LD).
  by destruct beq_nat. 
Qed.
