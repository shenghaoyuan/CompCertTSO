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

(** Correctness proof for the [Reload] pass. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Pointers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Import Simulations.
Require Import TSOmachine.
Require Import TSOsimulation.
(*Require Import Allocproof.*)
Require Import LTLin.
Require Import LTLintyping.
Require Import Linear.
Require Import Parallelmove.
Require Import Reload.
Require Import Memcomp Traces.
Require Import Libtactics.


(* TODO: define a relation on global environments... *)
Definition genv_rel : LTLin.genv -> Linear.genv -> Prop :=
 (fun x y => Genv.genv_match (fun a b => transf_fundef a = b) y x).

(** * Exploitation of the typing hypothesis *)

(** Reloading is applied to LTLin code that is well-typed in
  the sense of [LTLintyping]. We exploit this hypothesis to obtain information on
  the number of temporaries required for reloading the arguments. *)

Fixpoint temporaries_ok_rec (tys: list typ) (itmps ftmps: list mreg)
                            {struct tys} : bool :=
  match tys with
  | nil => true
  | Tint :: ts =>
      match itmps with
      | nil => false
      | it1 :: its => temporaries_ok_rec ts its ftmps
      end
  | Tfloat :: ts =>
      match ftmps with
      | nil => false
      | ft1 :: fts => temporaries_ok_rec ts itmps fts
      end
  end.

Definition temporaries_ok (tys: list typ) :=
  temporaries_ok_rec tys int_temporaries float_temporaries.

Remark temporaries_ok_rec_incr_1:
  forall tys it itmps ftmps,
  temporaries_ok_rec tys itmps ftmps = true ->
  temporaries_ok_rec tys (it :: itmps) ftmps = true.
Proof.
  induction tys; intros until ftmps; simpl.
  tauto.
  destruct a. 
  destruct itmps. congruence. auto.
  destruct ftmps. congruence. auto.
Qed.

Remark temporaries_ok_rec_incr_2:
  forall tys ft itmps ftmps,
  temporaries_ok_rec tys itmps ftmps = true ->
  temporaries_ok_rec tys itmps (ft :: ftmps) = true.
Proof.
  induction tys; intros until ftmps; simpl.
  tauto.
  destruct a. 
  destruct itmps. congruence. auto.
  destruct ftmps. congruence. auto.
Qed.

Remark temporaries_ok_rec_decr:
  forall tys ty itmps ftmps,
  temporaries_ok_rec (ty :: tys) itmps ftmps = true ->
  temporaries_ok_rec tys itmps ftmps = true.
Proof.
  intros until ftmps. simpl. destruct ty. 
  destruct itmps. congruence. intros. apply temporaries_ok_rec_incr_1; auto.
  destruct ftmps. congruence. intros. apply temporaries_ok_rec_incr_2; auto.
Qed.

Lemma temporaries_ok_enough_rec:
  forall locs itmps ftmps,
  temporaries_ok_rec (List.map Loc.type locs) itmps ftmps = true ->
  enough_temporaries_rec locs itmps ftmps = true.
Proof.
  induction locs; intros until ftmps.
  simpl. auto.
  simpl enough_temporaries_rec. simpl map. 
  destruct a. intros. apply IHlocs. eapply temporaries_ok_rec_decr; eauto. 
  simpl. destruct (slot_type s). 
  destruct itmps; auto.
  destruct ftmps; auto.
Qed.

Lemma temporaries_ok_enough:
  forall locs,
  temporaries_ok (List.map Loc.type locs) = true ->
  enough_temporaries locs = true.
Proof.
  unfold temporaries_ok, enough_temporaries. intros. 
  apply temporaries_ok_enough_rec; auto.
Qed.

Lemma enough_temporaries_op_args:
  forall (op: operation) (args: list loc) (res: loc),
  (List.map Loc.type args, Loc.type res) = type_of_operation op ->
  enough_temporaries args = true.
Proof.
  intros. apply temporaries_ok_enough.
  replace (map Loc.type args) with (fst (type_of_operation op)).
  destruct op; try (destruct c); try (destruct a); compute; try reflexivity.
  rewrite <- H. auto.
Qed.

Lemma enough_temporaries_astmt_args:
  forall (op: atomic_statement) (args: list loc) (res: loc),
  (List.map Loc.type args, Loc.type res) = type_of_atomic_statement op ->
  enough_temporaries args = true.
Proof.
  intros. apply temporaries_ok_enough.
  replace (map Loc.type args) with (fst (type_of_atomic_statement op)).
  destruct op; try (destruct c); compute; reflexivity.
  rewrite <- H. auto.
Qed.

Lemma enough_temporaries_cond:
  forall (cond: condition) (args: list loc),
  List.map Loc.type args = type_of_condition cond ->
  enough_temporaries args = true.
Proof.
  intros. apply temporaries_ok_enough. rewrite H.
  destruct cond; compute; reflexivity.
Qed.

Lemma enough_temporaries_addr:
  forall (addr: addressing) (args: list loc),
  List.map Loc.type args = type_of_addressing addr ->
  enough_temporaries args = true.
Proof.
  intros. apply temporaries_ok_enough. rewrite H. 
  destruct addr; compute; reflexivity.
Qed.

Lemma temporaries_ok_rec_length:
  forall tys itmps ftmps,
  (length tys <= length itmps)%nat ->
  (length tys <= length ftmps)%nat ->
  temporaries_ok_rec tys itmps ftmps = true.
Proof.
  induction tys; intros until ftmps; simpl.
  auto.
  intros. destruct a.
  destruct itmps; simpl in H. omegaContradiction. apply IHtys; omega.
  destruct ftmps; simpl in H0. omegaContradiction. apply IHtys; omega.
Qed.

Lemma enough_temporaries_length:
  forall args,
  (length args <= 2)%nat -> enough_temporaries args = true.
Proof.
  intros. apply temporaries_ok_enough. unfold temporaries_ok.
  apply temporaries_ok_rec_length. 
  rewrite list_length_map. simpl. omega.
  rewrite list_length_map. simpl. omega.
Qed.

Lemma not_enough_temporaries_length:
  forall src args,
  enough_temporaries (src :: args) = false ->
  (length args >= 2)%nat.
Proof.
  intros.
  assert (length (src :: args) <= 2 \/ length (src :: args) > 2)%nat by omega.
  destruct H0.
  exploit enough_temporaries_length. eauto. congruence. 
  simpl in H0. omega.
Qed.

Lemma not_enough_temporaries_addr:
  forall (ge: genv) sp addr src args ls v,
  enough_temporaries (src :: args) = false ->
  eval_addressing ge sp addr (List.map ls args) = Some v ->
  eval_operation ge sp (op_for_binary_addressing addr) (List.map ls args) = Some v.
Proof.
  intros.
  apply eval_op_for_binary_addressing; auto.
  rewrite list_length_map. eapply not_enough_temporaries_length; eauto.
Qed.

(** Some additional properties of [reg_for] and [regs_for]. *)

Lemma regs_for_cons:
  forall src args,
  exists rsrc, exists rargs, regs_for (src :: args) = rsrc :: rargs.
Proof.
  intros. unfold regs_for. simpl. 
  destruct src. econstructor; econstructor; reflexivity. 
  destruct (slot_type s); econstructor; econstructor; reflexivity.
Qed.

Lemma reg_for_not_IT2:
  forall l, loc_acceptable l -> reg_for l <> IT2.
Proof.
  intros. destruct l; simpl. 
  red; intros; subst m. simpl in H. intuition congruence.
  destruct (slot_type s); congruence.
Qed.

(** * Correctness of the Linear constructors *)

(** This section proves theorems that establish the correctness of the
  Linear constructor functions such as [add_move].  The theorems are of
  the general form ``the generated Linear instructions execute and
  modify the location set in the expected way: the result location(s)
  contain the expected values; other, non-temporary locations keep
  their values''. *)

Section LINEAR_CONSTRUCTORS.

Variable ge: genv.
Variable stk: list stackframe.
Variable f: function.
Variable sp: option pointer.

Let lts := (mklts thread_labels (step ge)).


Lemma reg_for_spec:
  forall l,
  R(reg_for l) = l \/ In (R (reg_for l)) temporaries.
Proof.
  intros. unfold reg_for. destruct l. tauto.
  case (slot_type s); simpl; tauto.
Qed.

Lemma reg_for_diff:
  forall l l',
  Loc.diff l l' -> Loc.notin l' temporaries ->
  Loc.diff (R (reg_for l)) l'.
Proof.
  intros. destruct (reg_for_spec l). 
  rewrite H1; auto.
  apply Loc.diff_sym. eapply Loc.in_notin_diff; eauto.
Qed.

Lemma add_reload_correct:
  forall src dst k rs,
  exists rs',
  taustar lts (State stk f sp (add_reload src dst k) rs)
            (State stk f sp k rs') /\
  rs' (R dst) = rs src /\
  forall l, Loc.diff (R dst) l -> 
            loc_acceptable src \/ Loc.diff (R IT1) l ->
            rs' l = rs l.
Proof.
  intros. unfold add_reload. destruct src.
    case (mreg_eq m dst); intro.
      by subst dst; exists rs; split; [constructor |].
    exists (Locmap.set (R dst) (rs (R m)) rs).
    split; [apply steptau_taustar; simpl; apply exec_Lop; reflexivity|]. 
    split. apply Locmap.gss. by intros; apply Locmap.gso.
  exists (Locmap.set (R dst) (rs (S s)) rs).
  split. apply steptau_taustar; simpl; apply exec_Lgetstack.
  by split; [apply Locmap.gss|intros;apply Locmap.gso]. 
Qed.

Lemma add_reload_correct_2:
  forall src k rs,
  loc_acceptable src ->
  exists rs',
  taustar lts (State stk f sp (add_reload src (reg_for src) k) rs)
            (State stk f sp k rs') /\
  rs' (R (reg_for src)) = rs src /\
  (forall l, Loc.notin l temporaries -> rs' l = rs l) /\
  rs' (R IT2) = rs (R IT2).
Proof.
  intros. unfold reg_for, add_reload; destruct src.
  rewrite dec_eq_true. exists rs; split. constructor. auto.
  set (t := match slot_type s with
                    | Tint => IT1
                    | Tfloat => FT1
                    end).
  exists (Locmap.set (R t) (rs (S s)) rs).
  split. apply steptau_taustar.  simpl. apply exec_Lgetstack. 
  split. apply Locmap.gss.
  split. intros. rewrite Locmap.gso; auto. 
  apply Loc.diff_sym. simpl in H0; unfold t; destruct (slot_type s); tauto.
  rewrite Locmap.gso. done.
  unfold t; destruct (slot_type s); red; congruence.
Qed.

Lemma add_spill_correct:
  forall src dst k rs,
  exists rs',
  taustar lts (State stk f sp (add_spill src dst k) rs)
            (State stk f sp k rs') /\
  rs' dst = rs (R src) /\
  forall l, Loc.diff dst l -> rs' l = rs l.
Proof.
  intros. unfold add_spill. destruct dst.
  case (mreg_eq src m); intro.
  subst src. exists rs. split. constructor. tauto.
  exists (Locmap.set (R m) (rs (R src)) rs).
  split. apply steptau_taustar; simpl; apply exec_Lop. reflexivity.
  split. apply Locmap.gss.
  intros; apply Locmap.gso; auto.
  exists (Locmap.set (S s) (rs (R src)) rs).
  split. apply steptau_taustar; simpl; apply exec_Lsetstack. 
  split. apply Locmap.gss.
  intros; apply Locmap.gso; auto.
Qed.

Lemma add_reloads_correct_rec:
  forall srcs itmps ftmps k rs,
  locs_acceptable srcs ->
  enough_temporaries_rec srcs itmps ftmps = true ->
  (forall r, In (R r) srcs -> In r itmps -> False) ->
  (forall r, In (R r) srcs -> In r ftmps -> False) ->
  list_disjoint itmps ftmps ->
  NoDup itmps ->
  NoDup ftmps ->
  exists rs',
  taustar lts 
      (State stk f sp (add_reloads srcs (regs_for_rec srcs itmps ftmps) k) rs)
      (State stk f sp k rs') /\
  reglist rs' (regs_for_rec srcs itmps ftmps) = map rs srcs /\
  (forall r, ~(In r itmps) -> ~(In r ftmps) -> rs' (R r) = rs (R r)) /\
  (forall s, rs' (S s) = rs (S s)).
Proof.
  induction srcs; simpl; intros.
  (* base case *)
  exists rs. split. constructor. tauto.
  (* inductive case *)
  assert (ACC1: loc_acceptable a) by (auto with coqlib).
  assert (ACC2: locs_acceptable srcs) by (red; auto with coqlib).
  destruct a as [r | s].
  (* a is a register *)
  simpl add_reload. rewrite dec_eq_true. 
  exploit IHsrcs; eauto.
  intros [rs' [EX [RES [OTH1 OTH2]]]].
  exists rs'. split. eauto.
  split. simpl. decEq. apply OTH1. red; intros; eauto. red; intros; eauto. auto.
  auto.
  (* a is a stack slot *)
  destruct (slot_type s).
  (* ... of integer type *)
  destruct itmps as [ | it1 itmps ]. discriminate. inv H4.
  destruct (add_reload_correct (S s) it1 (add_reloads srcs (regs_for_rec srcs itmps ftmps) k) rs)
  as [rs1 [A [B C]]].
  exploit IHsrcs; eauto. 
  intros. apply H1 with r. tauto. simpl. tauto. eapply list_disjoint_cons_left; eauto. 
  intros [rs' [P [Q [T U]]]]. 
  exists rs'. split. eapply taustar_trans; eauto. 
  split. simpl. decEq. rewrite <- B. apply T. auto.
    eapply list_disjoint_notin; eauto with coqlib.
    rewrite Q. apply list_map_exten. intros. symmetry. apply C. 
    simpl. destruct x; auto. red; intro; subst m. apply H1 with it1; auto with coqlib.
    auto.
  split. simpl. intros. transitivity (rs1 (R r)).
    apply T; tauto. apply C. simpl. tauto. auto.
  intros. transitivity (rs1 (S s0)). auto. apply C. simpl. auto. auto.
  (* ... of float type *)
  destruct ftmps as [ | ft1 ftmps ]. discriminate. inv H5.
  destruct (add_reload_correct (S s) ft1 (add_reloads srcs (regs_for_rec srcs itmps ftmps) k) rs)
  as [rs1 [A [B C]]].
  exploit IHsrcs; eauto. 
  intros. apply H2 with r. tauto. simpl. tauto. eapply list_disjoint_cons_right; eauto. 
  intros [rs' [P [Q [T U]]]]. 
  exists rs'. split. eapply taustar_trans; eauto. 
  split. simpl. decEq. rewrite <- B. apply T; auto.
    eapply list_disjoint_notin; eauto. apply list_disjoint_sym. eauto. auto with coqlib.
    rewrite Q. apply list_map_exten. intros. symmetry. apply C. 
    simpl. destruct x; auto. red; intro; subst m. apply H2 with ft1; auto with coqlib. auto.
  split. simpl. intros. transitivity (rs1 (R r)).
    apply T; tauto. apply C. simpl. tauto. auto. 
  intros. transitivity (rs1 (S s0)). auto. apply C. simpl. auto. auto.
Qed.

Lemma add_reloads_correct:
  forall srcs rs k,
  enough_temporaries srcs = true ->
  locs_acceptable srcs ->
  exists rs',
  taustar lts (State stk f sp (add_reloads srcs (regs_for srcs) k) rs)
              (State stk f sp k rs') /\
  reglist rs' (regs_for srcs) = List.map rs srcs /\
  forall l, Loc.notin l temporaries -> rs' l = rs l.
Proof.
  intros.
  unfold enough_temporaries in H.
  exploit add_reloads_correct_rec; eauto.
    intros. generalize (H0 _ H1). unfold loc_acceptable. generalize H2. 
    simpl. intuition congruence. 
    intros. generalize (H0 _ H1). unfold loc_acceptable. generalize H2. 
    simpl. intuition congruence. 
    red; intros r1 r2; simpl. intuition congruence.
    unfold int_temporaries. NoRepet.
    unfold float_temporaries. NoRepet.
  intros [rs' [EX [RES [OTH1 OTH2]]]].
  exists rs'. split. eexact EX. 
  split. exact RES.
  intros. destruct l. apply OTH1.
  generalize (Loc.notin_not_in _ _ H1). simpl. intuition congruence.
  generalize (Loc.notin_not_in _ _ H1). simpl. intuition congruence.
  apply OTH2.
Qed.

Lemma add_move_correct:
  forall src dst k rs,
  exists rs',
  taustar lts (State stk f sp (add_move src dst k) rs)
              (State stk f sp k rs') /\
  rs' dst = rs src /\
  forall l, Loc.diff l dst -> Loc.diff l (R IT1) -> Loc.diff l (R FT1) -> rs' l = rs l.
Proof.
  intros; unfold add_move.
  case (Loc.eq src dst); intro.
  subst dst. exists rs. split. constructor. tauto.
  destruct src.
  (* src is a register *)
  generalize (add_spill_correct m dst k rs); intros [rs' [EX [RES OTH]]].
  exists rs'; intuition. apply OTH; apply Loc.diff_sym; auto.
  destruct dst.
  (* src is a stack slot, dst a register *)
  generalize (add_reload_correct (S s) m k rs); intros [rs' [EX [RES OTH]]].
  exists rs'; intuition. apply OTH. apply Loc.diff_sym; auto. right. apply Loc.diff_sym; auto.
  (* src and dst are stack slots *)
  set (tmp := match slot_type s with Tint => IT1 | Tfloat => FT1 end).
  generalize (add_reload_correct (S s) tmp (add_spill tmp (S s0) k) rs);
  intros [rs1 [EX1 [RES1 OTH1]]].
  generalize (add_spill_correct tmp (S s0) k rs1);
  intros [rs2 [EX2 [RES2 OTH2]]].
  exists rs2. split.
  eapply taustar_trans; eauto. 
  split. congruence.
  intros. rewrite OTH2. apply OTH1. 
  apply Loc.diff_sym. unfold tmp; case (slot_type s); auto.
  right. apply Loc.diff_sym; auto.
  apply Loc.diff_sym; auto.
Qed.

Lemma effect_move_sequence:
  forall k moves rs,
  let k' := List.fold_right (fun p k => add_move (fst p) (snd p) k) k moves in
  exists rs',
  taustar lts (State stk f sp k' rs)
              (State stk f sp k rs') /\
  effect_seqmove moves rs rs'.
Proof.
  induction moves; intros; simpl.
  exists rs; split. constructor. constructor.
  destruct a as [src dst]; simpl.
  set (k1 := fold_right
              (fun (p : loc * loc) (k : code) => add_move (fst p) (snd p) k)
              k moves) in *.
  destruct (add_move_correct src dst k1 rs) as [rs1 [A [B C]]].
  destruct (IHmoves rs1) as [rs' [D E]].
  exists rs'; split. 
  eapply taustar_trans; eauto.
  econstructor; eauto. red. tauto. 
Qed.

Lemma parallel_move_correct:
  forall srcs dsts k rs,
  List.length srcs = List.length dsts ->
  Loc.no_overlap srcs dsts ->
  Loc.norepet dsts ->
  Loc.disjoint srcs temporaries ->
  Loc.disjoint dsts temporaries ->
  exists rs',
  taustar lts (State stk f sp (parallel_move srcs dsts k) rs)
              (State stk f sp k rs') /\
  List.map rs' dsts = List.map rs srcs /\
  forall l, Loc.notin l dsts -> Loc.notin l temporaries -> rs' l = rs l.
Proof.
  intros. 
  generalize (effect_move_sequence k (parmove srcs dsts) rs).
  intros [rs' [EXEC EFFECT]].
  exists rs'. split. exact EXEC. 
  apply effect_parmove; auto.
Qed.

Lemma parallel_move_arguments_correct:
  forall args sg k rs,
  List.map Loc.type args = sg.(sig_args) ->
  locs_acceptable args ->
  exists rs',
  taustar lts (State stk f sp (parallel_move args (loc_arguments sg) k) rs)
              (State stk f sp k rs') /\
  List.map rs' (loc_arguments sg) = List.map rs args /\
  forall l, Loc.notin l (loc_arguments sg) -> Loc.notin l temporaries -> rs' l = rs l.
Proof.
  intros. apply parallel_move_correct.
  transitivity (length sg.(sig_args)).
  rewrite <- H. symmetry; apply list_length_map. 
  symmetry. apply loc_arguments_length.
  apply no_overlap_arguments; auto.
  apply loc_arguments_norepet.
  apply locs_acceptable_disj_temporaries; auto.
  apply loc_arguments_not_temporaries.
Qed.

Lemma parallel_move_parameters_correct:
  forall params sg k rs,
  List.map Loc.type params = sg.(sig_args) ->
  locs_acceptable params ->
  Loc.norepet params ->
  exists rs',
  taustar lts (State stk f sp (parallel_move (loc_parameters sg) params k) rs)
              (State stk f sp k rs') /\
  List.map rs' params = List.map rs (loc_parameters sg) /\
  forall l, Loc.notin l params -> Loc.notin l temporaries -> rs' l = rs l.
Proof.
  intros. apply parallel_move_correct.
  transitivity (length sg.(sig_args)).
  apply loc_parameters_length.
  rewrite <- H. apply list_length_map.
  apply no_overlap_parameters; auto.
  auto. apply loc_parameters_not_temporaries. 
  apply locs_acceptable_disj_temporaries; auto.
Qed.

End LINEAR_CONSTRUCTORS.

(** * Agreement between values of locations *)

(** The predicate [agree] states that two location maps
  give compatible values to all acceptable locations,
  that is, non-temporary registers and [Local] stack slots.
  The notion of compatibility used is the [Val.lessdef] ordering,
  which enables a [Vundef] value in the original program to be refined
  into any value in the transformed program.  

  A typical situation where this refinement of values occurs is at
  function entry point.  In LTLin, all registers except those
  belonging to the function parameters are set to [Vundef].  In
  Linear, these registers have whatever value they had in the caller
  function.  This difference is harmless: if the original LTLin code
  does not get stuck, we know that it does not use any of these
  [Vundef] values. *)

Definition agree (rs1 rs2: locset) : Prop :=
  forall l, loc_acceptable l -> Val.lessdef (rs1 l) (rs2 l).

Lemma agree_loc:
  forall rs1 rs2 l,
  agree rs1 rs2 -> loc_acceptable l -> Val.lessdef (rs1 l) (rs2 l).
Proof.
  auto.
Qed.

Lemma agree_locs:
  forall rs1 rs2 ll,
  agree rs1 rs2 -> locs_acceptable ll -> 
  Val.lessdef_list (map rs1 ll) (map rs2 ll).
Proof.
  induction ll; simpl; intros.
  constructor.
  constructor. apply H. apply H0; auto with coqlib.
  apply IHll; auto. red; intros. apply H0; auto with coqlib.
Qed.

Lemma agree_exten:
  forall rs ls1 ls2,
  agree rs ls1 ->
  (forall l, Loc.notin l temporaries -> ls2 l = ls1 l) ->
  agree rs ls2.
Proof.
  intros; red; intros. rewrite H0. auto. 
  apply temporaries_not_acceptable; auto.
Qed.

Remark undef_temps_others:
  forall rs l,
  Loc.notin l temporaries -> LTL.undef_temps rs l = rs l.
Proof.
  intros. apply Locmap.guo; auto. 
Qed.

Remark undef_op_others:
  forall op rs l,
  Loc.notin l temporaries -> undef_op op rs l = rs l.
Proof.
  intros. generalize (undef_temps_others rs l H); intro. 
  destruct op; simpl; auto.
Qed.

Lemma agree_undef_temps:
  forall rs1 rs2,
  agree rs1 rs2 -> agree (LTL.undef_temps rs1) rs2.
Proof.
  intros; red; intros. rewrite undef_temps_others; auto. 
  apply Conventions.temporaries_not_acceptable. auto.
Qed.

Lemma agree_undef_temps2:
  forall rs1 rs2,
  agree rs1 rs2 -> agree (LTL.undef_temps rs1) (LTL.undef_temps rs2).
Proof.
  intros. apply agree_exten with rs2. apply agree_undef_temps; auto.
  intros. apply undef_temps_others; auto.
Qed.

Lemma agree_set:
  forall rs1 rs2 rs2' l v,
  loc_acceptable l ->
  Val.lessdef v (rs2' l) ->
  (forall l', Loc.diff l l' -> Loc.notin l' temporaries -> rs2' l' = rs2 l') ->
  agree rs1 rs2 -> agree (Locmap.set l v rs1) rs2'.
Proof.
  intros; red; intros.
  destruct (Loc.eq l l0).
  subst l0. rewrite Locmap.gss. auto.
  assert (Loc.diff l l0). eapply loc_acceptable_noteq_diff; eauto.
  rewrite Locmap.gso; auto. rewrite H1. auto. auto.
  apply temporaries_not_acceptable; auto. 
Qed.

Lemma agree_set2:
  forall rs1 rs2 rs2' l v,
  loc_acceptable l ->
  Val.lessdef v (rs2' l) ->
  (forall l', Loc.diff l l' -> Loc.notin l' temporaries -> rs2' l' = rs2 l') ->
  agree rs1 rs2 -> agree (Locmap.set l v (LTL.undef_temps rs1)) rs2'.
Proof.
  intros. eapply agree_set; eauto. apply agree_undef_temps; auto.
Qed.

Lemma agree_find_funct:
  forall (ge: Linear.genv) rs ls r f,
  Genv.find_funct ge (rs r) = Some f ->
  agree rs ls ->
  loc_acceptable r ->
  Genv.find_funct ge (ls r) = Some f.
Proof.
  intros. 
  assert (Val.lessdef (rs r) (ls r)) by (eapply agree_loc; eauto).
  by destruct (rs r); try done; inv H2.
Qed.

Lemma agree_postcall_1:
  forall rs ls,
  agree rs ls ->
  agree (LTL.postcall_locs rs) ls.
Proof.
  intros; red; intros. unfold LTL.postcall_locs.
  destruct l; auto. 
  destruct (In_dec Loc.eq (R m) temporaries). constructor.
  destruct (In_dec Loc.eq (R m) destroyed_at_call). constructor.
  auto.
Qed.

Lemma agree_postcall_2:
  forall rs ls ls',
  agree (LTL.postcall_locs rs) ls ->
  (forall l,
      loc_acceptable l -> ~In l destroyed_at_call -> ~In l temporaries ->
      ls' l = ls l) ->
  agree (LTL.postcall_locs rs) ls'.
Proof.
  intros; red; intros. generalize (H l H1). unfold LTL.postcall_locs. 
  destruct l. 
  destruct (In_dec Loc.eq (R m) temporaries). intro; constructor.
  destruct (In_dec Loc.eq (R m) destroyed_at_call). intro; constructor.
  intro. rewrite H0; auto. 
  intro. rewrite H0; auto.
  simpl. intuition congruence.
  simpl. intuition congruence.
Qed.

Lemma agree_postcall_call:
  forall rs ls ls' sig,
  agree rs ls ->
  (forall l,
     Loc.notin l (loc_arguments sig) -> Loc.notin l temporaries -> 
     ls' l = ls l) ->
  agree (LTL.postcall_locs rs) ls'.
Proof.
  intros. apply agree_postcall_2 with ls. apply agree_postcall_1; auto.
  intros. apply H0.
  apply arguments_not_preserved; auto.
  destruct l; simpl. simpl in H2. intuition congruence. 
  destruct s; tauto.
  apply temporaries_not_acceptable; auto.
Qed.


Lemma agree_postthreadcreate_1:
  forall rs ls,
  agree rs ls ->
  agree (LTL.postthreadcreate_locs rs) ls.
Proof.
  intros; red; intros. unfold LTL.postthreadcreate_locs.
  destruct l; auto. 
  destruct (In_dec Loc.eq (R m) temporaries). constructor.
  destruct (In_dec Loc.eq (R m) destroyed_at_threadcreate). constructor.
  auto.
Qed.

Lemma agree_postthreadcreate_2:
  forall rs ls ls',
  agree (LTL.postthreadcreate_locs rs) ls ->
  (forall l,
      loc_acceptable l -> ~In l destroyed_at_threadcreate -> ~In l temporaries ->
      ls' l = ls l) ->
  agree (LTL.postthreadcreate_locs rs) ls'.
Proof.
  intros; red; intros. generalize (H l H1). unfold LTL.postthreadcreate_locs. 
  destruct l. 
  destruct (In_dec Loc.eq (R m) temporaries). intro; constructor.
  destruct (In_dec Loc.eq (R m) destroyed_at_threadcreate). intro; constructor.
  intro. rewrite H0; auto. 
  intro. rewrite H0; auto.
  simpl. intuition congruence.
  simpl. intuition congruence.
Qed.

Lemma agree_postthreadcreate_call:
  forall rs ls ls' sig,
  agree rs ls ->
  (forall l,
     Loc.notin l (loc_arguments sig) -> Loc.notin l temporaries -> 
     ls' l = ls l) ->
  agree (LTL.postthreadcreate_locs rs) ls'.
Proof.
  intros. apply agree_postthreadcreate_2 with ls. apply agree_postthreadcreate_1; auto.
  intros. apply H0.
  apply arguments_not_preserved; auto.
  destruct l; simpl. simpl in H2. intuition congruence. 
  destruct s; tauto.
  apply temporaries_not_acceptable; auto.
Qed.

Lemma agree_init_locs:
  forall ls dsts vl,
  locs_acceptable dsts ->
  Loc.norepet dsts ->
  Val.lessdef_list vl (map ls dsts) ->
  agree (LTL.init_locs vl dsts) ls.
Proof.
  induction dsts; intros; simpl.
  red; intros. unfold Locmap.init. constructor.
  simpl in H1. inv H1. inv H0. 
  apply agree_set with ls. apply H; auto with coqlib. auto. auto.
  apply IHdsts; auto. red; intros; apply H; auto with coqlib.
Qed.

Lemma call_regs_parameters:
  forall ls sig,
  map (call_regs ls) (loc_parameters sig) = map ls (loc_arguments sig).
Proof.
  intros. unfold loc_parameters. rewrite list_map_compose. 
  apply list_map_exten; intros. 
  unfold call_regs, parameter_of_argument. 
  generalize (loc_arguments_acceptable _ _ H). 
  unfold loc_argument_acceptable. 
  destruct x. auto.
  destruct s; intros; try contradiction. auto.
Qed. 

Lemma return_regs_preserve:
  forall ls1 ls2 l,
  ~ In l temporaries ->
  ~ In l destroyed_at_call ->
  return_regs ls1 ls2 l = ls1 l.
Proof.
  intros. unfold return_regs. destruct l; auto.
  destruct (In_dec Loc.eq (R m) temporaries). contradiction.
  destruct (In_dec Loc.eq (R m) destroyed_at_call). contradiction.
  auto.
Qed.

(* Lemma return_regs_arguments: *)
(*   forall ls1 ls2 sig, *)
(*   tailcall_possible sig -> *)
(*   map (return_regs ls1 ls2) (loc_arguments sig) = map ls2 (loc_arguments sig). *)
(* Proof. *)
(*   intros. apply list_map_exten; intros.  *)
(*   unfold return_regs. generalize (H x H0). destruct x; intros. *)
(*   destruct (In_dec Loc.eq (R m) temporaries). auto. *)
(*   destruct (In_dec Loc.eq (R m) destroyed_at_call). auto. *)
(*   elim n0. eapply arguments_caller_save. eauto. *)
(*   contradiction. *)
(* Qed. *)

Lemma return_regs_result:
  forall ls1 ls2 sig,
  return_regs ls1 ls2 (R (loc_result sig)) = ls2 (R (loc_result sig)).
Proof.
  intros. unfold return_regs. 
  destruct (In_dec Loc.eq (R (loc_result sig)) temporaries). auto.
  destruct (In_dec Loc.eq (R (loc_result sig)) destroyed_at_call). auto.
  generalize (loc_result_temporary sig). tauto. 
Qed.

(** * Preservation of labels and gotos *)

Lemma find_label_add_spill:
  forall lbl src dst k,
  find_label lbl (add_spill src dst k) = find_label lbl k.
Proof.
  intros. destruct dst; simpl; auto.
  destruct (mreg_eq src m); auto.
Qed.

Lemma find_label_add_reload:
  forall lbl src dst k,
  find_label lbl (add_reload src dst k) = find_label lbl k.
Proof.
  intros. destruct src; simpl; auto.
  destruct (mreg_eq m dst); auto.
Qed.

Lemma find_label_add_reloads:
  forall lbl srcs dsts k,
  find_label lbl (add_reloads srcs dsts k) = find_label lbl k.
Proof.
  induction srcs; intros; simpl. auto.
  destruct dsts; auto. rewrite find_label_add_reload. auto.
Qed.

Lemma find_label_add_move:
  forall lbl src dst k,
  find_label lbl (add_move src dst k) = find_label lbl k.
Proof.
  intros; unfold add_move.
  destruct (Loc.eq src dst); auto.
  destruct src. apply find_label_add_spill.
  destruct dst. apply find_label_add_reload.
  rewrite find_label_add_reload. apply find_label_add_spill.
Qed.

Lemma find_label_parallel_move:
  forall lbl srcs dsts k,
  find_label lbl (parallel_move srcs dsts k) = find_label lbl k.
Proof.
  intros. unfold parallel_move. generalize (parmove srcs dsts). 
  induction m; simpl. auto.
  rewrite find_label_add_move. auto.
Qed.

Hint Rewrite find_label_add_spill find_label_add_reload
             find_label_add_reloads find_label_add_move
             find_label_parallel_move: labels.

Opaque reg_for.

Ltac FL := simpl; autorewrite with labels; auto.

Lemma find_label_transf_instr:
  forall lbl sg instr k,
  find_label lbl (transf_instr sg instr k) =
  if LTLin.is_label lbl instr then Some k else find_label lbl k.
Proof.
  intros. destruct instr; FL.
  destruct (is_move_operation o l); FL; FL.
  FL.
  destruct (enough_temporaries (l0 :: l)).
    destruct (regs_for (l0 :: l)); FL.
    FL. FL. 
  destruct s0; FL; FL; FL.
(*  destruct s0; FL; FL; FL. *)
  FL.
  destruct o; FL.
  FL.
Qed.

Lemma find_label_transf_code:
  forall sg lbl c,
  find_label lbl (transf_code sg c) =
  option_map (transf_code sg) (LTLin.find_label lbl c).
Proof.
  induction c; simpl.
  auto.
  rewrite find_label_transf_instr.
  destruct (LTLin.is_label lbl a); auto.
Qed.

Lemma find_label_transf_function:
  forall lbl f c,
  LTLin.find_label lbl (LTLin.fn_code f) = Some c ->
  find_label lbl (Linear.fn_code (transf_function f)) =
  Some (transf_code f c).
Proof.
  intros. destruct f; simpl in *. FL. 
  rewrite find_label_transf_code. rewrite H; auto.
Qed.

(** * Semantic preservation *)

Section PRESERVATION.

(* Assume fixed global environments that are related: *)
Variables (ge : LTLin.genv) (tge : Linear.genv).
Hypothesis TRANSF: genv_rel ge tge.

Let lts := (mklts thread_labels (ltlin_step ge)).
Let tlts := (mklts thread_labels (Linear.step tge)).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
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
  Genv.find_funct tge v = Some (transf_fundef f).
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
  forall f,
  Linear.funsig (transf_fundef f) = LTLin.funsig f.
Proof. 
  intros []; done. 
Qed.

Definition wt_genv := 
  forall f, match (Genv.find_funct ge f) with 
    | Some x => wt_fundef x 
    | None => True
    end.

Hypothesis WTGENV : wt_genv.

Lemma find_function_wt:
  forall ros rs f,
  wt_genv -> LTLin.find_function ge ros rs = Some f -> wt_fundef f.
Proof.
  intros ros rs f WT H. 
  destruct ros; simpl in H.
    by specialize (WT (rs l)); rewrite H in WT. 
  destruct (Genv.find_symbol ge i); try done.
  by specialize (WT (Vptr p)); simpl in WT; rewrite H in WT. 
Qed.


(*
Lemma find_function_translated:
  forall ros ls f,
  LTLin.find_function ge ros ls = Some f ->
  find_function tge ros ls = Some (transf_fundef f).
Proof.
  intros [l|] ls f; simpl.
    destruct (ls l); try done; apply functions_translated; done.
  rewrite symbols_preserved; destruct (Genv.find_symbol ge i); try done.
  apply function_ptr_translated; done.
Qed.
*)

(** The [match_state] predicate relates states in the original LTLin
  program and the transformed Linear program.  The main property
  it enforces are:
- Agreement between the values of locations in the two programs,
  according to the [agree] or [agree_arguments] predicates.
- Agreement between the memory states of the two programs,
  according to the [Mem.lessdef] predicate.
- Lists of LTLin instructions appearing in the source state
  are always suffixes of the code for the corresponding functions.
- Well-typedness of the source code, which ensures that
  only acceptable locations are accessed by this code.
- Agreement over return types during calls: the return type of a function
  is always equal to the return type of the signature of the corresponding
  call.  This invariant is necessary since the conventional location
  used for passing return values depend on the return type.  This invariant
  is enforced through the third parameter of the [match_stackframes]
  predicate, which is the signature of the called function.
*)

Inductive match_stackframes:
       list LTLin.stackframe -> list Linear.stackframe -> signature -> Prop :=
  | match_stackframes_nil:
      forall sig,
(*      sig.(sig_res) = Some Tint -> *)
      match_stackframes nil nil sig
  | match_stackframes_cons:
      forall res f sp c rs s s' c' ls sig,
      match_stackframes s s' (LTLin.fn_sig f) ->
      c' = add_spill (loc_result sig) res (transf_code f c) ->      
      agree (LTL.postcall_locs rs) ls ->
      loc_acceptable res ->
      wt_function f ->
      is_tail c (LTLin.fn_code f) ->
      match_stackframes
         (LTLin.Stackframe res f sp (LTL.postcall_locs rs) c :: s)
         (Linear.Stackframe (transf_function f) sp ls c' :: s')
         sig.

Inductive match_states: LTLin.state -> Linear.state -> Prop :=
  | match_states_intro:
      forall s f sp c rs s' ls
        (STACKS: match_stackframes s s' (LTLin.fn_sig f))
        (AG: agree rs ls)
        (WT: wt_function f)
        (TL: is_tail c (LTLin.fn_code f))
        (*MMD: Mem.lessdef m tm*),
      match_states (LTLin.State s f sp c rs)
                   (Linear.State s' (transf_function f) sp (transf_code f c) ls)
  | match_states_call:
      forall s f args s' ls
        (STACKS: match_stackframes s s' (LTLin.funsig f))
        (AG: Val.lessdef_list args (map ls (Conventions.loc_arguments (LTLin.funsig f))))
        (PRES: s' <> nil -> forall l, ~In l temporaries -> ~In l destroyed_at_call ->
                 ls l = parent_locset s' l)
        (WT: wt_fundef f)
        (*MMD: Mem.lessdef m tm*),
      match_states (LTLin.Callstate s f args)
                   (Linear.Callstate s' (transf_fundef f) ls)
  | match_states_return:
      forall s res s' ls sig
        (STACKS: match_stackframes s s' sig)
        (AG: Val.lessdef res (ls (R (Conventions.loc_result sig))))
        (PRES: s' <> nil -> forall l, ~In l temporaries -> ~In l destroyed_at_call ->
                 ls l = parent_locset s' l)
        (*MMD: Mem.lessdef m tm*),
      match_states (LTLin.Returnstate s res)
                   (Linear.Returnstate s' ls)
  | match_states_blocked:
      forall s res s' ls sig
        (STACKS: match_stackframes s s' sig)
        (AG: Val.lessdef res (ls (R (Conventions.loc_result sig))))
        (PRES: s' <> nil -> forall l, ~In l temporaries -> ~In l destroyed_at_call ->
                 ls l = parent_locset s' l)
        (*MMD: Mem.lessdef m tm*),
      match_states (LTLin.Blockedstate s sig)
                   (Linear.Blockedstate s' ls sig).


Lemma match_stackframes_change_sig:
  forall s s' sig1 sig2,
  match_stackframes s s' sig1 ->
  sig2.(sig_res) = sig1.(sig_res) ->
  match_stackframes s s' sig2.
Proof.
  intros. inv H. constructor. (*congruence.*)
  econstructor; eauto. unfold loc_result. rewrite H0. auto.
Qed.

Ltac ExploitWT :=
  match goal with
  | [ WT: wt_function _, TL: is_tail _ _ |- _ ] =>
       generalize (wt_instrs _ WT _ (is_tail_in TL)); intro WTI
  end.


(* Define the simulation relation on states *)
Definition st_rel : LTLin.state -> Linear.state -> Prop :=
  fun s ts => match_states s ts.

(** The proof of semantic preservation is a simulation argument
  based on diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  It is possible for the transformed code to take no transition,
  remaining in the same state; for instance, if the source transition
  corresponds to a move instruction that was eliminated.  
  To ensure that this cannot occur infinitely often in a row,
  we use the following [measure] function that just counts the 
  remaining number of instructions in the source code sequence. *)

Definition measure (st: LTLin.state) : nat :=
  match st with
  | LTLin.State s f sp c ls => List.length c
  | LTLin.Callstate s f ls => 0%nat
  | LTLin.Returnstate s ls => 0%nat
  | LTLin.Blockedstate _ _ => 0%nat
  end.

Theorem transf_step_correct:
  forward_sim_with_undefs2 lts tlts st_rel (fun x y => (measure x < measure y)%nat).
Proof.
  Opaque regs_for. Opaque add_reloads.
  intros s t l s' STEP MS; simpl.
  (ltlin_step_cases (destruct STEP) Case); try inv MS; simpl; right.

  Case "exec_Lop".
  ExploitWT. inv WTI. 
  (* move *)
  simpl.
  destruct (add_move_correct tge s' (transf_function f) sp r1 res (transf_code f b) ls)
        as [ls2 [A [B C]]].
  inv A. 
  left. split; [omega|].
  rewrite !H2; econstructor; eauto with coqlib; apply agree_set2 with ls2; auto. 
  rewrite B. simpl in H; inversion H. auto.

  right; econstructor; split. eapply step_taustar_weakstep; eauto.
  econstructor; eauto with coqlib. 
  apply agree_set2 with ls; auto.
  rewrite B. simpl in H; inversion H. auto.
  intros; apply C; [by apply Loc.diff_sym| |]; simpl in *; tauto.

  (* other ops *)
  assert (is_move_operation op args = None).
    caseEq (is_move_operation op args); intros.
    destruct (is_move_operation_correct _ _ H0). congruence.
    auto.
  rewrite H0.
  exploit add_reloads_correct. 
    eapply enough_temporaries_op_args; eauto. auto.
  intros [ls2 [A [B C]]]. instantiate (1 := ls) in B. 
  assert (exists tv, eval_operation tge sp op (reglist ls2 (regs_for args)) = Some tv
                     /\ Val.lessdef v tv).
    apply eval_operation_lessdef with (map rs args); auto.
    rewrite B. eapply agree_locs; eauto. 
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  destruct H1 as [tv [P Q]].
  exploit add_spill_correct.
  intros [ls3 [D [E F]]].
  right; econstructor; split.
  eapply taustar_weakstep. eexact A. 
  eapply step_taustar_weakstep; simpl. eapply exec_Lop with (v := tv); eauto.
  eexact D. eauto. 
  econstructor; eauto with coqlib.
  apply agree_set2 with ls; auto.
  rewrite E. rewrite Locmap.gss. auto.
  intros. rewrite F; auto. rewrite Locmap.gso. rewrite undef_op_others; auto. 
  apply reg_for_diff; auto.

  Case "exec_Lload".
  ExploitWT; inv WTI.

  exploit (add_reloads_correct tge s' (transf_function f) sp args ls). 
    eby eapply enough_temporaries_addr. auto.
  intros [ls2 [A [B C]]].

  assert (eval_addressing tge sp addr (reglist ls2 (regs_for args)) = Some (Vptr a)) as P.
    apply eval_addressing_lessdef with (map rs args).
      by rewrite B; apply agree_locs.
    by rewrite <- H; apply eval_addressing_preserved; apply symbols_preserved.

  exploit (add_spill_correct tge s').
  intros [ls3 [D [E F]]].
  eexists; split.
    eapply taustar_weakstep. eassumption.
  eby eapply step_taustar_weakstep; simpl; [eapply exec_Lload|].

  intros; eexists; split.
    by constructor; try done; inv H0.
  constructor; try done.
    apply agree_set2 with ls; try done; [by rewrite E; rewrite Locmap.gss|].
    intros; rewrite F; auto. 
    by rewrite Locmap.gso; try apply reg_for_diff; try rewrite undef_temps_others; auto.
  eby eapply is_tail_cons_left.

  Case "exec_Lstore".
  ExploitWT; inv WTI.
  caseEq (enough_temporaries (src :: args)); intro ENOUGH. 
  destruct (regs_for_cons src args) as [rsrc [rargs EQ]]. rewrite EQ.
  exploit add_reloads_correct.
    eauto. red; intros. elim H0; intro; auto. subst l; auto. 
  intros [ls2 [A [B C]]]. rewrite EQ in A. rewrite EQ in B.
  injection B. intros D E. 
  simpl in B.
  assert (eval_addressing tge sp addr (reglist ls2 rargs) = Some (Vptr a)).
    apply eval_addressing_lessdef with (map rs args).
    rewrite D. eapply agree_locs; eauto. 
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
(*  destruct H0 as [ta [P Q]] . *)
  assert (X: Val.lessdef (rs src) (ls2 (R rsrc))).
    eby rewrite E; eapply agree_loc.
  eexists; eexists; split; [apply cast_value_to_chunk_lessdef, (Val.conv_lessdef _ _ _ X)|split].
    eapply taustar_weakstep; [eassumption|].
    by apply step_weakstep; simpl; apply exec_Lstore.
  by econstructor; eauto with coqlib;
    apply agree_undef_temps2; apply agree_exten with ls.

  (* not enough temporaries *)
  destruct (add_reloads_correct tge s' (transf_function f) sp args ls
             (Lop (op_for_binary_addressing addr) (regs_for args) IT2
            :: add_reload src (reg_for src)
                 (Lstore chunk (Aindexed Int.zero) (IT2 :: nil) (reg_for src)
                  :: transf_code f b)))
  as [ls2 [A [B C]]].
    eby eapply enough_temporaries_addr. auto.
  assert (eval_addressing tge sp addr (reglist ls2 (regs_for args)) = Some (Vptr a)).
    apply eval_addressing_lessdef with (map rs args).
    rewrite B; eapply agree_locs; eauto. 
    by rewrite <- H; apply eval_addressing_preserved; apply symbols_preserved.
  set (ls3 := Locmap.set (R IT2) (Vptr a) (undef_op (op_for_binary_addressing addr) ls2)).
  destruct (add_reload_correct_2 tge s' (transf_function f) sp src
              (Lstore chunk (Aindexed Int.zero) (IT2 :: nil) (reg_for src)
                  :: transf_code f b) ls3 H7)
  as [ls4 [D [E [F G]]]].
  assert (NT: Loc.notin src temporaries) by (apply temporaries_not_acceptable; auto).
  assert (X: Val.lessdef (rs src) (ls4 (R (reg_for src)))).
    rewrite E. unfold ls3. rewrite Locmap.gso. 
    rewrite undef_op_others; auto. rewrite C; auto.
    apply Loc.diff_sym. simpl in NT; tauto. 
  eexists; eexists; split; [by apply cast_value_to_chunk_lessdef, (Val.conv_lessdef _ _ _ X)|split].
  eapply taustar_weakstep; [eassumption|].
  eapply steptau_weakstep; simpl.
    eapply exec_Lop with (v := Vptr a). 
    rewrite B. eapply not_enough_temporaries_addr; eauto.
    rewrite <- B; auto.
  eapply taustar_weakstep; [eassumption|].
  eapply step_weakstep; simpl; eapply exec_Lstore; eauto.
    simpl reglist. rewrite G. unfold ls3. rewrite Locmap.gss. simpl. 
    by destruct a; rewrite Int.add_zero. 
  econstructor; eauto with coqlib.
  apply agree_undef_temps2. apply agree_exten with ls; auto.
  intros. rewrite F; auto. unfold ls3. rewrite Locmap.gso.
  rewrite undef_op_others; auto. 
  apply Loc.diff_sym. simpl in H1; tauto.

  Case "exec_Lcall".
  ExploitWT. inversion WTI. subst ros0 args0 res0. rewrite <- H0. 
  assert (WTF': wt_fundef f') by (eapply find_function_wt; edone).
  destruct ros as [fn | id].
  (* indirect call *)
  red in H6. destruct H6 as [OK1 [OK2 OK3]].
  rewrite <- H0 in H4. rewrite <- H0 in OK3.
  destruct (parallel_move_arguments_correct tge s' (transf_function f) sp 
              args sig
              (add_reload fn (reg_for fn)
                (Lcall sig (inl ident (reg_for fn))
                  :: add_spill (loc_result sig) res (transf_code f b)))
              ls H4 H7)
  as [ls2 [A [B C]]].
  destruct (add_reload_correct_2 tge s' (transf_function f) sp fn
             (Lcall sig (inl ident (reg_for fn))
              :: add_spill (loc_result sig) res (transf_code f b))
             ls2 OK2)
  as [ls3 [D [E [F G]]]].
  assert (ARGS: Val.lessdef_list (map rs args) 
                                 (map ls3 (loc_arguments sig))).
    replace (map ls3 (loc_arguments sig)) with (map ls2 (loc_arguments sig)).
    by rewrite B; apply agree_locs.
    by apply list_map_exten; intros; apply F; 
       apply Loc.disjoint_notin with (loc_arguments sig); try done;
       apply loc_arguments_not_temporaries.

  right; eexists; split.
  eapply taustar_weakstep. eexact A. eapply taustar_weakstep; simpl. eexact D. 
  eapply step_weakstep; simpl.
  eapply exec_Lcall; eauto.
    simpl. rewrite E. rewrite C. eapply agree_find_funct; eauto. 
    apply functions_translated. eauto.
    apply loc_acceptable_notin_notin; auto. 
    apply temporaries_not_acceptable; auto.
    rewrite H0; symmetry; apply sig_preserved.
  eauto. 
  econstructor; eauto. 
  econstructor; eauto with coqlib.
  rewrite H0. auto.
  apply agree_postcall_call with ls sig; auto.
  intros. rewrite F; auto. congruence.
  (* direct call *)
  rewrite <- H0 in H4.
  destruct (parallel_move_arguments_correct tge s' (transf_function f) sp
              args sig
              (Lcall sig (inr mreg id)
                :: add_spill (loc_result sig) res (transf_code f b))
              ls H4 H7)
  as [ls3 [D [E F]]].
  assert (ARGS: Val.lessdef_list (map rs args) (map ls3 (loc_arguments sig))).
    rewrite E. apply agree_locs; auto.
  right; econstructor; split.
  eapply taustar_weakstep. eexact D. 
  eapply step_weakstep; simpl; eapply exec_Lcall; eauto.
    simpl. rewrite symbols_preserved. 
    generalize H; simpl. destruct (Genv.find_symbol ge id).
    apply function_ptr_translated; auto. congruence.
    rewrite H0. symmetry; apply sig_preserved.
  econstructor; eauto.
  econstructor; eauto with coqlib. rewrite H0; auto. 
  apply agree_postcall_call with ls sig; auto.
  congruence.

  Case "exec_Llabel".
  right; econstructor; split.
  apply step_weakstep; simpl; apply exec_Llabel.
  econstructor; eauto with coqlib.

  Case "exec_Lgoto".
  right; econstructor; split.
  apply step_weakstep; simpl; apply exec_Lgoto. apply find_label_transf_function; eauto.
  econstructor; eauto.
  eapply LTLin.find_label_is_tail; eauto.

  Case "exec_Lcond_true".
  ExploitWT; inv WTI.
  exploit add_reloads_correct.
    eapply enough_temporaries_cond; eauto. auto.
  intros [ls2 [A [B C]]].
  right; econstructor; split.
  eapply taustar_weakstep. eauto. 
  eapply step_weakstep; simpl; eapply exec_Lcond_true; eauto.
  rewrite B. apply eval_condition_lessdef with (map rs args); auto.
  eapply agree_locs; eauto. 
  apply find_label_transf_function; eauto.
  econstructor; eauto.
  apply agree_undef_temps2.  apply agree_exten with ls; auto.
  eapply LTLin.find_label_is_tail; eauto.

  Case "exec_Lcond_false".
  ExploitWT; inv WTI.
  exploit add_reloads_correct.
    eapply enough_temporaries_cond; eauto. auto.
  intros [ls2 [A [B C]]].
  right; econstructor; split.
  eapply taustar_weakstep. eauto. 
  eapply step_weakstep; simpl; eapply exec_Lcond_false; eauto.
  rewrite B. apply eval_condition_lessdef with (map rs args); auto.
  eapply agree_locs; eauto. 
  econstructor; eauto with coqlib.
  apply agree_undef_temps2.  apply agree_exten with ls; auto.

  Case "exec_Lreturn".
  ExploitWT; inv WTI. 
  destruct or; simpl.
  (* with an argument *)
    destruct sp; simpl; [|right];
    exploit add_reload_correct; intros [ls2 [A [B C]]];
    (eexists; split;
     [eapply taustar_weakstep; [eassumption|];
      eapply step_weakstep; simpl; eapply exec_Lreturn; eauto |];
     econstructor; eauto;
     [ rewrite return_regs_result; rewrite B; apply agree_loc; auto
     | intro; apply return_regs_preserve]).

  (* without an argument *)
  destruct sp; simpl; [|right];
   (eexists; split; [apply step_weakstep; simpl; eapply exec_Lreturn; eauto|];  
    econstructor; eauto; intro; apply return_regs_preserve).

  Case "exec_Lthreadcreate".
  ExploitWT. inversion WTI. subst fn0 arg0.
  assert (LA : locs_acceptable (fn :: arg :: nil)).
    by intros l [-> | [-> | N]].
  destruct (parallel_move_arguments_correct tge s' (transf_function f) sp
              (fn :: arg :: nil) thread_create_sig
              (Lthreadcreate
                :: transf_code f b)
              ls H2 LA)
  as [ls3 [D [E F]]].
  assert (ARGS: Val.lessdef_list (map rs (fn :: arg :: nil)) 
                                 (map ls3 (loc_arguments thread_create_sig))).
    rewrite E. apply agree_locs; auto.
  remember (map ls3 (loc_arguments thread_create_sig)) as largs.
  destruct largs as [|lfn [|larg []]]; try done; [].
  inv E. inversion ARGS as [|? ? ? ? LD LDR]. subst.
  rewrite H in LD. inv LD.
  eexists. exists (ls arg :: nil).
  split. by inv ARGS.
  split. eapply taustar_weakstep. eexact D. 
  eapply step_weakstep. simpl. eapply exec_Lthreadcreate.
  congruence.
  econstructor; eauto with coqlib.
  apply agree_postthreadcreate_call with (ls := ls)(sig := thread_create_sig); auto.

  Case "exec_Latomic".
  ExploitWT. inv WTI. 
  destruct lab; try (by inv ASME).
  (* rmw *)
  assert (Evm : v = v0 /\ chunk = Mint32). by inv ASME. destruct Evm as [<- ->]. 
  exploit (add_reloads_correct tge s' (transf_function f) sp args ls); try done.
      eby eapply enough_temporaries_astmt_args.
  intros [ls2 [A [B C]]].
  exploit add_spill_correct.
  intros [l3 [D [E F]]].
  assert (Erl: reglist ls2 (regs_for args) = map rs args).
    eapply atomic_statement_lessdef_arg. edone.
    rewrite B. eapply agree_locs; eauto. 
  econstructor; split.
  eapply taustar_weakstep. eexact A. 
  eapply step_taustar_weakstep; simpl.
    eapply exec_Latomic; eauto. by rewrite Erl.
  eexact D. 
  (* lessdef case of rmw *)
  intros v' LD.
  eexists; split.
  eapply LTLin.exec_Latomic.
  eby eapply atomic_statement_lessdef_res.
  edone. eby eapply Val.has_type_lessdef.
  econstructor; eauto with coqlib.
  apply agree_set2 with ls; auto.
  rewrite E. by rewrite Locmap.gss.  
  intros. rewrite F; auto. rewrite Locmap.gso. auto. 
  rewrite undef_temps_others; auto.
  apply reg_for_diff; auto.

  Case "exec_Lfence".
  ExploitWT. inv WTI. 
  eexists; split; [by eapply step_weakstep; vauto|].
  by econstructor; eauto with coqlib.

  Case "exec_function_internal_empty".
  simpl in WT. inversion_clear WT. inversion H0. simpl in AG.
  destruct (parallel_move_parameters_correct tge s' (transf_function f)
               None (LTLin.fn_params f) (LTLin.fn_sig f)
               (transf_code f (LTLin.fn_code f)) (call_regs ls)
               wt_params wt_acceptable wt_norepet)
  as [ls2 [A [B C]]].
  assert (AG2: agree (LTL.init_locs args (fn_params f)) ls2).
    apply agree_init_locs; auto.
    rewrite B. rewrite call_regs_parameters. auto. 
  right; eexists; split.
  eapply step_taustar_weakstep; simpl.
    eapply exec_function_internal_empty; eauto.
  eassumption.
  econstructor; eauto with coqlib.

  Case "exec_function_internal_nonempty".
  simpl in WT. inversion_clear WT. inversion H. simpl in AG.
  destruct (parallel_move_parameters_correct tge s' (transf_function f)
               (Some stk) (LTLin.fn_params f) (LTLin.fn_sig f)
               (transf_code f (LTLin.fn_code f)) (call_regs ls)
               wt_params wt_acceptable wt_norepet)
  as [ls2 [A [B C]]].
  assert (AG2: agree (LTL.init_locs args (fn_params f)) ls2).
    apply agree_init_locs; auto.
    rewrite B. rewrite call_regs_parameters. auto. 
  eexists; split.
  eapply step_taustar_weakstep; simpl.
    eapply exec_function_internal_nonempty; eauto.
  eassumption.
  by econstructor; eauto with coqlib.

  Case "exec_function_external_call".
  pose proof (lessdef_map_val_of_eval _ _ AG).
  eexists; split.
    by apply step_weakstep; simpl; eapply exec_function_external_call. 
  by econstructor; eauto.

  Case "exec_function_external_return".
  eexists; split.
    apply step_weakstep; simpl; eapply exec_function_external_return; eauto. 
  intros. (*; split ; [by constructor; inv H|].*)
  econstructor; try eassumption. 
    by rewrite Locmap.gss.
  intros; rewrite Locmap.gso; [by auto|].
  by destruct l; try done; intro; subst; elim H;
    generalize (loc_result_temporary efsig); auto. 

  Case "exec_return".
  inv STACKS. 
  exploit add_spill_correct. intros [ls2 [A [B C]]].
  right; eexists; split.
  eapply step_taustar_weakstep; simpl. eapply exec_return; eauto.
  eassumption.
  econstructor; eauto. 
  apply agree_set with ls; auto.
  rewrite B. auto.
  unfold parent_locset in PRES.
  refine (modusponens _ _ (PRES _) _). done.
  by intro PRES'; apply agree_postcall_2 with ls0; auto. 

  Case "exec_return_exit".
  inv STACKS.
  eexists; split. apply step_weakstep. simpl; apply exec_return_exit.
  vauto.
Qed.

Lemma my_backward_sim_with_undefs:
  @backward_sim_with_undefs thread_labels lts tlts te_ldo te_ldi
    (@bsr thread_labels lts tlts st_rel) (@bsc thread_labels tlts).
Proof.
  apply (@forward_to_backward_sim_with_undefs thread_labels lts tlts
          (ltlin_receptive ge) (linear_determinate tge) (ltlin_progress_dec ge) 
          te_ldo te_ldi ldo_samekind_eq ldo_not_tau ldi_refl 
          st_rel (fun x y => (measure x < measure y)%nat)).
  apply (mk_forward_sim_with_undefs).
    apply well_founded_ltof. 
  apply transf_step_correct.
Qed.

Ltac Doptionmap r E :=
  match goal with
    H: option_map ?f ?l = Some ?l' |- _ =>
      destruct l as [r|] _eqn : E; [simpl in H|done]
  end.

Lemma notin_map_eq:
 forall A l ls' (v : A) locs (NI: Loc.notin l locs),
   map (fun l' => if Loc.eq l' l then v else ls' l') locs =
   map ls' locs.
Proof. 
  induction locs; intros. done.
  simpl in NI; destruct NI as [D NI]. 
  simpl. rewrite IHlocs by done.
  f_equal.
  destruct Loc.eq as [-> | N]. eby eelim Loc.same_not_diff.
  done.
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

Lemma build_locs_eq:
  forall sg vals
    (HT: Val.has_type_list vals sg.(sig_args)),
    map (build_locs (loc_arguments sg) vals)
              (loc_arguments sg) = vals.
Proof.
  intro sg.
  pose proof (loc_arguments_norepet sg) as NR.
  unfold loc_arguments in *.
  remember 0 as n. clear Heqn. revert n NR.
  induction (sig_args sg); intros; destruct vals; try done; [].
  simpl in HT; apply andb_true_iff in HT; destruct HT as [_ HT].
  destruct a; inv NR; simpl; destruct Loc.eq; try done; f_equal;
    rewrite <- (IHl _ H2 _ HT); apply list_map_exten; intros l' IN;
      by destruct Loc.eq as [-> | N]; [apply Loc.notin_not_in in H1 |
                                       rewrite (IHl _ H2 _ HT)].
Qed.

Lemma init_sim_succ:
  forall {p vals vals' tinit}
    (LI:  linear_init tge p vals = Some tinit)
    (LD : Val.lessdef_list vals' vals),
    exists sinit, ltlin_init ge p vals' = Some sinit /\ match_states sinit tinit.
Proof.
  intros. unfold ltlin_init, linear_init in *.
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  pose proof (WTGENV (Vptr p)) as WTF. unfold Genv.find_funct in WTF.
  repeat (destruct Genv.find_funct_ptr); try done; [].
  destruct f; destruct f0; try done.
  inv MF. destruct f0. simpl in *.
  destruct (beq_nat (length vals) (length (sig_args fn_sig))) as [] _eqn : BE; [|done].
  apply sym_eq, beq_nat_eq in BE.
  rewrite (Val.lessdef_list_length LD), BE, <- beq_nat_refl.
  eexists; split; try done.
  inv LI; econstructor; vauto. simpl in *.
  rewrite build_locs_eq.
    by apply Val.conv_list_lessdef.
  by apply Val.conv_list_wt.
Qed.

Lemma init_sim_fail:
  forall {p vals vals'}
    (LI: linear_init tge p vals = None)
    (LD : Val.lessdef_list vals' vals),
    ltlin_init ge p vals' = None.
Proof.
  intros. unfold ltlin_init, linear_init in *.
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  destruct (Genv.find_funct_ptr tge p) as [[[]|]|]; try done;
    destruct (Genv.find_funct_ptr ge  p) as [[[]|]|]; try done; simpl in *.
  rewrite (Val.lessdef_list_length LD). inv MF.
  by destruct (beq_nat (length vals) (length (sig_args fn_sig))) as [] _eqn : BE.
Qed.

Definition bsim_rel := @bsr _ lts tlts match_states.
Definition bsim_order := @bsc _ tlts.

End PRESERVATION.

Definition full_genv_rel (ge : LTLin.genv) (tge : Linear.genv) :=
  genv_rel ge tge /\ wt_genv ge.

Definition reload_match_prg (p  : ltlin_sem.(SEM_PRG))
                            (p' : linear_sem.(SEM_PRG)) : Prop :=
  wt_program p /\transf_program p = p'.

(** The whole-system backward simulation for the [Reloading]
    phase. *)
Theorem reload_sim : Sim.sim tso_mm tso_mm ltlin_sem linear_sem reload_match_prg.
Proof.
  eapply (TSOsim_with_undefs.sim ltlin_sem linear_sem full_genv_rel
    bsim_rel (fun _ => bsim_order)); intros; simpl in *.
  - destruct GENVR as [[GR FR] _]. rewrite GR. by inv MP.
  - destruct (Genv.exists_matching_genv_and_mem_rev
                  (transform_program_match (proj2 MP)) INIT) 
      as [sge [INIT' GEM]].
    exists sge. split. done.
    split. done.
    intro f. 
    destruct (Genv.find_funct sge f) as [fd|] _eqn : Efd; [|done].
    set (P f' := exists id, In (id, f') src_prog.(prog_funct)).
    assert (II: forall id' f', In (id', f') src_prog.(prog_funct) -> P f').
      intros id' f' IN. eby eexists.
    pose proof (Genv.find_funct_prop P f INIT' II Efd) as [id IN].
    by specialize (proj1 MP _ _ IN).
  - destruct (init_sim_succ _ _ (proj1 GENVR) (proj2 GENVR) INIT LD) 
      as [si [INIT' MS]].
    exists si. split. done.
    by apply fsr_in_bsr. 
  - eby destruct GENVR; eapply init_sim_fail.
  - by destruct GENR; eapply my_backward_sim_with_undefs.
Qed.
