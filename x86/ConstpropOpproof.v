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

(** Correctness proof for constant propagation (processor-dependent part). *)

Require Import Coqlib.
Require Import Ast.
Require Import Integers.
Require Import Pointers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import ConstpropOp.
Require Import Constprop.

(** * Correctness of the static analysis *)

Section ANALYSIS.

Variable ge: genv.

(** We first show that the dataflow analysis is correct with respect
  to the dynamic semantics: the approximations (sets of values) 
  of a register at a program point predicted by the static analysis
  are a superset of the values actually encountered during concrete
  executions.  We formalize this correspondence between run-time values and
  compile-time approximations by the following predicate. *)

Definition val_match_approx (a: approx) (v: val) : Prop :=
  match a with
  | Unknown => True
  | I p => v = Vint p
  | F p => v = Vfloat p
  | S symb ofs => exists b, Genv.find_symbol ge symb = Some b /\ v = Vptr (MPtr.add b ofs)
  | _ => False
  end.

Inductive val_list_match_approx: list approx -> list val -> Prop :=
  | vlma_nil:
      val_list_match_approx nil nil
  | vlma_cons:
      forall a al v vl,
      val_match_approx a v ->
      val_list_match_approx al vl ->
      val_list_match_approx (a :: al) (v :: vl).

Ltac SimplVMA :=
  match goal with
  | H: (val_match_approx (I _) ?v) |- _ =>
      simpl in H; (try subst v); SimplVMA
  | H: (val_match_approx (F _) ?v) |- _ =>
      simpl in H; (try subst v); SimplVMA
  | H: (val_match_approx (S _ _) ?v) |- _ =>
      simpl in H; 
      (try (elim H;
            let b := fresh "b" in let A := fresh in let B := fresh in
            (intros b [A B]; subst v; clear H)));
      SimplVMA
  | _ =>
      idtac
  end.

Ltac InvVLMA :=
  match goal with
  | H: (val_list_match_approx nil ?vl) |- _ =>
      inversion H
  | H: (val_list_match_approx (?a :: ?al) ?vl) |- _ =>
      inversion H ; SimplVMA; InvVLMA
  | _ =>
      idtac
  end.

(** We then show that [eval_static_operation] is a correct abstract
  interpretations of [eval_operation]: if the concrete arguments match
  the given approximations, the concrete results match the
  approximations returned by [eval_static_operation]. *)

Lemma eval_static_condition_correct:
  forall cond al vl b,
  val_list_match_approx al vl ->
  eval_static_condition cond al = Some b ->
  eval_condition cond vl = Some b.
Proof.
  intros until b.
  unfold eval_static_condition. 
  case (eval_static_condition_match cond al); intros;
  InvVLMA; simpl; congruence.
Qed.

Ltac FZSimpPtr := 
  match goal with
| H: (match ?v with | Ptr _ _ => _ end) = Some _ |- _ =>
  destruct v as [b' ofs']; inv H
end.

Ltac FZSimplGenv :=
 match goal with
   | [ H : Genv.find_symbol _ _ |- _ ] => 
      match goal with
        | [ H' : Genv.find_symbol _ _ |- _ ] =>
            try ( rewrite H' in H )
      end
end.

Ltac FZSimplVMA :=
  match goal with
 | H: (val_match_approx (I _) ?v) |- _ =>
      simpl in H; (try subst v); FZSimplVMA
  | H: (val_match_approx (F _) ?v) |- _ =>
      simpl in H; (try subst v); FZSimplVMA
  | H: (val_match_approx (S _ _) ?v) |- _ =>
      simpl in H; 
      elim H;
        let b := fresh "b" in let A := fresh in let B := fresh in
            (intros b [A B]; (try subst v); clear H);
      FZSimplVMA
 | _ =>
      idtac
  end.
  

Ltac FZInvVLMA :=
  match goal with
  | H: (val_list_match_approx (?a :: ?al) ?vl) |- _ =>
      inversion H; FZSimplVMA
  end.

Ltac FZsimplify :=
  try FZSimpPtr; try FZInvVLMA; try FZInvVLMA; try clarify.

Lemma eval_static_addressing_correct:
  forall addr sp al vl v,
  val_list_match_approx al vl ->
  eval_addressing ge sp addr vl = Some v ->
  val_match_approx (eval_static_addressing addr al) v.
Proof.
  intros until v. unfold eval_static_addressing.
  case (eval_static_addressing_match addr al); intros;
  InvVLMA; simpl in *; FuncInv; try congruence; FZsimplify;
    try (by (exists b0; repeat rewrite MPtr.add_add_r; rewrite <- H1));
    try (by (destruct (Genv.find_symbol ge id); try inv H0; exists p; try rewrite Int.mul_commut)). 
  by (exists b1; rewrite MPtr.add_add_r; rewrite <- H1).
  by (exists b0; repeat rewrite MPtr.add_add_r; rewrite <- H1; simpl; rewrite Int.add_assoc).
Qed.
    (* try (by destruct Int.eq; clarify); *)
    (* try (by destruct Int.ltu; clarify); *)
    (* try by destruct ptr; unfold MPtr.add in *; clarify;  *)
    (*        destruct (Genv.find_symbol ge s1); clarify; *)
    (*        eexists; split; try done; simpl; *)
    (*        rewrite ?Int.sub_add_opp, Int.add_assoc. *)


Lemma eval_static_operation_correct:
  forall op sp al vl v,
  val_list_match_approx al vl ->
  eval_operation ge sp op vl = Some v ->
  val_match_approx (eval_static_operation op al) v.
Proof.
  intros until v.
  unfold eval_static_operation.
  case (eval_static_operation_match op al); intros;
  InvVLMA; simpl in *; FuncInv; try congruence; 
  try (destruct (Int.eq n2 Int.zero); by (inv H0));
  try (destruct (Int.ltu n2 (Int.repr 32)); by (inv H0)); 
  try (destruct (Int.ltu n (Int.repr 32)); by (inv H0)).

  destruct b; inv H0. exists (Ptr z i); split; auto. 
  simpl. do 2 decEq.  rewrite Int.add_commut, Int.sub_add_l, Int.add_commut. auto. 

  destruct (Int.ltu n (Int.repr 31)). 
    destruct (Int.ltu n (Int.repr 32)). by (inv H0). by inv H0. discriminate.

  eapply eval_static_addressing_correct; eauto.

  caseEq (eval_static_condition c vl0).
  intros. generalize (eval_static_condition_correct _ _ _ _ H H1).
  intro. rewrite H2 in H0.
  destruct b; injection H0; intro; subst v; simpl; auto.
  intros; simpl; auto.
Qed.

(** * Correctness of strength reduction *)

(** We now show that strength reduction over operators and addressing
  modes preserve semantics: the strength-reduced operations and
  addressings evaluate to the same values as the original ones if the
  actual arguments match the static approximations used for strength
  reduction. *)

Section STRENGTH_REDUCTION.

Variable app: reg -> approx.
Variable sp: option pointer.
Variable rs: regset.
Hypothesis MATCH: forall r, val_match_approx (app r) rs#r.

Lemma intval_correct:
  forall r n,
  intval app r = Some n -> rs#r = Vint n.
Proof.
  intros until n.
  unfold intval. caseEq (app r); intros; try discriminate.
  generalize (MATCH r). unfold val_match_approx. rewrite H.
  congruence. 
Qed.

Lemma cond_strength_reduction_correct:
  forall cond args,
  let (cond', args') := cond_strength_reduction app cond args in
  eval_condition cond' rs##args' = eval_condition cond rs##args.
Proof.
  intros. unfold cond_strength_reduction.
  case (cond_strength_reduction_match cond args); intros.
  caseEq (intval app r1); intros.
  simpl. rewrite (intval_correct _ _ H).
  destruct (rs#r2); auto. rewrite Int.swap_cmp. auto.
  destruct c; reflexivity.
  caseEq (intval app r2); intros.
  simpl. rewrite (intval_correct _ _ H0). destruct (rs # r1); try destruct p; reflexivity.
  auto.
  caseEq (intval app r1); intros.
  simpl. rewrite (intval_correct _ _ H).
  destruct (rs#r2); auto. rewrite Int.swap_cmpu. auto.
  caseEq (intval app r2); intros.
  simpl. rewrite (intval_correct _ _ H0). auto.
  auto.
  auto.
Qed.

Ltac KnownApprox :=
  match goal with
  | H: ?approx ?r = ?a |- _ =>
      generalize (MATCH r); rewrite H; intro; clear H; KnownApprox
  | _ => idtac
  end.
 
Lemma addr_strength_reduction_correct:
  forall addr args,
  let (addr', args') := addr_strength_reduction app addr args in
  eval_addressing ge sp addr' rs##args' = eval_addressing ge sp addr rs##args.
Proof.
  intros.

  unfold addr_strength_reduction. destruct (addr_strength_reduction_match addr args).

  generalize (MATCH r1); caseEq (app r1); intros; auto.
  simpl in H0. destruct H0 as [b [A B]]. simpl. rewrite A; rewrite B.
  rewrite Int.add_commut. destruct b. simpl. rewrite Int.add_assoc. auto.

  generalize (MATCH r1) (MATCH r2); caseEq (app r1); auto; caseEq (app r2); auto;
  simpl val_match_approx; intros; try contradiction; simpl.
  rewrite H2. destruct (rs#r1); auto. rewrite Int.add_assoc; auto. destruct p. rewrite Int.add_assoc; auto.
  destruct H2 as [b [A B]]. rewrite A; rewrite B.
  destruct (rs#r1); auto. destruct b. repeat rewrite Int.add_assoc. simpl. decEq. decEq. decEq. repeat rewrite Int.add_assoc. decEq. decEq. by rewrite Int.add_commut.
  by destruct p.
  rewrite H1. destruct (rs#r2); auto. decEq. rewrite Int.add_permut. rewrite Int.add_assoc. auto. 
  destruct p. rewrite Int.add_assoc; auto. 
  rewrite H1; rewrite H2. rewrite Int.add_permut. rewrite Int.add_assoc. auto.
  rewrite H1; rewrite H2. auto.
  destruct H2 as [b [A B]]. rewrite A; rewrite B. rewrite H1. destruct b. simpl. do 3 decEq. rewrite <- Int.add_assoc. decEq. rewrite Int.add_assoc. decEq. apply Int.add_commut.
  rewrite H1; auto.
  rewrite H1; auto.
  destruct H1 as [b [A B]]. rewrite A; rewrite B. destruct (rs#r2); auto.
  by destruct b. 
  destruct b; simpl.
  repeat rewrite Int.add_assoc. do 5 decEq. apply Int.add_commut.
  by destruct b. by destruct b.
  destruct H1 as [b [A B]]. rewrite A; rewrite B; rewrite H2. destruct b; simpl. do 3 decEq. by repeat rewrite Int.add_assoc. 
  rewrite H2. destruct (rs#r1); try destruct p; auto.
  destruct H1 as [b [A B]]. destruct H2 as [b' [A' B']].
  rewrite A; rewrite B; rewrite B'. destruct b; auto.

  generalize (MATCH r1) (MATCH r2); caseEq (app r1); auto; caseEq (app r2); auto;
  simpl val_match_approx; intros; try contradiction; simpl.
  rewrite H2. destruct (rs#r1); auto.
  rewrite H1; rewrite H2. auto.
  rewrite H1. auto.
  destruct H1 as [b [A B]]. rewrite A; rewrite B.
  destruct (rs#r2); try destruct b; auto. simpl. do 3 decEq; repeat rewrite Int.add_assoc; do 2 decEq. apply Int.add_commut.
  destruct H1 as [b [A B]]. rewrite A; rewrite B; rewrite H2. rewrite Int.add_assoc. destruct b; simpl. repeat rewrite Int.add_assoc. auto.
  rewrite H2. destruct (rs#r1); auto. destruct p; auto.
  destruct H1 as [b [A B]]. destruct H2 as [b' [A' B']].
  rewrite A; rewrite B; rewrite B'. destruct b; auto.

  generalize (MATCH r1); caseEq (app r1); auto;
  simpl val_match_approx; intros; try contradiction; simpl.
  rewrite H0. auto.

  generalize (MATCH r1); caseEq (app r1); auto;
  simpl val_match_approx; intros; try contradiction; simpl.
  rewrite H0. rewrite Int.mul_commut. auto.

  auto.
Qed.

Lemma make_shlimm_correct:
  forall n r v,
  let (op, args) := make_shlimm n r in
  eval_operation ge sp Oshl (rs#r :: Vint n :: nil) = Some v ->
  eval_operation ge sp op rs##args = Some v.
Proof.
  intros; unfold make_shlimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.shl_zero. congruence.
  simpl in *. auto.
Qed.

Lemma make_shrimm_correct:
  forall n r v,
  let (op, args) := make_shrimm n r in
  eval_operation ge sp Oshr (rs#r :: Vint n :: nil) = Some v ->
  eval_operation ge sp op rs##args = Some v.
Proof.
  intros; unfold make_shrimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.shr_zero. congruence.
  assumption.
Qed.

Lemma make_shruimm_correct:
  forall n r v,
  let (op, args) := make_shruimm n r in
  eval_operation ge sp Oshru (rs#r :: Vint n :: nil) = Some v ->
  eval_operation ge sp op rs##args = Some v.
Proof.
  intros; unfold make_shruimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.shru_zero. congruence.
  assumption.
Qed.

Lemma make_mulimm_correct:
  forall n r v,
  let (op, args) := make_mulimm n r in
  eval_operation ge sp Omul (rs#r :: Vint n :: nil) = Some v ->
  eval_operation ge sp op rs##args = Some v.
Proof.
  intros; unfold make_mulimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in H0. FuncInv. rewrite Int.mul_zero. simpl. congruence.
  generalize (Int.eq_spec n Int.one); case (Int.eq n Int.one); intros.
  subst n. simpl in H1. simpl. FuncInv. rewrite Int.mul_one. congruence.
  caseEq (Int.is_power2 n); intros.
  replace (eval_operation ge sp Omul (rs # r :: Vint n :: nil))
     with (eval_operation ge sp Oshl (rs # r :: Vint i :: nil)).
  apply make_shlimm_correct. 
  simpl. generalize (Int.is_power2_range _ _ H1). 
  unfold Int.iwordsize.
  change (Z_of_nat Int.wordsize) with 32. intro. rewrite H2.
  destruct rs#r; auto. rewrite (Int.mul_pow2 i0 _ _ H1). auto.
  exact H2.
Qed.

Lemma make_andimm_correct:
  forall n r v,
  let (op, args) := make_andimm n r in
  eval_operation ge sp Oand (rs#r :: Vint n :: nil) = Some v ->
  eval_operation ge sp op rs##args = Some v.
Proof.
  intros; unfold make_andimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.and_zero. congruence.
  generalize (Int.eq_spec n Int.mone); case (Int.eq n Int.mone); intros.
  subst n. simpl in *. FuncInv. rewrite Int.and_mone. congruence.
  exact H1.
Qed.

Lemma make_orimm_correct:
  forall n r v,
  let (op, args) := make_orimm n r in
  eval_operation ge sp Oor (rs#r :: Vint n :: nil) = Some v ->
  eval_operation ge sp op rs##args = Some v.
Proof.
  intros; unfold make_orimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.or_zero. congruence.
  generalize (Int.eq_spec n Int.mone); case (Int.eq n Int.mone); intros.
  subst n. simpl in *. FuncInv. rewrite Int.or_mone. congruence.
  exact H1.
Qed.

Lemma make_xorimm_correct:
  forall n r v,
  let (op, args) := make_xorimm n r in
  eval_operation ge sp Oxor (rs#r :: Vint n :: nil) = Some v ->
  eval_operation ge sp op rs##args = Some v.
Proof.
  intros; unfold make_xorimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.xor_zero. congruence.
  exact H0.
Qed.

Lemma op_strength_reduction_correct:
  forall op args v,
  let (op', args') := op_strength_reduction app op args in
  eval_operation ge sp op rs##args = Some v ->
  eval_operation ge sp op' rs##args' = Some v.
Proof.
  intros; unfold op_strength_reduction;
  case (op_strength_reduction_match op args); intros; simpl List.map.
  (* Osub *)
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H).
  unfold make_addimm. generalize (Int.eq_spec (Int.neg i) Int.zero).
  destruct (Int.eq (Int.neg i) (Int.zero)); intros.
  assert (i = Int.zero). rewrite <- (Int.neg_involutive i). rewrite H0. reflexivity.
  subst i. simpl in *. destruct (rs#r1); inv H1; try destruct p; rewrite Int.sub_zero_r; auto.
  simpl in *. destruct (rs#r1); inv H1; try destruct p; rewrite Int.sub_add_opp; auto.
  auto.
  (* Omul *)
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H). apply make_mulimm_correct.
  assumption.
  (* Odiv *)

  caseEq (intval app r2); intros.
  caseEq (Int.is_power2 i); intros.
  caseEq (Int.ltu i0 (Int.repr 31)); intros.
  rewrite (intval_correct _ _ H) in H2.   
  simpl in *; FuncInv. destruct (Int.eq i Int.zero). congruence.
  rewrite H1. rewrite (Int.divs_pow2 i1 _ _ H0) in H2. auto.
  assumption.
  assumption.
  assumption.
  (* Odivu *)
  caseEq (intval app r2); intros.
  caseEq (Int.is_power2 i); intros.
  rewrite (intval_correct _ _ H).
  replace (eval_operation ge sp Odivu (rs # r1 :: Vint i :: nil))
     with (eval_operation ge sp Oshru (rs # r1 :: Vint i0 :: nil)).
  apply make_shruimm_correct. 
  simpl. destruct rs#r1; auto. replace (Int.repr 32) with (Int.iwordsize) by done.
  rewrite (Int.is_power2_range _ _ H0). 
  generalize (Int.eq_spec i Int.zero); case (Int.eq i Int.zero); intros.
  subst i. discriminate. 
  rewrite (Int.divu_pow2 i1 _ _ H0). auto.
  assumption.
  assumption.
  (* Omodu *)
  caseEq (intval app r2); intros.
  caseEq (Int.is_power2 i); intros.
  rewrite (intval_correct _ _ H) in H1.
  simpl in *; FuncInv. destruct (Int.eq i Int.zero). congruence.
  rewrite (Int.modu_and i1 _ _ H0) in H1. auto.
  assumption.
  assumption.
  (* Oand *)
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H). apply make_andimm_correct.
  assumption.
  (* Oor *)
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H). apply make_orimm_correct.
  assumption.
  (* Oxor *)
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H). apply make_xorimm_correct.
  assumption.
  (* Oshl *)
  caseEq (intval app r2); intros.
  caseEq (Int.ltu i (Int.repr 32)); intros.
  rewrite (intval_correct _ _ H). apply make_shlimm_correct.
  assumption.
  assumption.
  (* Oshr *)
  caseEq (intval app r2); intros.
  caseEq (Int.ltu i (Int.repr 32)); intros.
  rewrite (intval_correct _ _ H). apply make_shrimm_correct.
  assumption.
  assumption.
  (* Oshru *)
  caseEq (intval app r2); intros.
  caseEq (Int.ltu i (Int.repr 32)); intros.
  rewrite (intval_correct _ _ H). apply make_shruimm_correct.
  assumption.
  assumption.
  (* Olea *)
  generalize (addr_strength_reduction_correct addr args0).
  destruct (addr_strength_reduction app addr args0) as [addr' args'].
  intros. simpl in *. congruence.
  (* Ocmp *)
  generalize (cond_strength_reduction_correct c args0).
  destruct (cond_strength_reduction app c args0).
  simpl. intro. rewrite H. auto.
  (* default *)
  assumption.
Qed.

End STRENGTH_REDUCTION.

End ANALYSIS.

