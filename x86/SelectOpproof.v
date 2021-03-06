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

(** Correctness of instruction selection for operators *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Floats.
Require Import Pointers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
(*Require Import Smallstep.*)
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.

Open Local Scope cminorsel_scope.

Section CMCONSTR.

Variable ge: genv.
Variable sp: option Pointers.pointer.
Variable e: env.
(*Variable m: mem. *)

(** * Useful lemmas and tactics *)

(** The following are trivial lemmas and custom tactics that help
  perform backward (inversion) and forward reasoning over the evaluation
  of operator applications. *)  

Ltac EvalOp := (try rewrite <- app_nil_end); eapply eval_Eop; eauto with evalexpr.

Ltac TrivialOp cstr := unfold cstr; intros; EvalOp.

Ltac InvEval1 :=
  match goal with
  | [ H: (eval_expr _ _ _ _ (Eop _ Enil) _) |- _ ] =>
      inv H; InvEval1
  | [ H: (eval_expr _ _ _ _ (Eop _ (_ ::: Enil)) _) |- _ ] =>
      inv H; InvEval1
  | [ H: (eval_expr _ _ _ _ (Eop _ (_ ::: _ ::: Enil)) _) |- _ ] =>
      inv H; InvEval1
  | [ H: (eval_exprlist _ _ _ _ Enil _) |- _ ] =>
      inv H; InvEval1
  | [ H: (eval_exprlist _ _ _ _ (_ ::: _) _) |- _ ] =>
      inv H; InvEval1
  | _ =>
      idtac
  end.

(*
Ltac InvEval2 :=
  match goal with
  | [ H: (eval_operation _ _ _ nil = Some _) |- _ ] =>
      simpl in H; inv H
  | [ H: (eval_operation _ _ _ (_ :: nil) = Some _) |- _ ] =>
      simpl in H; FuncInv
  | [ H: (eval_operation _ _ _ (_ :: _ :: nil) = Some _) |- _ ] =>
      simpl in H; FuncInv
  | [ H: (eval_operation _ _ _ (_ :: _ :: _ :: nil) = Some _) |- _ ] =>
      simpl in H; FuncInv
  | _ =>
      idtac
  end.
*)
(* Ltac InvEval := InvEval1; InvEval2; InvEval2. *)



Ltac FuncInv :=
  match goal with
  | H: (match ?x with nil => _ | _ :: _ => _ end = Some _) |- _ =>
      destruct x; simpl in H; try discriminate; FuncInv
  | H: (match ?v with Vundef => _ | Vint _ => _ | Vfloat _ => _ | Vptr _ => _ end = Some _) |- _ =>
      destruct v as [| | |[]]; simpl in H; try discriminate; FuncInv
  | H: (Some _ = Some _) |- _ =>
      injection H; intros; clear H; FuncInv
  | _ =>
      idtac
  end.
Ltac InvEval2 :=
  match goal with
  | [ H: (eval_operation _ _ _ nil = Some _) |- _ ] =>
      simpl in H; inv H
  | [ H: (eval_operation _ _ _ (_ :: nil) = Some _) |- _ ] =>
      simpl in H; FuncInv
  | [ H: (eval_operation _ _ _ (_ :: _ :: nil) = Some _) |- _ ] =>
      simpl in H; FuncInv
  | [ H: (eval_operation _ _ _ (_ :: _ :: _ :: nil) = Some _) |- _ ] =>
      simpl in H; FuncInv
  | _ =>
      idtac
  end.

Ltac InvEval := InvEval1; InvEval2; InvEval2.


(** * Correctness of the smart constructors *)

(** We now show that the code generated by "smart constructor" functions
  such as [SelectOp.notint] behaves as expected.  Continuing the
  [notint] example, we show that if the expression [e]
  evaluates to some integer value [Vint n], then [SelectOp.notint e]
  evaluates to a value [Vint (Int.not n)] which is indeed the integer
  negation of the value of [e].

  All proofs follow a common pattern:
- Reasoning by case over the result of the classification functions
  (such as [add_match] for integer addition), gathering additional
  information on the shape of the argument expressions in the non-default
  cases.
- Inversion of the evaluations of the arguments, exploiting the additional
  information thus gathered.
- Equational reasoning over the arithmetic operations performed,
  using the lemmas from the [Int] and [Float] modules.
- Construction of an evaluation derivation for the expression returned
  by the smart constructor.
*)

Theorem eval_addrsymbol:
  forall id ofs ofs0 b,
  Genv.find_symbol ge id = Some (Ptr b ofs0) ->
  eval_expr ge sp e nil (addrsymbol id ofs) (Vptr (Ptr b (Int.add ofs0 ofs))).
Proof.
  intros. unfold addrsymbol. econstructor. eapply eval_Enil. 
  simpl. rewrite H. auto.
Qed.

Theorem eval_addrstack:
  forall ofs b n,
  sp = Some (Ptr b n) ->
  eval_expr ge sp e nil (addrstack ofs) (Vptr (Ptr b (Int.add n ofs))).
Proof.
  intros. unfold addrstack. econstructor. constructor. 
  simpl. unfold offset_sp. rewrite H. auto.
Qed.

Lemma eval_notbool_base:
  forall t a v b,
  eval_expr ge sp e t a v ->
  Val.bool_of_val v b ->
  eval_expr ge sp e t (notbool_base a) (Val.of_bool (negb b)).
Proof. 
  TrivialOp notbool_base.  econstructor. eauto. econstructor. rewrite <- app_nil_end. done.
  simpl.
  inv H0. 
  rewrite Int.eq_false; auto.
  rewrite Int.eq_true; auto.
  reflexivity.
Qed.

Hint Resolve Val.bool_of_true_val Val.bool_of_false_val
             Val.bool_of_true_val_inv Val.bool_of_false_val_inv: valboolof.

Theorem eval_notbool:
  forall a v b t,
  eval_expr ge sp e t a v ->
  Val.bool_of_val v b ->
  eval_expr ge sp e t (notbool a) (Val.of_bool (negb b)).
Proof.
  induction a; simpl; intros; try (eapply eval_notbool_base; eauto).
  destruct o; try (eapply eval_notbool_base; eauto).

-  destruct e0. InvEval. 
  inv H0. rewrite Int.eq_false; auto. 
  simpl; eauto with evalexpr.
  rewrite Int.eq_true; simpl; eauto with evalexpr.
  eapply eval_notbool_base; eauto.

-  inv H. eapply eval_Eop; eauto.
  simpl. assert (eval_condition c vl = Some b).
  generalize EVAL. simpl. 
  case (eval_condition c vl); intros.
  destruct b0; inv EVAL0; inversion H0; auto; congruence.
  congruence.
  rewrite (Op.eval_negate_condition _ _ H). 
  destruct b; reflexivity.

-  inv H. eapply eval_Econdition; eauto. 
  destruct vb1; eauto.  
Qed.

Lemma eval_offset_addressing:
  forall addr n args v,
  eval_addressing ge sp addr args = Some v ->
  eval_addressing ge sp (offset_addressing addr n) args = Some (Val.add v (Vint n)).
Proof.
  intros. destruct addr; simpl in *; FuncInv; subst; simpl.
  rewrite Int.add_assoc. auto.
  rewrite Int.add_assoc. auto.
  rewrite <- Int.add_assoc. auto.
  rewrite <- Int.add_assoc. auto.
  rewrite <- Int.add_assoc. auto.
  rewrite <- Int.add_assoc. auto.
  rewrite <- Int.add_assoc. decEq. decEq. repeat rewrite Int.add_assoc. auto.
  decEq. decEq. repeat rewrite Int.add_assoc. auto.

  rewrite <- Int.add_assoc. decEq. decEq. repeat rewrite Int.add_assoc. auto.
  decEq. decEq. repeat rewrite Int.add_assoc. auto.
  destruct (Genv.find_symbol ge i); inv H. auto.  unfold Val.add.  unfold MPtr.add.  destruct p. rewrite Int.add_assoc. done.
  destruct (Genv.find_symbol ge i); inv H. simpl.  unfold MPtr.add. destruct p. 
  repeat rewrite Int.add_assoc. decEq. decEq. decEq.  decEq. decEq.  rewrite Int.add_commut. done.
  destruct (Genv.find_symbol ge i0); inv H. simpl. 
  repeat rewrite Int.add_assoc. decEq. decEq. unfold MPtr.add.  destruct p. decEq.  repeat rewrite Int.add_assoc. decEq.  decEq. apply Int.add_commut. 
  unfold offset_sp in *. destruct sp; inv H. simpl.  unfold MPtr.add.  destruct p. decEq.  decEq.  decEq.  rewrite Int.add_assoc. auto.
Qed.

Theorem eval_addimm:
  forall t n a x,
  eval_expr ge sp e t a (Vint x) ->
  eval_expr ge sp e t (addimm n a) (Vint (Int.add x n)).
Proof.
  unfold addimm; intros until x.
  generalize (Int.eq_spec n Int.zero). case (Int.eq n Int.zero); intro.
  subst n. rewrite Int.add_zero. auto.
  case (addimm_match a); intros; InvEval.
  EvalOp. simpl. rewrite Int.add_commut. auto.
  inv H0. EvalOp. simpl.  rewrite (eval_offset_addressing _ _ _ _ EVAL). auto. 
(*  inv H0. EvalOp. simpl.  unfold eval_operation in EVAL. rewrite (eval_offset_addressing _ _ _ EVAL). auto. *)
  EvalOp.  econstructor. eauto. econstructor. apply app_nil_end.  unfold eval_operation.  unfold eval_addressing.  done.
Qed. 
                             
Theorem eval_addimm_ptr:
  forall t n a b ofs,
  eval_expr ge sp e t a (Vptr (Ptr b ofs)) ->
  eval_expr ge sp e t (addimm n a) (Vptr (Ptr b (Int.add ofs n))).
Proof.
  unfold addimm; intros until ofs.
  generalize (Int.eq_spec n Int.zero). case (Int.eq n Int.zero); intro.
  subst n. rewrite Int.add_zero. auto.
  case (addimm_match a); intros; InvEval.
(*  inv H0. EvalOp. simpl.  unfold eval_operation in EVAL. rewrite (eval_offset_addressing _ _ _ EVAL). auto. *)
  inv H0. EvalOp. simpl.  rewrite (eval_offset_addressing _ _ _ _ EVAL). auto. 
  EvalOp.  econstructor.  eauto. econstructor.  by rewrite <- app_nil_end.  auto.
Qed.

Theorem eval_add:
  forall ta tb a b x y,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vint y) ->
  eval_expr ge sp e (ta++tb) (add a b) (Vint (Int.add x y)).
Proof.
  intros until y.
  unfold add; case (add_match a b); intros; InvEval.
- rewrite Int.add_commut. apply eval_addimm. auto.
- apply eval_addimm. rewrite <- app_nil_end. auto.
- subst. (* rewrite <- app_nil_end.*)  EvalOp.   simpl. decEq. decEq. repeat rewrite Int.add_assoc. decEq. apply Int.add_permut.
  subst. EvalOp. simpl. decEq. decEq. repeat rewrite Int.add_assoc. decEq. apply Int.add_permut.

  subst. EvalOp. simpl. decEq. decEq. rewrite Int.add_commut. repeat rewrite Int.add_assoc.  decEq. decEq. apply Int.add_commut.

(*  subst. EvalOp.    econstructor.  eauto.  econstructor.  eauto.  econstructor.  eauto. simpl.  simpl. decEq. decEq.
    rewrite Int.add_permut. rewrite Int.add_assoc. decEq. apply Int.add_permut.*)
  destruct (Genv.find_symbol ge id); inv H0.
  destruct (Genv.find_symbol ge id); inv H0.
  destruct (Genv.find_symbol ge id); inv H0.
  destruct (Genv.find_symbol ge id); inv H0.
  subst. EvalOp. econstructor.   eauto.  econstructor.  eauto.  econstructor. simpl. eauto. rewrite <- app_nil_end.  auto.  (*rewrite Int.add_commut. auto.*)
  unfold eval_operation.  unfold eval_addressing. rewrite Int.add_commut. auto.
  subst. EvalOp. econstructor. eauto. econstructor. eauto.  econstructor.  eauto. rewrite <-app_nil_end.  done.  unfold eval_addressing. unfold eval_operation. auto.
  subst. EvalOp. econstructor.  eauto.  econstructor.  eauto.  econstructor.  auto.  rewrite <-app_nil_end.  done. simpl. decEq. decEq. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  subst. EvalOp. econstructor.  eauto.  econstructor.  eauto.  econstructor.  auto.  rewrite <-app_nil_end.  done. simpl. decEq. decEq. apply Int.add_assoc.
  EvalOp. econstructor.  eauto.  econstructor.  eauto.  econstructor.  auto.  rewrite <-app_nil_end.  done. simpl.  rewrite Int.add_zero. auto.
Qed.

Theorem eval_add_ptr:
  forall ta tb a b p x y,
  eval_expr ge sp e ta a (Vptr (Ptr p x)) ->
  eval_expr ge sp e tb b (Vint y) ->
  eval_expr ge sp e (ta++tb) (add a b) (Vptr (Ptr p (Int.add x y))).
Proof.
  intros until y. unfold add; case (add_match a b); intros; InvEval.
  apply eval_addimm_ptr; auto.
  subst. rewrite <- app_nil_end. done. 
  subst. EvalOp; simpl. decEq. decEq. repeat rewrite Int.add_assoc. decEq. decEq. apply Int.add_permut.
  subst. EvalOp; simpl. decEq. decEq. repeat rewrite Int.add_assoc. decEq. decEq. apply Int.add_permut.
  destruct (Genv.find_symbol ge id); inv H0.
  subst. EvalOp; simpl. econstructor.  eauto.  econstructor. by rewrite <- app_nil_end. simpl. destruct (Genv.find_symbol ge id); inv H0.  decEq.  decEq.  unfold MPtr.add. destruct p0.   unfold MPtr.add in H1.  clarify.  
  decEq. rewrite Int.add_assoc. rewrite Int.add_assoc. decEq.  decEq. apply Int.add_commut.
  subst. simpl.   rewrite <- app_nil_end. EvalOp. econstructor.  eauto.  econstructor.  by rewrite <-app_nil_end. (* destruct (Genv.find_symbol ge id); inv H0.*)  unfold eval_operation.    unfold eval_addressing. destruct (Genv.find_symbol ge id); inv H0. unfold MPtr.add. destruct p0.   unfold MPtr.add in H1.  clarify.  
  decEq. decEq.  decEq. repeat rewrite Int.add_assoc. decEq. decEq. apply Int.add_commut.
  subst. econstructor.  econstructor.  eauto.  econstructor.  eauto.  econstructor. auto. auto. econstructor. 
  subst. EvalOp; simpl. econstructor. eauto.  econstructor.  eauto.  econstructor.  eauto. by rewrite <-app_nil_end. simpl.  decEq. decEq. decEq. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  subst. EvalOp; simpl. econstructor. eauto.  econstructor.  eauto.  econstructor.  eauto.  by rewrite <-app_nil_end.  simpl. decEq. decEq. decEq. repeat rewrite Int.add_assoc. auto.
  EvalOp; simpl. econstructor.  eauto. econstructor.  eauto.  econstructor.  eauto.  by rewrite <-app_nil_end.  simpl. rewrite Int.add_zero. auto.
Qed.

Theorem eval_add_ptr_2:
  forall ta tb a b x p y,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vptr (Ptr p y)) ->
  eval_expr ge sp e (ta++tb) (add a b) (Vptr (Ptr p (Int.add y x))).
Proof.
  intros until y. unfold add; case (add_match a b); intros; InvEval.
  apply eval_addimm_ptr; auto.
  subst. EvalOp; simpl. decEq. decEq. repeat rewrite Int.add_assoc. decEq.
    rewrite (Int.add_commut n1 n2). decEq. apply Int.add_permut.
  subst. EvalOp; simpl. decEq. decEq. repeat rewrite Int.add_assoc. decEq. decEq. 
    rewrite (Int.add_commut n1 n2). apply Int.add_permut.
  subst. EvalOp; simpl. destruct (Genv.find_symbol ge id); inv H0. 
  decEq. decEq. unfold MPtr.add.  destruct p0.  unfold MPtr.add in H1. clarify. decEq. repeat rewrite Int.add_assoc. decEq.  decEq. apply Int.add_commut.
  destruct (Genv.find_symbol ge id); inv H0. 
  subst. EvalOp; simpl. destruct (Genv.find_symbol ge id); inv H0. 
  decEq. decEq. unfold MPtr.add in *.   destruct p0.  clarify. repeat rewrite Int.add_assoc.  decEq. decEq.  decEq. apply Int.add_commut.
  subst. EvalOp.  econstructor. eauto. econstructor. eauto.  econstructor.  auto. by rewrite<-app_nil_end. simpl. done.
  subst. EvalOp; simpl.  econstructor. eauto. econstructor. eauto.  econstructor.  auto. by rewrite<-app_nil_end. simpl. decEq. decEq.  decEq. repeat rewrite Int.add_assoc. auto.
  subst. EvalOp; simpl.  econstructor. eauto. econstructor. eauto.  econstructor.  auto. by rewrite<-app_nil_end. simpl.  decEq. decEq. decEq. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  EvalOp; simpl.   econstructor. eauto. econstructor. eauto.  econstructor.  auto. by rewrite<-app_nil_end. simpl.  rewrite Int.add_zero. auto.
Qed.


Ltac EvalOp2 := 
  (repeat rewrite <- app_nil_end);
  eapply eval_Eop;
    try match goal with 
          |  |- eval_exprlist _ _ _ _ (_ ::: _ ::: Enil) _ => 
            econstructor; eauto; econstructor;  eauto; try econstructor; 
              (try repeat rewrite <- app_nil_end);   try simpl
        end;
    auto.   

Theorem eval_sub:
  forall ta tb a b x y,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vint y) ->
  eval_expr ge sp e (ta++tb) (sub a b) (Vint (Int.sub x y)).
Proof.
  intros until y.
  unfold sub; case (sub_match a b); intros; InvEval.
-  rewrite Int.sub_add_opp. 
    apply eval_addimm.  rewrite <- app_nil_end. assumption.
-  replace (Int.sub x y) with (Int.add (Int.sub i0 i) (Int.sub n1 n2)).
    apply eval_addimm. EvalOp2. 
    subst x; subst y.
    repeat rewrite Int.sub_add_opp.
    repeat rewrite Int.add_assoc. decEq. 
    rewrite Int.add_permut. decEq. symmetry. apply Int.neg_add_distr.
-  replace (Int.sub x y) with (Int.add (Int.sub i y) n1).
    apply eval_addimm. EvalOp2.
    subst x. rewrite Int.sub_add_l. auto.
-  replace (Int.sub x y) with (Int.add (Int.sub x i) (Int.neg n2)).
    apply eval_addimm. EvalOp2.
    subst y. rewrite (Int.add_commut i n2). symmetry. apply Int.sub_add_r. 
-  EvalOp2.
Qed.

Theorem eval_sub_ptr_int:
  forall ta tb a b p x y,
  eval_expr ge sp e ta a (Vptr (Ptr p x)) ->
  eval_expr ge sp e tb b (Vint y) ->
  eval_expr ge sp e (ta++tb) (sub a b) (Vptr (Ptr p (Int.sub x y))).
Proof.
  intros until y.
  unfold sub; case (sub_match a b); intros; InvEval.
  rewrite Int.sub_add_opp. 
    apply eval_addimm_ptr. rewrite <- app_nil_end. assumption.
  subst z. replace (Int.sub x y) with (Int.add (Int.sub i0 i) (Int.sub n1 n2)).
    apply eval_addimm_ptr. EvalOp2.
    subst x; subst y.
    repeat rewrite Int.sub_add_opp.
    repeat rewrite Int.add_assoc. decEq. 
    rewrite Int.add_permut. decEq. symmetry. apply Int.neg_add_distr.
  subst z. replace (Int.sub x y) with (Int.add (Int.sub i y) n1).
    apply eval_addimm_ptr. EvalOp2.
    subst x. rewrite Int.sub_add_l. auto.
  replace (Int.sub x y) with (Int.add (Int.sub x i) (Int.neg n2)).
    apply eval_addimm_ptr. EvalOp2.
    subst y. rewrite (Int.add_commut i n2). symmetry. apply Int.sub_add_r. 
  EvalOp2.
Qed.

Theorem eval_sub_ptr_ptr:
  forall ta tb a b p x y,
  eval_expr ge sp e ta a (Vptr (Ptr p x)) ->
  eval_expr ge sp e tb b (Vptr (Ptr p y)) ->
  eval_expr ge sp e (ta++tb) (sub a b) (Vint (Int.sub x y)).
Proof.
  intros until y.
  unfold sub; case (sub_match a b); intros; InvEval.
  replace (Int.sub x y) with (Int.add (Int.sub i0 i) (Int.sub n1 n2)).
    apply eval_addimm. EvalOp2. 
    simpl; unfold Z_eq_dec. (*eq_block.*) subst z0; subst z; rewrite zeq_true. auto.
    subst x; subst y.
    repeat rewrite Int.sub_add_opp.
    repeat rewrite Int.add_assoc. decEq. 
    rewrite Int.add_permut. decEq. symmetry. apply Int.neg_add_distr.
  subst z. replace (Int.sub x y) with (Int.add (Int.sub i y) n1).
    apply eval_addimm. EvalOp2.
    simpl. unfold Z_eq_dec. rewrite zeq_true. auto.
    subst x. rewrite Int.sub_add_l. auto.
  subst z. replace (Int.sub x y) with (Int.add (Int.sub x i) (Int.neg n2)).
    apply eval_addimm. EvalOp2.
    simpl. unfold Z_eq_dec. rewrite zeq_true. auto.
    subst y. rewrite (Int.add_commut i n2). symmetry. apply Int.sub_add_r. 
  EvalOp2. simpl. unfold Z_eq_dec. rewrite zeq_true. auto.
Qed.

Definition Int_iwordsize := Int.repr ( 32).

Ltac EvalOp1 := 
  (repeat rewrite <- app_nil_end);
  eapply eval_Eop;
    try match goal with 
          |  |- eval_exprlist _ _ _ _ (_ ::: Enil) _ => 
            econstructor;  eauto; try econstructor; 
              (try rewrite <- app_nil_end); (try rewrite <- app_nil_end); (try rewrite <- app_nil_end);   try simpl
        end;
    auto.   


Theorem eval_shlimm:
  forall t a n x,
  eval_expr ge sp e t a (Vint x) ->
  Int.ltu n Int_iwordsize = true ->
  eval_expr ge sp e t (shlimm a n) (Vint (Int.shl x n)).
Proof.
  intros until x; unfold shlimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero).
  intros. subst n. rewrite Int.shl_zero. auto.
  case (shlimm_match a); intros. 
  InvEval. EvalOp. 
  case_eq (Int.ltu (Int.add n n1) (Int.repr 32) (*Int_iwordsize*)); intros.
  InvEval. revert EVAL. case_eq (Int.ltu n1 (Int.repr 32) (*Int_iwordsize*)); intros;  inv EVAL. 
  EvalOp1. simpl.  rewrite H2. rewrite Int.shl_shl; auto; rewrite Int.add_commut; auto. 
  EvalOp1. simpl. unfold Int_iwordsize in*. rewrite H1; auto.
  InvEval. subst. 
  destruct (shift_is_scale n). 
  EvalOp1. simpl. decEq. decEq.
  rewrite (Int.shl_mul (Int.add i n1)); auto. rewrite (Int.shl_mul n1); auto.
  rewrite Int.mul_add_distr_l. auto.

  econstructor.  econstructor. econstructor.    econstructor.  eauto.  econstructor.  eauto.  eauto.  econstructor.  econstructor.  repeat rewrite <- app_nil_end. done.  unfold Int_iwordsize in *. unfold eval_operation.  rewrite H1.  auto. 
(*  EvalOp.  econstructor. EvalOp. simpl. eauto. constructor. simpl. rewrite H1. auto.*)
  destruct (shift_is_scale n).
  EvalOp1. simpl. decEq. decEq.
  rewrite Int.add_zero. symmetry. apply Int.shl_mul. unfold Int_iwordsize in *.  
  EvalOp1. simpl. rewrite H1; auto.
Qed.


Theorem eval_shruimm:
  forall t a n x,
  eval_expr ge sp e t a (Vint x) ->
  Int.ltu n Int_iwordsize = true ->
  eval_expr ge sp e t (shruimm a n) (Vint (Int.shru x n)).
Proof.
  intros until x; unfold shruimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero).
  intros. subst n. rewrite Int.shru_zero. auto.
  case (shruimm_match a); intros. 
  InvEval. EvalOp. 
  unfold Int_iwordsize in *. case_eq (Int.ltu (Int.add n n1) Int_iwordsize); intros.   
  InvEval. revert EVAL. case_eq (Int.ltu n1 (Int.repr 32)(*Int_iwordsize*)); intros. inv EVAL. unfold Int_iwordsize in *. rewrite H2.  rewrite <- app_nil_end. econstructor.   econstructor.  eauto.  econstructor.  rewrite <- app_nil_end.  done. unfold eval_operation.  rewrite H2.  rewrite Int.shru_shru. decEq. decEq. decEq. rewrite Int.add_commut. done.  unfold Int.wordsize. clarify. unfold Int.wordsize.  clarify.  unfold Int.wordsize.  rewrite Int.add_commut. clarify.

discriminate. 
unfold Int_iwordsize in *. rewrite H2.   EvalOp1. simpl. rewrite H1; auto. 
unfold Int_iwordsize in *. EvalOp1. simpl. rewrite H1; auto.
Qed.

Theorem eval_shrimm:
  forall t a n x,
  eval_expr ge sp e t a (Vint x) ->
  Int.ltu n Int_iwordsize = true ->
  eval_expr ge sp e t (shrimm a n) (Vint (Int.shr x n)).
Proof.
  intros until x; unfold shrimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero).
  intros. subst n. rewrite Int.shr_zero. auto.
  case (shrimm_match a); intros. 
  InvEval. EvalOp1.  econstructor.  auto. 
  case_eq (Int.ltu (Int.add n n1) Int_iwordsize); intros.
  InvEval. revert EVAL. case_eq (Int.ltu n1 (Int.repr 32) (*Int_iwordsize*)); intros; inv EVAL.
  unfold Int_iwordsize in *. rewrite H2. EvalOp1. simpl. rewrite H2. rewrite Int.shr_shr; auto; rewrite Int.add_commut; auto.
  unfold Int_iwordsize in *. rewrite H2. EvalOp1. simpl. rewrite H1; auto. 
  unfold Int_iwordsize in *.  EvalOp1. simpl. rewrite H1; auto.
Qed.

Lemma eval_mulimm_base:
  forall t a n x,
  eval_expr ge sp e t a (Vint x) ->
  eval_expr ge sp e t (mulimm_base n a) (Vint (Int.mul x n)).
Proof.
  intros; unfold mulimm_base.
  generalize (Int.one_bits_decomp n). 
  generalize (Int.one_bits_range n).
  destruct (Int.one_bits n).
  intros. EvalOp1. 
  destruct l.
  intros. rewrite H1. simpl. 
  rewrite Int.add_zero. rewrite <- Int.shl_mul.
  apply eval_shlimm. auto. auto with coqlib. 
  destruct l.
  intros.  EvalOp1. 
  intros.  EvalOp1.
(*auto. apply eval_Ediscard with (Vint x). auto. 
  rewrite H1. simpl. rewrite Int.add_zero. 
  rewrite Int.mul_add_distr_r.
  apply eval_add. 
  rewrite <- Int.shl_mul. apply eval_shlimm. constructor. auto. auto with coqlib.
  rewrite <- Int.shl_mul. apply eval_shlimm. constructor. auto. auto with coqlib.
  intros. EvalOp1. *)
Qed.

Theorem eval_mulimm:
  forall t a n x,
  eval_expr ge sp e t a (Vint x) ->
  eval_expr ge sp e t (mulimm n a) (Vint (Int.mul x n)).
Proof.
  intros until x; unfold mulimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intro.
  subst n. rewrite Int.mul_zero. intros.    econstructor.  edone. econstructor. econstructor. auto. rewrite <- app_nil_end.  done. 

  generalize (Int.eq_spec n Int.one); case (Int.eq n Int.one); intro.
  subst n. rewrite Int.mul_one. auto.
  case (mulimm_match a); intros; InvEval. 
  (*EvalOp1.*) econstructor.   econstructor.  rewrite Int.mul_commut. auto. 

  subst. rewrite Int.mul_add_distr_l. 
  rewrite (Int.mul_commut n n2). apply eval_addimm. apply eval_mulimm_base. rewrite <- app_nil_end.  auto.
  apply eval_mulimm_base. assumption.
Qed.

Theorem eval_mul:
  forall ta tb a b x y,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vint y) ->
  eval_expr ge sp e (ta++tb) (mul a b) (Vint (Int.mul x y)).
Proof.
  intros until y.
  unfold mul; case (mul_match a b); intros; InvEval.
  rewrite Int.mul_commut. apply eval_mulimm. auto. 
  apply eval_mulimm. auto. rewrite <- app_nil_end.  assumption.
  EvalOp2.
Qed.

Lemma eval_orimm:
  forall t n a x,
  eval_expr ge sp e t a (Vint x) ->
  eval_expr ge sp e t (orimm n a) (Vint (Int.or x n)).
Proof.
  intros. unfold orimm. 
  predSpec Int.eq Int.eq_spec n Int.zero.
  subst n. rewrite Int.or_zero. auto.
  predSpec Int.eq Int.eq_spec n Int.mone.
  subst n. rewrite Int.or_mone.  (*EvalOp. *) econstructor.  edone. econstructor.  econstructor. edone.  rewrite <- app_nil_end. done. 
  EvalOp1.
Qed.

Remark eval_same_expr:
  forall t1 t2 a1 a2 v1 v2,
  same_expr_pure a1 a2 = true ->
  eval_expr ge sp e t1 a1 v1 ->
  eval_expr ge sp e t2 a2 v2 ->
  t1 = t2 /\ a1 = a2 /\ v1 = v2.
Proof.
  intros until v2.
  destruct a1; simpl; try (intros; discriminate). 
  destruct a2; simpl; try (intros; discriminate).
  case (ident_eq i i0); intros.
  subst i0. inversion H0. inversion H1. split. done.  split. auto. congruence. 
  discriminate.
Qed.

Theorem eval_or:
  forall ta tb a x b y,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vint y) ->
  eval_expr ge sp e (ta++tb) (or a b) (Vint (Int.or x y)).
Proof.
  intros until y; unfold or; case (or_match a b); intros; InvEval. simpl.  

  rewrite Int.or_commut. apply eval_orimm; auto.
 rewrite <- app_nil_end.  apply eval_orimm; auto.

  repeat rewrite <- app_nil_end.

  revert EVAL0; case_eq (Int.ltu n1 (Int.repr 32) (*Int.iwordsize*)).  intros.  inv EVAL0.  revert H; case_eq (Int.ltu n2 (Int.repr 32)(*Int.iwordsize*)); intros. rewrite H in *. inv EVAL.  repeat rewrite <- app_nil_end.  econstructor.  econstructor.  econstructor.  econstructor.  eauto. econstructor.  eauto. simpl. rewrite H0.  eauto. econstructor.  econstructor.  econstructor.  eauto. econstructor. eauto. simpl. rewrite H. eauto. econstructor. eauto. by repeat rewrite <- app_nil_end. simpl. done.

rewrite H in EVAL.  discriminate.

intros. discriminate.


econstructor. econstructor. econstructor. econstructor. eauto. econstructor. eauto. simpl. eauto.

econstructor. econstructor. econstructor. eauto. econstructor. eauto. simpl. eauto.
econstructor. eauto. by repeat rewrite <- app_nil_end.
by simpl. 
econstructor.  econstructor. eauto. econstructor. eauto. econstructor.  eauto. by rewrite <- app_nil_end. simpl. done.
Qed.

(*

rewrite H0. eauto. econstructor. econstructor. econstructor. eauto. econstructor. eauto. simpl. rewrite H. rewrite H in EVAL. eauto. 

  caseEq (Int.eq (Int.add n1 n2) (Int.repr 32) (*Int.iwordsize*)
          && same_expr_pure t1 t2); intro.
  destruct (andb_prop _ _ H1). 
  generalize (Int.eq_spec (Int.add n1 n2) (Int.repr 32) (*Int.iwordsize*)).  rewrite H2; intros.
  exploit eval_same_expr; eauto. intros [EQ1 EQ2]. inv EQ1. inv EQ2.
  (*EvalOp.*) econstructor.   econstructor. eauto. econstructor. (* *)  simpl. rewrite H0. rewrite <- Int.or_ror; auto.
  EvalOp. econstructor. EvalOp. simpl. rewrite H; eauto.
  econstructor. EvalOp. simpl. rewrite H0; eauto. constructor.
  simpl. auto.

  revert H7; case_eq (Int.ltu n2 Int.iwordsize); intros; inv H7.
  revert H6; case_eq (Int.ltu n1 Int.iwordsize); intros; inv H6.
  caseEq (Int.eq (Int.add n1 n2) Int.iwordsize
          && same_expr_pure t1 t2); intro.
  destruct (andb_prop _ _ H1).
  generalize (Int.eq_spec (Int.add n1 n2) Int.iwordsize); rewrite H4; intros.
  exploit eval_same_expr; eauto. intros [EQ1 EQ2]. inv EQ1. inv EQ2.
  EvalOp. simpl. rewrite H. rewrite Int.or_commut. rewrite <- Int.or_ror; auto.
  EvalOp. econstructor. EvalOp. simpl. rewrite H; eauto.
  econstructor. EvalOp. simpl. rewrite H0; eauto. constructor.
  simpl. auto.

  EvalOp.

--------------


  intros until y; unfold or; case (or_match a b); intros; InvEval.

  rewrite Int.or_commut. apply eval_orimm; auto.
  apply eval_orimm; auto.

  rewrite <- app_nil_end; assumption. 

  revert EVAL; case_eq (Int.ltu n1 Int_iwordsize); intros.  unfold Int_iwordsize in *. rewrite H in EVAL0. inv EVAL0. repeat rewrite <- app_nil_end.
  revert EE1; case_eq (Int.ltu n2 Int_iwordsize); intros; inv H6.
  caseEq (Int.eq (Int.add n1 n2) Int_iwordsize
          && same_expr_pure t1 t2); intro.
  destruct (andb_prop _ _ H1).
  generalize (Int.eq_spec (Int.add n1 n2) Int_iwordsize); rewrite H4; intros.
  exploit eval_same_expr; eauto. intros [EQ1 EQ2]. inv EQ1. inv EQ2.
  EvalOp. simpl. rewrite H0. rewrite <- Int.or_ror; auto.
  EvalOp. econstructor. EvalOp. simpl. rewrite H; eauto.
  econstructor. EvalOp. simpl. rewrite H0; eauto. constructor.
  simpl. auto.

  revert H7; case_eq (Int.ltu n2 Int_iwordsize); intros; inv H7.
  revert H6; case_eq (Int.ltu n1 Int_iwordsize); intros; inv H6.
  caseEq (Int.eq (Int.add n1 n2) Int_iwordsize
          && same_expr_pure t1 t2); intro.
  destruct (andb_prop _ _ H1).
  generalize (Int.eq_spec (Int.add n1 n2) Int_iwordsize); rewrite H4; intros.
  exploit eval_same_expr; eauto. intros [EQ1 EQ2]. inv EQ1. inv EQ2.
  EvalOp. simpl. rewrite H. rewrite Int.or_commut. rewrite <- Int.or_ror; auto.
  EvalOp. econstructor. EvalOp. simpl. rewrite H; eauto.
  econstructor. EvalOp. simpl. rewrite H0; eauto. constructor.
  simpl. auto.

  EvalOp.
Qed.
*)

Lemma eval_andimm:
  forall t n a x,
  eval_expr ge sp e t a (Vint x) ->
  eval_expr ge sp e t (andimm n a) (Vint (Int.and x n)).
Proof.
  intros. unfold andimm. 
  predSpec Int.eq Int.eq_spec n Int.zero.
  subst n. rewrite Int.and_zero. econstructor.  edone.  econstructor.  econstructor. edone. rewrite <- app_nil_end. done.
  predSpec Int.eq Int.eq_spec n Int.mone.
  subst n. rewrite Int.and_mone. auto.
  EvalOp1.
Qed.

Theorem eval_and:
  forall ta tb a x b y,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vint y) ->
  eval_expr ge sp e (ta++tb) (and a b) (Vint (Int.and x y)).
Proof.
  intros until y; unfold and. case (mul_match a b); intros.
  InvEval. rewrite Int.and_commut. apply eval_andimm; auto.
  InvEval. apply eval_andimm.  rewrite <- app_nil_end. auto. 
  EvalOp2.
Qed.

Lemma eval_xorimm:
  forall t n a x,
  eval_expr ge sp e t a (Vint x) ->
  eval_expr ge sp e t (xorimm n a) (Vint (Int.xor x n)).
Proof.
  intros. unfold xorimm. 
  predSpec Int.eq Int.eq_spec n Int.zero.
  subst n. rewrite Int.xor_zero. auto.
  EvalOp1.
Qed.

Theorem eval_xor:
  forall ta tb a x b y,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vint y) ->
  eval_expr ge sp e (ta++tb) (xor a b) (Vint (Int.xor x y)).
Proof.
  intros until y; unfold xor. case (mul_match a b); intros.
  InvEval. rewrite Int.xor_commut. apply eval_xorimm; auto.
  InvEval. apply eval_xorimm; rewrite <- app_nil_end; auto.
  EvalOp2.
Qed.

Theorem eval_divu:
  forall ta tb a x b y,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp e (ta++tb) (divu a b) (Vint (Int.divu x y)).
Proof.
  intros; unfold divu; EvalOp2.
  simpl.  rewrite Int.eq_false; auto. 
Qed.

Theorem eval_modu:
  forall ta tb a x b y,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp e (ta++tb) (modu a b) (Vint (Int.modu x y)).
Proof.
  intros; unfold modu; EvalOp2.
  simpl. rewrite Int.eq_false; auto. 
Qed.

Lemma eqz: forall y,  y = Int.zero -> Int.eq y Int.zero = true. 
Proof. 
  intros. subst. auto.  
Qed.

Lemma neqz: forall y,  y <> Int.zero -> Int.eq y Int.zero = false. 
Proof. 
  intros.
  assert (if Int.eq y Int.zero then y=Int.zero else y <> Int.zero). 
  eapply Int.eq_spec.
  destruct (Int.eq y Int.zero). clarify. auto.
Qed.

Theorem eval_divs:
  forall ta tb a b x y,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp e (ta++tb) (divs a b) (Vint (Int.divs x y)).
Proof.
  TrivialOp divs. simpl. 
  predSpec Int.eq Int.eq_spec y Int.zero. contradiction.    econstructor.  eauto.  econstructor.  eauto.  econstructor.  eauto. by rewrite <- app_nil_end.    unfold eval_operation.

 assert (Int.eq y Int.zero = false).  by apply neqz.  rewrite H2.  eauto. 
Qed.

Theorem eval_mods:
  forall ta tb a b x y,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp e (ta++tb) (mods a b) (Vint (Int.mods x y)).
Proof.
  TrivialOp mods. simpl. 
  predSpec Int.eq Int.eq_spec y Int.zero. contradiction. econstructor.   eauto.  econstructor.  eauto.  econstructor. eauto.   rewrite <- app_nil_end.  done. unfold eval_operation. assert (Int.eq y Int.zero = false).  apply neqz.  auto.  rewrite H2. auto.
Qed.

Theorem eval_shl:
  forall ta tb a x b y,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vint y) ->
  Int.ltu y Int_iwordsize = true ->
  eval_expr ge sp e (ta++tb) (shl a b) (Vint (Int.shl x y)).
Proof.
  intros until y; unfold shl; case (shift_match b); intros.
  InvEval. apply eval_shlimm; auto. rewrite <- app_nil_end. auto.
  EvalOp2. unfold Int_iwordsize in *. simpl.  rewrite H1. auto.
Qed.

Theorem eval_shru:
  forall ta tb a x b y,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vint y) ->
  Int.ltu y Int_iwordsize = true ->
  eval_expr ge sp e (ta++tb) (shru a b) (Vint (Int.shru x y)).
Proof.
  intros until y; unfold shru; case (shift_match b); intros.
  InvEval. apply eval_shruimm; auto. rewrite <- app_nil_end. auto.
  EvalOp2. unfold Int_iwordsize in *. simpl. rewrite H1. auto.
Qed.

Theorem eval_shr:
  forall ta tb a x b y,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vint y) ->
  Int.ltu y Int_iwordsize = true ->
  eval_expr ge sp e (ta++tb) (shr a b) (Vint (Int.shr x y)).
Proof.
  intros until y; unfold shr; case (shift_match b); intros.
  InvEval. apply eval_shrimm; auto. rewrite <- app_nil_end. auto.
  EvalOp2. unfold Int_iwordsize in *. simpl. rewrite H1. auto.
Qed.

Theorem eval_comp_int:
  forall ta tb c a x b y,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vint y) ->
  eval_expr ge sp e (ta++tb) (comp c a b) (Val.of_bool(Int.cmp c x y)).
Proof.
  intros until y.
  unfold comp; case (comp_match a b); intros; InvEval; simpl.
  EvalOp. econstructor.   eauto.  econstructor.  by rewrite <- app_nil_end. simpl. rewrite Int.swap_cmp. destruct (Int.cmp c x y); reflexivity.  
  EvalOp. econstructor.   eauto.  econstructor.  by rewrite <- app_nil_end.  simpl. destruct (Int.cmp c x y); reflexivity.
  EvalOp. econstructor.   eauto.  econstructor.  eauto.  econstructor.  rewrite <- app_nil_end.  eauto.  by repeat rewrite <- app_nil_end. simpl. destruct (Int.cmp c x y); reflexivity.
Qed.


Remark eval_compare_null_transf:
  forall c x v,
  Cminor.eval_compare_null c x = Some v ->
  match eval_compare_null c x with
  | Some true => Some Vtrue
  | Some false => Some Vfalse
  | None => None (A:=val)
  end = Some v.
Proof.
  unfold Cminor.eval_compare_null, eval_compare_null, Cminor.eval_compare_null,Cminorops.eval_compare_null; intros.
  destruct (Int.eq x Int.zero); try discriminate. 
  destruct c; try discriminate; auto.
Qed.

Theorem eval_comp_ptr_int:
  forall ta tb c a x1 x2 b y v,
  eval_expr ge sp e ta a (Vptr (Ptr x1 x2)) ->
  eval_expr ge sp e tb b (Vint y) ->
  Cminor.eval_compare_null c y = Some v ->
  eval_expr ge sp e (ta++tb) (comp c a b) v.
Proof.
  intros until v.
  unfold comp; case (comp_match a b); intros; InvEval.
  (*EvalOp2.*) rewrite <- app_nil_end.   econstructor.  econstructor. edone.  econstructor.  by rewrite <- app_nil_end.    simpl. apply eval_compare_null_transf; auto.
  EvalOp2. simpl. apply eval_compare_null_transf; auto.
Qed.

Remark eval_compare_null_swap:
  forall c x,
  Cminor.eval_compare_null (swap_comparison c) x = 
  Cminor.eval_compare_null c x.
Proof.
  intros. unfold Cminor.eval_compare_null,Cminorops.eval_compare_null. 
  destruct (Int.eq x Int.zero). destruct c; auto. auto.
Qed.

Theorem eval_comp_int_ptr:
  forall ta tb c a x b y1 y2 v,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vptr (Ptr y1 y2)) ->
  Cminor.eval_compare_null c x = Some v ->
  eval_expr ge sp e (ta++tb) (comp c a b) v.
Proof.
  intros until v.
  unfold comp; case (comp_match a b); intros; InvEval.
   simpl.   econstructor.  econstructor. edone.  econstructor.  by rewrite <- app_nil_end.  simpl. apply eval_compare_null_transf. 
  rewrite eval_compare_null_swap; auto.
  EvalOp2. simpl. apply eval_compare_null_transf. auto.
Qed.
(*
Theorem eval_comp_ptr_ptr:
  forall ta tb c a x1 x2 b y1 y2,
  eval_expr ge sp e ta a (Vptr (Ptr x1 x2)) ->
  eval_expr ge sp e tb b (Vptr (Ptr y1 y2)) ->
  x1 = y1 ->
  eval_expr ge sp e (ta++tb) (comp c a b) (Val.of_bool(Int.cmp c x2 y2)).
Proof.
  intros until y2.
  unfold comp; case (comp_match a b); intros; InvEval.
  econstructor. econstructor.   eauto. econstructor. eauto. econstructor.  eauto.  by rewrite <- app_nil_end. simpl. subst y1. rewrite dec_eq_true. 
  destruct (Int.cmp c x2 y2); reflexivity.
Qed.

Theorem eval_comp_ptr_ptr_2:
  forall ta tb c a x1 x2 b y1 y2 v,
  eval_expr ge sp e ta a (Vptr (Ptr x1 x2)) ->
  eval_expr ge sp e tb b (Vptr (Ptr y1 y2)) ->
  x1 <> y1 ->
  Cminor.eval_compare_mismatch c = Some v ->
  eval_expr ge sp e (ta++tb) (comp c a b) v.
Proof.
  intros until y2.
  unfold comp; case (comp_match a b); intros; InvEval.
  EvalOp2. simpl. rewrite dec_eq_false; auto.
  destruct c; simpl in H2; inv H2; auto.
Qed.
*)


Theorem eval_comp_ptr_ptr3:
  forall ta tb c a pa b pb v
  (EE1:eval_expr ge sp e ta a (Vptr pa))
  (EE2:eval_expr ge sp e tb b (Vptr pb))
  (VOB:Val.option_val_of_bool3 (MPtr.cmp c pa pb) = Some v),
  eval_expr ge sp e (ta++tb) (comp c a b) v. 
Proof.
  unfold comp; intros until v.
  case (comp_match a b); intros; InvEval. econstructor.   econstructor.  eauto.  econstructor.  eauto.  econstructor.  eauto.  by rewrite <- app_nil_end. 

  simpl. 
  generalize VOB. destruct (MPtr.cmp c pa pb); simpl; done.
Qed.

Theorem eval_compu:
  forall ta tb c a x b y,
  eval_expr ge sp e ta a (Vint x) ->
  eval_expr ge sp e tb b (Vint y) ->
  eval_expr ge sp e (ta++tb) (compu c a b) (Val.of_bool(Int.cmpu c x y)).
Proof.
  intros until y.
  unfold compu; case (comp_match a b); intros; InvEval.
  simpl. (* EvalOp2.*) econstructor. econstructor. eauto.  econstructor.  by rewrite<- app_nil_end. simpl. rewrite Int.swap_cmpu. destruct (Int.cmpu c x y); reflexivity.
  (*EvalOp2.*)   simpl. (* EvalOp2.*) econstructor. econstructor. eauto.  econstructor.  by rewrite<- app_nil_end. simpl. destruct (Int.cmpu c x y); reflexivity.
  EvalOp2. simpl. destruct (Int.cmpu c x y); reflexivity.
Qed.

Theorem eval_compf:
  forall ta tb c a x b y,
  eval_expr ge sp e ta a (Vfloat x) ->
  eval_expr ge sp e tb b (Vfloat y) ->
  eval_expr ge sp e (ta++tb) (compf c a b) (Val.of_bool(Float.cmp c x y)).
Proof.
  intros. unfold compf. EvalOp2. simpl. 
  destruct (Float.cmp c x y); reflexivity.
Qed.

Theorem eval_cast8signed:
  forall t a v,
  eval_expr ge sp e t a v ->
  eval_expr ge sp e t (cast8signed a) (Val.sign_ext 8 v).
Proof. intros; unfold cast8signed; EvalOp1. Qed.

Theorem eval_cast8unsigned:
  forall t a v,
  eval_expr ge sp e t a v ->
  eval_expr ge sp e t (cast8unsigned a) (Val.zero_ext 8 v).
Proof. intros; unfold cast8unsigned; EvalOp1. Qed.

Theorem eval_cast16signed:
  forall t a v,
  eval_expr ge sp e t a v ->
  eval_expr ge sp e t (cast16signed a) (Val.sign_ext 16 v).
Proof. intros; unfold cast16signed; EvalOp1. Qed.

Theorem eval_cast16unsigned:
  forall t a v,
  eval_expr ge sp e t a v ->
  eval_expr ge sp e t (cast16unsigned a) (Val.zero_ext 16 v).
Proof. intros; unfold cast16unsigned; EvalOp1. Qed.

Theorem eval_singleoffloat:
  forall t a v,
  eval_expr ge sp e t a v ->
  eval_expr ge sp e t (singleoffloat a) (Val.singleoffloat v).
Proof. intros; unfold singleoffloat; EvalOp1. Qed.

Theorem eval_notint:
  forall t a x,
  eval_expr ge sp e t a (Vint x) ->
  eval_expr ge sp e t (notint a) (Vint (Int.xor x Int.mone)).
Proof. intros; unfold notint; EvalOp1. Qed.

Theorem eval_negint:
  forall t a x,
  eval_expr ge sp e t a (Vint x) ->
  eval_expr ge sp e t (negint a) (Vint (Int.neg x)).
Proof. intros; unfold notint; EvalOp1. Qed.

Theorem eval_negf:
  forall t a x,
  eval_expr ge sp e t a (Vfloat x) ->
  eval_expr ge sp e t (negf a) (Vfloat (Float.neg x)).
Proof. intros; unfold negf; EvalOp1. Qed.

Theorem eval_intoffloat:
  forall t a x,
  eval_expr ge sp e t a (Vfloat x) ->
  eval_expr ge sp e t (intoffloat a) (Vint (Float.intoffloat x)).
Proof. intros; unfold intoffloat; EvalOp1. Qed.

Theorem eval_floatofint:
  forall t a x,
  eval_expr ge sp e t a (Vint x) ->
  eval_expr ge sp e t (floatofint a) (Vfloat (Float.floatofint x)).
Proof. intros; unfold floatofint; EvalOp1. Qed.

Theorem eval_addf:
  forall ta tb a x b y,
  eval_expr ge sp e ta a (Vfloat x) ->
  eval_expr ge sp e tb b (Vfloat y) ->
  eval_expr ge sp e (ta++tb) (addf a b) (Vfloat (Float.add x y)).
Proof. intros; unfold addf; EvalOp2. Qed.

Theorem eval_subf:
  forall ta tb a x b y,
  eval_expr ge sp e ta a (Vfloat x) ->
  eval_expr ge sp e tb b (Vfloat y) ->
  eval_expr ge sp e (ta++tb) (subf a b) (Vfloat (Float.sub x y)).
Proof. intros; unfold subf; EvalOp2. Qed.

Theorem eval_mulf:
  forall ta tb a x b y,
  eval_expr ge sp e ta a (Vfloat x) ->
  eval_expr ge sp e tb b (Vfloat y) ->
  eval_expr ge sp e (ta++tb) (mulf a b) (Vfloat (Float.mul x y)).
Proof. intros; unfold mulf; EvalOp2. Qed.

Theorem eval_divf:
  forall ta tb a x b y,
  eval_expr ge sp e ta a (Vfloat x) ->
  eval_expr ge sp e tb b (Vfloat y) ->
  eval_expr ge sp e (ta++tb) (divf a b) (Vfloat (Float.div x y)).
Proof. intros; unfold divf; EvalOp2. Qed.

Theorem eval_intuoffloat:
  forall t a x,
  eval_expr ge sp e t a (Vfloat x) ->
  eval_expr ge sp e t (intuoffloat a) (Vint (Float.intuoffloat x)).
Proof.
  intros. unfold intuoffloat. 
  econstructor. eauto. 
(*
  set (im := Int.repr Integers.half_modulus).  (* CompCert1499 has half_modulus in Int *)
  set (fm := Float.floatofintu im). 
*)
  - econstructor.  eauto.  econstructor.  by rewrite <- app_nil_end. 
  - simpl. auto. 
(* 
  assert (eval_expr ge sp e m (Vfloat x :: le) (Eletvar O) (Vfloat x)).
    constructor. auto. 
  apply eval_Econdition with (v1 := Float.cmp Clt x fm).
  econstructor. constructor. eauto. constructor. EvalOp1. simpl; eauto. constructor.
  simpl. auto.
  caseEq (Float.cmp Clt x fm); intros.
  rewrite Float.intuoffloat_intoffloat_1; auto.
  EvalOp.
  rewrite Float.intuoffloat_intoffloat_2; auto.
  fold im. apply eval_addimm. apply eval_intoffloat. apply eval_subf; auto. EvalOp.
*)
Qed.

Theorem eval_floatofintu:
  forall t a x,
  eval_expr ge sp e t a (Vint x) ->
  eval_expr ge sp e t (floatofintu a) (Vfloat (Float.floatofintu x)).
Proof.
  intros. unfold floatofintu. EvalOp1.
(*
  econstructor. eauto. 
  set (fm := Float.floatofintu Float.ox8000_0000).
  assert (eval_expr ge sp e m (Vint x :: le) (Eletvar O) (Vint x)).
    constructor. auto. 
  apply eval_Econdition with (v1 := Int.ltu x Float.ox8000_0000).
  econstructor. constructor. eauto. constructor.
  simpl. auto.
  caseEq (Int.ltu x Float.ox8000_0000); intros.
  rewrite Float.floatofintu_floatofint_1; auto.
  apply eval_floatofint; auto.
  rewrite Float.floatofintu_floatofint_2; auto.
  fold fm. apply eval_addf. apply eval_floatofint. 
  rewrite Int.sub_add_opp. apply eval_addimm; auto.
  EvalOp.
*)
Qed.

Theorem eval_addressing:
  forall t chunk a v b ofs,
  eval_expr ge sp e t a v ->
  v = Vptr (Ptr b ofs) ->
  match addressing chunk a with (mode, args) =>
    exists vl,
    eval_exprlist ge sp e t args vl /\ 
    eval_addressing ge sp mode vl = Some v
  end.
Proof.
  intros until v. unfold addressing; case (addressing_match a); intros; InvEval.
  inv H. exists vl; auto.
  exists (v :: nil); split. econstructor.  eauto.  econstructor. by rewrite <-  app_nil_end. unfold eval_addressing. clarify.    auto.    rewrite Int.add_zero; auto. 
Qed.

End CMCONSTR.
