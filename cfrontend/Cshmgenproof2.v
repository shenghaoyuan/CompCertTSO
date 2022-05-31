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

(** * Correctness of the C front end, part 2: simulation of binops and casts *)

Require Import Coqlib.
Require Import Libtactics.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Ast.
Require Import Values.
Require Import Events.

Require Import Mem.
Require Import Memcomp.
Require Import Globalenvs.
Require Import Pointers.
Require Import Csyntax.
Require Import Csem.
Require Import Ctyping.
Require Import Cminorops.
Require Import Csharpminor.
Require Import Cshmgen.
Require Import Cshmgenproof1.
Require Import Simulations.

Section CLIGHT_DEFS.

Variable prog: Csyntax.program.
Variable tprog: Csharpminor.program.
Hypothesis WTPROG: wt_program prog.
Hypothesis TRANSL: transl_program prog = OK tprog.

Variables (ge : Clight.cl_sem.(SEM_GE)) (tge : cs_sem.(SEM_GE)).

Let lts := (mklts thread_labels (Clight.step ge)).
Let tlts := (mklts thread_labels (cs_step tge)).

Notation match_states := (match_states prog tge).


Ltac simp_inv X := eby inv X; econstructor; try edone; constructor.

Ltac odone := abstract (solve [done|simpl;omega]).
 
Ltac clarify' :=
  clarify;
  repeat match goal with 
    | H1: ?x = Some _, H2: ?x = None   |- _ => rewrite H2 in H1; clarify
    | H1: ?x = Some _, H2: ?x = Some _ |- _ => rewrite H2 in H1; clarify
  end.

Ltac rewrite_discriminate :=
  match goal with 
   | H : ?a = ?b, H' : ?a = ?c |- _ => rewrite H in H'; discriminate
   | H : ?a = ?b, H' : ?a = ?c \/ ?a = ?d |- _ =>
       rewrite H in H'; destruct H'; discriminate
  end. 

Ltac sim_binop2_simp H2 :=
 try (left; eexists; split;
      try (eapply step_weakstep; simpl); 
      try (eapply StepBinop; inv H2; edone);
      try (eapply match_val; [ edone | done | eassumption ])).

Ltac sim_binop2 v1 v2 H2 :=
 try (destruct v1; destruct v2; try done;
      sim_binop2_simp H2).

Ltac sim_binop2_cmp H1 H2 v1 v2 :=
  unfold cmp in H2; unfold Clight.sem_cmp in H1;  try (destruct classify_cmp; try done);
  try (sim_binop2 v1 v2 H2).

Ltac sim_binop EQ2 WT C :=
  try (left; eexists; split;
       try (eapply step_weakstep; simpl);
       inv EQ2;
       try (eapply StepBinop1);
       try (eapply match_expr; inv WT; try edone; try done);
       try discriminate;
       try (eapply match_EKbinop1; unfold match_binop; 
            try (rewrite C); try reflexivity);
       try (unfold cmp);
       simpl; try rewrite C; try edone).

Ltac sim_binop_logical e1 e2 EQ2 WT C :=
  unfold make_cmp in EQ2;
  try destruct (classify_cmp (typeof e1) (typeof e2)) as []_eqn : C; try done;
  sim_binop EQ2 WT C.

Ltac sim_cast1 WT :=
  left; eexists; split;  
  try (eapply step_weakstep; simpl);
  try eapply StepUnop1;
  eapply match_expr;
     [ edone | done |
       eapply match_EKcast; [ edone | edone | done ] |
       inv WT; done | done ].

Ltac sim_cast1_measure e t WT :=
  right; split; [|split]; try done;
  destruct e; try done; 
    [try destruct e; simpl; omega
    |try eapply match_expr; try eapply match_EKcast; try edone;
      [by destruct t | |]; inv WT; try edone;
      try by destruct e; try done; destruct t]. 

Ltac sim_cast2 :=
   try ( left; eexists; split;
         try (eapply steptau_weakstep; simpl);
         try (eapply StepUnop; edone);
         try (eapply step_weakstep; simpl);
         try (eapply StepUnop; edone);
         eapply match_val; edone);
   try ( left; eexists; split;
         try (eapply step_weakstep; simpl);
         try (eapply StepUnop; edone);
         eapply match_val; edone).

Lemma Sim_StepBinop1:
  forall
   (st1 : Clight.state)
   (t : thread_event)
   (st2: Clight.state)
   (H : Clight.cl_step ge st1 t st2),
   forall (e1 : Csyntax.expr) (op2 : Csyntax.binary_operation)
          (e2 : Csyntax.expr) (ty : type) (ek : Clight.expr_cont)
          (env : Clight.env) (st1' : state),
   match_states 
      (Clight.SKexpr (Expr (Csyntax.Ebinop op2 e1 e2) ty) env ek)  st1' ->
   (exists st2' : St tlts,
      weakstep tlts st1' TEtau st2' /\
      match_states 
                   (Clight.SKexpr e1 env
                     (Clight.EKbinop1 op2 (typeof e1) (typeof e2) ty e2 ek)) 
                   st2') \/
   (measure
      (Clight.SKexpr e1 env
         (Clight.EKbinop1 op2 (typeof e1) (typeof e2) ty e2 ek)) <
    measure (Clight.SKexpr (Expr (Csyntax.Ebinop op2 e1 e2) ty) env ek))%nat /\
   TEtau = TEtau /\
   match_states 
     (Clight.SKexpr e1 env
        (Clight.EKbinop1 op2 (typeof e1) (typeof e2) ty e2 ek)) 
     st1'.
Proof.   
  intros st1 t st2 H.
  intros until 0.  intro MS.
  inv MS. inv TE.
  monadInv H1.

  unfold transl_binop in EQ2;
  destruct op2 as [] _eqn : O; try done.

  unfold make_add in EQ2;
  destruct (classify_add (typeof e1) (typeof e2)) as []_eqn : C.
  
  sim_binop EQ2 WT C.
  sim_binop EQ2 WT C.
 
  left; eexists; split.
  eapply step_weakstep; simpl.
  inversion EQ2.
  eapply StepBinop1. 
  try eby (eapply match_expr); 
  try eapply match_EKbinop1_add_case_pi;
  try eassumption; try edone; simpl;
  try (by rewrite C);
  inv WT; done.

  left; eexists; split;
  inv EQ2.
  eapply steptau_weakstep; simpl.
  eapply StepBinop1.
  eapply steptau_weakstep; simpl. 
  eapply StepBinop1. 
  unfold make_intconst. 
  eapply steptau_weakstep;  simpl.
  eapply StepConst; simpl; edone.
  eapply step_weakstep; simpl.
  eapply StepBinop2.
  eapply match_expr; try edone; 
    try eapply match_EKbinop1_add_ip; try eassumption; inv WT; try done;
    try econstructor; try eassumption; simpl;
    try (by rewrite C); try done; try (by inv WT).

  done.

  unfold make_sub in EQ2.
  destruct (classify_sub (typeof e1) (typeof e2)) as []_eqn : C.
  sim_binop EQ2 WT C.
  sim_binop EQ2 WT C.

  left; eexists; split.
  eapply step_weakstep; simpl.
  inversion EQ2.
  eapply StepBinop1. 
  eapply match_expr; try edone;
    try (eapply match_EKbinop1_sub_case_pi;
          try eassumption; try edone; simpl;
          try (by rewrite C));
    try (by inv WT).
  
  left; eexists; split;
  inversion EQ2.
  eapply steptau_weakstep; simpl.
  eapply StepBinop1.
  eapply step_weakstep; simpl.
  eapply StepBinop1.
  eapply match_expr; try edone;
    try eapply match_EKbinop1_sub_pp; try eassumption; inv WT; try done;
    try econstructor; try eassumption; simpl;
    try (by rewrite C); try done; try (by inv WT).

  done.

  unfold make_mul in EQ2;
  try (destruct (classify_mul (typeof e1) (typeof e2)) as []_eqn : C); try done;
  try sim_binop EQ2 WT C.

  unfold make_div in EQ2;
  try (destruct (classify_div (typeof e1) (typeof e2)) as []_eqn : C); try done;
  try sim_binop EQ2 WT C.

  unfold make_mod in EQ2;
  try (destruct (classify_mod (typeof e1) (typeof e2)) as []_eqn : C); try done;
  try sim_binop EQ2 WT C.

  unfold make_and in EQ2; sim_binop EQ2 WT C.
  unfold make_or in EQ2; sim_binop EQ2 WT C.
  unfold make_xor in EQ2; sim_binop EQ2 WT C.
  unfold make_shl in EQ2; sim_binop EQ2 WT C.

  unfold make_shr in EQ2;
  try (destruct (classify_shr (typeof e1) (typeof e2)) as []_eqn : C); try done.
  sim_binop EQ2 WT C.   sim_binop EQ2 WT C. 

  sim_binop_logical e1 e2 EQ2 WT C.
  sim_binop_logical e1 e2 EQ2 WT C.
  sim_binop_logical e1 e2 EQ2 WT C.
  sim_binop_logical e1 e2 EQ2 WT C.
  sim_binop_logical e1 e2 EQ2 WT C.
  sim_binop_logical e1 e2 EQ2 WT C.
Qed.


Lemma Sim_StepBinop2:
  forall
   (st1 : Clight.state)
   (t : thread_event)
   (st2: Clight.state)
   (H : Clight.cl_step ge st1 t st2),
   forall (v : val) (op2 : Csyntax.binary_operation) 
     (ty1 ty2 ty : type) (e2 : Csyntax.expr) (ek : Clight.expr_cont)
     (env : Clight.env),
   Clight.valid_arg op2 ty1 ty2 v = true ->
   forall st1' : state,
          match_states 
             (Clight.SKval v env (Clight.EKbinop1 op2 ty1 ty2 ty e2 ek)) st1' ->
     (exists st2' : St tlts,
        weakstep tlts st1' TEtau st2' /\
        match_states 
          (Clight.SKexpr e2 env (Clight.EKbinop2 op2 ty1 ty2 ty v ek)) st2') \/
        (measure (Clight.SKexpr e2 env (Clight.EKbinop2 op2 ty1 ty2 ty v ek)) <
         measure (Clight.SKval v env (Clight.EKbinop1 op2 ty1 ty2 ty e2 ek)))%nat /\
       TEtau = TEtau /\
       match_states 
         (Clight.SKexpr e2 env (Clight.EKbinop2 op2 ty1 ty2 ty v ek)) st1'.
Proof.
  intros st1 t st2 H.
  intros v op2 ty1 ty2 ty e2 ek ENV VA st1' MS.

  inv MS; inv MK.
  destruct ty1; destruct ty2; try done. inv VA. destruct v; inv H1.

  left; eexists; split.
  eapply steptau_weakstep; simpl.
  eapply StepBinop2.
  eapply steptau_weakstep; simpl.
  eapply StepBinop1.
  eapply steptau_weakstep; simpl.
  eapply StepConst. edone.
  eapply step_weakstep; simpl.
  eapply StepBinop2.
  eapply match_expr; try edone.
  eapply match_EKbinop2_add_case_pi; [ eassumption | done | edone | done ].

  left; eexists; split.
  eapply steptau_weakstep; simpl.
  eapply StepBinop2. 
  eapply steptau_weakstep; simpl.
  eapply StepBinop1.
  eapply steptau_weakstep; simpl.
  eapply StepConst; simpl. edone.
  eapply step_weakstep; simpl.
  eapply StepBinop2.

  eapply match_expr; try edone.
  eapply match_EKbinop2_add_case_pi;  [ eassumption | done | edone | done ].


  destruct ty1; destruct ty2; try done. inv VA. destruct v; inv H1.
  left; eexists; split.
  eapply steptau_weakstep; simpl.
  eapply StepBinop. edone.
    
  eapply step_weakstep; simpl.
  inv H13.
  eapply StepBinop2.
  eapply match_expr; try edone.
  eapply match_EKbinop2_add_case_ip; [ eassumption |  done | edone | done | done ].


  destruct v; try done. 
  left; eexists; split.
  eapply steptau_weakstep; simpl.
  eapply StepBinop. edone. 
  eapply step_weakstep; simpl.
  eapply StepBinop2.
  eapply match_expr; try done. edone. done.
  eapply match_EKbinop2_add_case_ip; try done;
   try eassumption; unfold classify_add in H14; by inv H14. done.

  left; eexists; split.
  eapply steptau_weakstep; simpl.
  eapply StepBinop2.
  eapply steptau_weakstep; simpl.
  eapply StepBinop1.
  eapply steptau_weakstep; simpl.
  eapply StepConst. edone.
  eapply step_weakstep; simpl.
  eapply StepBinop2.
  eapply match_expr; try done. edone. done.
  by eapply match_EKbinop2_sub_case_pi;
   [ eassumption | destruct ty1; destruct ty2; simpl in *; try done |
     edone | assumption]. done.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepBinop2.
  eapply match_expr; try done. edone. done.
  eapply match_EKbinop2_sub_case_pp; try edone. done.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepBinop2.
  eapply match_expr; try done. edone. done.
  eapply match_EKbinop2; try edone. done.
Qed.

Lemma Sim_StepBinop:
  forall
   (st1 : Clight.state)
   (t : thread_event)
   (st2: Clight.state)
   (H : Clight.cl_step ge st1 t st2),
   forall (v2 v1 : val) (op2 : Csyntax.binary_operation) 
     (ty1 ty2 ty : type) (ek : Clight.expr_cont) (env : Clight.env) 
     (v : val),
   Clight.sem_binary_operation op2 v1 ty1 v2 ty2 = Some v ->
   forall st1' : state,
   match_states 
      (Clight.SKval v2 env (Clight.EKbinop2 op2 ty1 ty2 ty v1 ek)) st1' ->
   (exists st2' : St tlts,
      weakstep tlts st1' TEtau st2' /\
      match_states  (Clight.SKval v env ek) st2') \/
   (measure (Clight.SKval v env ek) <
    measure (Clight.SKval v2 env (Clight.EKbinop2 op2 ty1 ty2 ty v1 ek)))%nat /\
   TEtau = TEtau /\ match_states  (Clight.SKval v env ek) st1'.
Proof.
  intros st1 t st2 H.
  intros v2 v1 op2 ty1 ty2 ty ek env v BO st1' MS.

  inv MS; inv MK. 

  destruct ty1; destruct ty2; try done. inv BO.
    unfold Clight.sem_add in H1. rewrite H14 in H1; try destruct v1; try done.
    destruct v2; try done.
  left; eexists; split. 
  eapply steptau_weakstep; simpl.
  eapply StepBinop;  edone.
  eapply step_weakstep; simpl.
  eapply StepBinop; inv H13; edone; inv H1.
  eapply match_val; [ edone | done | eassumption ].

  inv BO.
  unfold Clight.sem_add in H1. rewrite H14 in H1; destruct v1; try done.
    destruct v2; try done.
  left; eexists; split.
  eapply steptau_weakstep; simpl.
  eapply StepBinop; edone.
  eapply step_weakstep; simpl.
  eapply StepBinop; inv H13; edone.
  eapply match_val; [ edone | done | eassumption ].

  destruct ty1; destruct ty2; try done. inv BO.
    unfold Clight.sem_add in H1.  rewrite H14 in H1. destruct v2; try done.
  left; eexists; split.    
  eapply step_weakstep; simpl.
  eapply StepBinop; inv H13; edone; inv H1.
  eapply match_val; [ edone | done | eassumption ].

  inv BO.
  unfold Clight.sem_add in H1.  rewrite H14 in H1. destruct v2; try done.
  left; eexists; split.    
  eapply step_weakstep; simpl.
  eapply StepBinop; inv H13; edone; inv H1.
  eapply match_val; [ edone | done | eassumption ].

  destruct ty1; destruct ty2; try done. inv BO.
    unfold Clight.sem_sub in H1.  rewrite H14 in H1. destruct v2; try done.
    destruct v1; try done. destruct v1; try done; inv H1.

  left; eexists; split.
  eapply steptau_weakstep; simpl.
  eapply StepBinop; edone.
  eapply step_weakstep; simpl.
  eapply StepBinop. eby inv H13.  
  eapply match_val; [ edone | done | eassumption ].

  destruct v1; try done. destruct v1; try done.
  inv BO. unfold Clight.sem_sub in H1.
  rewrite H14 in H1; destruct v1; try done.
  destruct v2; try done. inv H1.

  left; eexists; split.
  eapply steptau_weakstep; simpl.
  eapply StepBinop. edone.
  eapply step_weakstep; simpl. 
  eapply StepBinop; eby inv H13.
  eapply match_val; [ edone | done | eassumption ].

  destruct ty1; destruct ty2; try done. inv BO.
    unfold Clight.sem_sub in H1. rewrite H14 in H1; destruct v1; try done.
    destruct v2; try done.   

  destruct (zeq (Ptr.block p) (Ptr.block p0)).
  unfold Ptr.block in e; destruct p; destruct p0.
  rewrite e.
  left; eexists; split.
  eapply steptau_weakstep; simpl.
  eapply StepBinop. 
    unfold eval_binop; unfold Cminorops.eval_binop;
    unfold option_map; unfold Ptr.sub_ptr; 
    destruct (zeq z0 z0); edone; by contradiction n0.

  eapply steptau_weakstep; simpl.
  eapply StepBinop2.
  eapply steptau_weakstep; simpl.
  eapply StepConst. edone. inv H13.
  eapply step_weakstep; simpl.
  eapply StepBinop; edone.
  eapply match_val; [ edone | done | eassumption ].
  done.

  inv BO. unfold Clight.sem_sub in H1. rewrite H14 in H1; destruct v1;
   destruct v2; try done.

  destruct (zeq (Ptr.block p) (Ptr.block p0)).
  unfold Ptr.block in e; destruct p; destruct p0.
  rewrite e.
  left; eexists; split.
  eapply steptau_weakstep; simpl.
  eapply StepBinop.  
    unfold eval_binop; unfold Cminorops.eval_binop;
    unfold option_map; unfold Ptr.sub_ptr; 
    destruct (zeq z1 z1); edone; by contradiction n0.

  eapply steptau_weakstep; simpl.
  eapply StepBinop2.
  eapply steptau_weakstep; simpl.
  eapply StepConst. edone. inv H13.
  eapply step_weakstep; simpl.
  eapply StepBinop; edone.
  eapply match_val; [ edone | done | eassumption ].
  done.

  inv BO. unfold Clight.sem_sub in H1. rewrite H14 in H1; destruct v1;
   destruct v2; try done.

  destruct (zeq (Ptr.block p) (Ptr.block p0)).
  unfold Ptr.block in e; destruct p; destruct p0.
  rewrite e.
  left; eexists; split.
  eapply steptau_weakstep; simpl.
  eapply StepBinop.  
    unfold eval_binop; unfold Cminorops.eval_binop;
    unfold option_map; unfold Ptr.sub_ptr; 
    destruct (zeq z1 z1); edone; by contradiction n0.

  eapply steptau_weakstep; simpl.
  eapply StepBinop2.
  eapply steptau_weakstep; simpl.
  eapply StepConst. edone. inv H13.
  eapply step_weakstep; simpl.
  eapply StepBinop; edone.
  eapply match_val; [ edone | done | eassumption ].
  discriminate.

  inv BO. unfold Clight.sem_sub in H1. rewrite H14 in H1; destruct v1;
   destruct v2; try done.

  destruct (zeq (Ptr.block p) (Ptr.block p0)).
  unfold Ptr.block in e; destruct p; destruct p0.
  rewrite e.
  left; eexists; split.
  eapply steptau_weakstep; simpl.
  eapply StepBinop.  
    unfold eval_binop; unfold Cminorops.eval_binop;
    unfold option_map; unfold Ptr.sub_ptr; 
    destruct (zeq z2 z2); edone; by contradiction n0.

  eapply steptau_weakstep; simpl.
  eapply StepBinop2.
  eapply steptau_weakstep; simpl.
  eapply StepConst. edone. inv H13.
  eapply step_weakstep; simpl.
  eapply StepBinop; edone.
  eapply match_val; [ edone | done | eassumption ].
  done.

  inv BO; unfold Clight.sem_binary_operation in H1;
  destruct op2;  unfold Clight.sem_add in H1; inv H12.

  destruct (classify_add ty1 ty2) as [] _eqn : C;
    try (sim_binop2 v1 v2 H2).
  unfold classify in H13; rewrite C in H13; done.
  unfold classify in H13; rewrite C in H13; done.

  unfold Clight.sem_sub in H1; destruct (classify_sub ty1 ty2) as [] _eqn : C; 
    try (sim_binop2 v1 v2 H2).
  unfold classify in H13; destruct classify_add in H13; 
    try (rewrite C in H13); try done.
  unfold classify in H13; destruct classify_add in H13; 
    try (rewrite C in H13); try done.

  unfold Clight.sem_mul in H1; destruct classify_mul; try (sim_binop2 v1 v2 H2).
  unfold Clight.sem_div in H1; destruct classify_div; try (sim_binop2 v1 v2 H2).
  unfold Clight.sem_mod in H1; destruct classify_mod; try (sim_binop2 v1 v2 H2).
  unfold Clight.sem_and in H1; sim_binop2_simp H1.
  unfold Clight.sem_or in H1; sim_binop2_simp H1.
  unfold Clight.sem_xor in H1; sim_binop2_simp H1.
  unfold Clight.sem_shl in H1; sim_binop2_simp H1.
  unfold Clight.sem_shr in H1; destruct classify_shr; try (sim_binop2 v1 v2 H2).

  (* FIXME: fix the comparison! *)
  sim_binop2_cmp H1 H2 v1 v2.
  sim_binop2_cmp H1 H2 v1 v2.
  sim_binop2_cmp H1 H2 v1 v2.
  sim_binop2_cmp H1 H2 v1 v2.
  sim_binop2_cmp H1 H2 v1 v2.
  sim_binop2_cmp H1 H2 v1 v2.
Qed. 

Lemma Sim_StepCast1:
  forall
   (st1 : Clight.state)
   (t : thread_event)
   (st2: Clight.state)
   (H : Clight.cl_step ge st1 t st2),
  forall (ty : type) (e : Csyntax.expr) (ty' : type) 
         (ek : Clight.expr_cont) (env : Clight.env) (st1' : state),
     match_states 
       (Clight.SKexpr (Expr (Ecast ty e) ty') env ek) st1' ->
     (exists st2' : St tlts,
        weakstep tlts st1' TEtau st2' /\
        match_states 
          (Clight.SKexpr e env (Clight.EKcast (typeof e) ty ek)) st2') \/
     (measure (Clight.SKexpr e env (Clight.EKcast (typeof e) ty ek)) <
      measure (Clight.SKexpr (Expr (Ecast ty e) ty') env ek))%nat /\
     TEtau = TEtau /\
     match_states 
      (Clight.SKexpr e env (Clight.EKcast (typeof e) ty ek)) st1'.
Proof.
  intros st1 t st2 H.
  intros ty e ty' ek env st1' MS.

  inv MS. 

  destruct ty as [] _eqn : T.

  right; split.
    destruct e as [] _eqn : E; simpl; try omega;
    destruct e0 as [] _eqn : E1; simpl; try omega.

  split. done. inv TE. monadInv H1.
  eapply match_expr;
    [ edone | done |  
      eapply match_EKcast; [ edone | edone | destruct (typeof e); done ] |
      inv WT; done |  
      unfold make_cast1; by destruct (typeof e)].

  inversion TE. monadInv H1.
  unfold make_cast1.
  destruct i; destruct s; destruct (typeof e);
  try (sim_cast1 WT);
  try (left; eexists; split;
        try eapply steptau_weakstep; simpl;
        try eapply StepUnop1;
        try eapply step_weakstep; simpl;
        try eapply StepUnop1;
        try eapply match_expr; 
           [ edone | done |
             eapply match_EKcast; 
                [ edone | done | by unfold make_int_cvt ] |
             inv WT; done | done ]);
  try (right; eexists;
        [ destruct e; simpl; try omega ;
          try (destruct e; simpl; try omega) |
          split; try done;
          eapply match_expr;
             [ edone |  done | 
               eapply match_EKcast; try edone |
               by inv WT |  assumption ]]);
  try (inv TE; monadInv H1;
       destruct f as [] _eqn : F;
       unfold make_cast1;
       try (destruct (typeof e) as [] _eqn : T);
       try (sim_cast1 WT));
  try (inversion TE;
          monadInv H1;
          destruct f as [] _eqn : F;
          try (destruct (typeof e) as [] _eqn : T1;
              sim_cast1 WT)).

  inversion TE;
  monadInv H1;
  destruct f as [] _eqn : F;
   try (destruct (typeof e) as [] _eqn : T1; sim_cast1).

  inversion TE. monadInv H1.
  unfold make_cast1.
  destruct (typeof e);
  try (left; eexists; split;
       try (eapply step_weakstep; simpl);
       try (eapply StepUnop1);
       eapply match_expr; try done; try edone;
       try (eapply match_EKcast); 
       try (inv WT); try edone; done).

  unfold make_floatofint.
  destruct s;
  try (left; eexists; split;
       try (eapply steptau_weakstep; simpl);
       try (eapply StepUnop1);
       try (eapply step_weakstep; simpl);
       try (eapply StepUnop1);
       eapply match_expr;
         [ edone | done |
           eapply match_EKcast; [ edone | done | by unfold make_float_cvt ] |
           by inv WT | done ]).

  unfold make_cast1.


  destruct (typeof e) as [];
  try (
  right; split; [|split]; try done;
  destruct e; try done; 
    [try destruct e; simpl; omega
    |try eapply match_expr; try eapply match_EKcast; 
      try edone; inv WT; try edone;
      try destruct e; done]).

  unfold make_floatofint.
  destruct s;
  try (sim_cast1 WT).

  inv TE; monadInv H1; sim_cast1_measure e t1 WT.
  inv TE; monadInv H1; sim_cast1_measure e t1 WT.
  inv TE; monadInv H1; sim_cast1_measure e t2 WT.
  inv TE; monadInv H1; sim_cast1_measure e t0 WT.
  inv TE; monadInv H1; sim_cast1_measure e t0 WT.
  inv TE; monadInv H1; sim_cast1_measure e t0 WT.
Qed.

Lemma intsize_dec (a b: intsize) : {a = b} + {a <> b}.
Proof. destruct a; destruct b; solve [by left | by right]. Qed.


Lemma Sim_StepCast2:
 forall 
  (st1 : Clight.state)
  (t : thread_event)
  (st2 : Clight.state)
  (H : Clight.cl_step ge st1 t st2),
   forall (v : val) (ty ty' : type) (ek : Clight.expr_cont)
     (env : Clight.env) (v' : val),
   Clight.cast v ty' ty v' ->
   forall st1' : state,
   match_states 
     (Clight.SKval v env (Clight.EKcast ty' ty ek)) st1' ->
   (exists st2' : St tlts,  
     weakstep tlts st1' TEtau st2' /\
     match_states  (Clight.SKval v' env ek) st2') \/
   (measure (Clight.SKval v' env ek) <
    measure (Clight.SKval v env (Clight.EKcast ty' ty ek)))%nat /\
   TEtau = TEtau /\ match_states  (Clight.SKval v' env ek) st1'.

Proof.
  intros st1 t st2 H. intros v ty ty' ek env v' C st1' MS.
  inv MS. 
  inversion C; inv MK.

  destruct (intsize_dec sz2 I32) as [->|NEQ].
    right; split; [|split;[done|eby eapply match_val]].
    by destruct si2; try odone; destruct ek; try odone; 
      try (destruct t0); try odone;
      try (destruct t1; try odone); try (destruct i1; try odone).
  left; destruct sz2; try done; destruct si2;
  ( eexists; split;
        try (eapply step_weakstep; simpl);
        try (eapply StepUnop; edone);
        eapply match_val; edone).

  destruct sz2; destruct si2; try sim_cast2.

  destruct sz2; destruct si1; try sim_cast2.
  destruct sz2; try sim_cast2.

  right; split.  
  destruct ek; try simpl; try omega.
  destruct t0; try destruct t1; try omega.
  destruct f1; try omega.
  split; try done.
  eapply match_val; edone.

  destruct ty;
  try (destruct ty'; inv C; try (inv H1); try (inv H3));
  right; eexists;
  destruct ek; try simpl; try (destruct t0); try omega;
  split; try done;
  eapply match_val; edone.

  destruct ty; destruct ty'; inv H0; inv H1;
  right; split; 
  try (split; try done);
  try (eapply match_val; try edone);
  destruct ek; simpl; try odone;
  try (destruct t0; destruct t1; try odone);
  try (destruct t2; try odone);
  try (destruct t3; try odone);
  try (destruct i0; try odone).
Qed.

End CLIGHT_DEFS.
