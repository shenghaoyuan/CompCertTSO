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
(*          Xavier Leroy, INRIA Paris-Rocquencourt  >                   *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** * Correctness of the C front end, part 3: semantic preservation *)

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
Require Import Globalenvs.
Require Import Pointers.
Require Import Csyntax.
Require Import Csem.
Require Import Ctyping.
Require Import Cminorops.
Require Import Csharpminor.
Require Import Cshmgen.
Require Import Cshmgenproof1.
Require Import Cshmgenproof2. 
Require Import Simulations MCsimulation.
Require Import Memcomp Traces.

Section CLIGHT_CSHM_SIM.

Variable prog: Csyntax.program.
Variable tprog: Csharpminor.program.
Variables (ge : Clight.cl_sem.(SEM_GE)) (tge : cs_sem.(SEM_GE)).
Hypothesis WTPROG: wt_program prog.
Hypothesis TRANSL: transl_program prog = OK tprog.
Hypothesis TRANSF: genv_rel ge (fst tge).
Hypothesis globenv_fn_in:
  forall p f, Genv.find_funct_ptr ge p = Some f -> 
              exists id, In (id, f) prog.(prog_funct).

Let lts := (mklts thread_labels (Clight.step ge)).
Let tlts := (mklts thread_labels (cs_step tge)).

Notation match_states := (match_states prog tge).

Ltac odone := abstract (solve [done|simpl;omega]).

Ltac rewrite_discriminate :=
  match goal with 
   | H : ?a = ?b, H' : ?a = ?c |- _ => rewrite H in H'; discriminate
   | H : ?a = ?b, H' : ?a = ?c \/ ?a = ?d |- _ =>
       rewrite H in H'; destruct H'; discriminate
  end. 

Lemma sig_translated:
  forall fd tfd targs tres,
  classify_fun (type_of_fundef fd) = fun_case_f targs tres ->
  transl_fundef fd = OK tfd ->
  funsig tfd = signature_of_type targs tres.
Proof.
  intros. destruct fd; monadInv H0; inv H. 
  monadInv EQ. simpl. auto. 
  simpl. auto.
Qed.

Lemma sem_atomic_statement_correct:
  forall astmt vs p rmwi astmt'
    (SAS : Clight.sem_atomic_statement astmt vs = Some (p, rmwi))
    (TAS : transl_atomic_statement astmt = OK astmt'),
      sem_atomic_statement astmt' vs = Some (p, rmwi).
Proof.
  intros.
  by destruct astmt; inv TAS.
Qed.

(** Proof of simulation for Clight steps. Essentially a huge case
    split on possible steps, and a separate proof of each case. *)

Lemma cshmgen_step_correct:
  forall st1 t st2,
  Clight.cl_step ge st1 t st2 ->
  match_globalenv (global_typenv prog) (snd tge) ->
  forall st1' (MS: match_states st1 st1'),
  (exists st2', weakstep tlts st1' t st2' /\ match_states st2 st2')
  \/ (measure st2 < measure st1 /\ t = TEtau /\ match_states st2 st1')%nat.

Proof.
  intros st1 t st2 H MG.
  
  cl_step_cases (case H) Case.

  Case "StepConstInt".

  intros until 0. intros MS.
  inv MS. inv TE.
  unfold make_intconst. 
  left; eexists; split.
  eapply step_weakstep; simpl.
  eby eapply StepConst.
  eby eapply match_val.

  Case "StepConstFloat".

  intros f ty ek env0 st1' M.
  inv M. inv TE.
  left; eexists; split.
  unfold make_floatconst.
  apply step_weakstep; simpl.
  eby eapply StepConst.
  eby eapply match_val. 

  Case "StepVarExprByValue".

  intros id ty ek env0 st1' MS.
  inv MS. inv TE.
  right; split; simpl.
  destruct ek as [] _eqn : K; try simpl; omega.
  split. edone. 
  unfold var_get in H1;
   destruct (access_mode ty) as [] _eqn: AM.
  inv H1; try eapply match_var_val; try edone.
  inv H1; eapply match_var_ref; try edone.
  left;  assumption. inv H1.

  Case "StepVarLocal". 

  intros id ty ek env0 p ENV st1' M.
  inv M. inv TE. 
  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepAddrOf.
  inv MENV.
  destruct (me_local id p ENV) as [vk' [ty' [C1 [C2 C3]]]].
  by eapply (eval_var_addr_local tge tenv id p vk'). 

  eapply match_val; try edone.

  right. split. simpl. try omega. 
  split.  done.
  econstructor; try edone; simpl.
  unfold var_get; rewrite AM; by done.
  inv MENV.
  destruct (me_local id p ENV) as [vk' [ty' [C1 [C2 C3]]]];
    try eapply (eval_var_ref_local tge tenv id p c);
    unfold match_var_kind in C2;
    inv WT; try rewrite C1 in H1; inv H1; try rewrite AM in C2. 
  by inv C2.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepAddrOf. 
  inv MENV.
  destruct (me_local id p ENV) as [vk' [ty' [C1 [C2 C3]]]];
    unfold match_var_kind in C2. inv C1;
   inv H1; inv WT; try rewrite H1 in H2; inv H2;
   inv AM; try rewrite H0 in C2; 
   try by eapply (eval_var_addr_local tge tenv id p vk'). 
  eapply match_val; try edone.
  eby eapply match_EKlval_ref. 

  right; split; simpl; try omega.
  split; try done.
  eapply match_assign_lval_stutter; try edone.
  inv MENV.
  destruct (me_local id p ENV) as [vk'' [ty'' [C1 [C2 C3]]]];
    try eapply (eval_var_ref_local tge tenv id p c);
    inv WT; try rewrite C1 in H1; inv H1; 
    unfold match_var_kind in C2; try rewrite AM in C2.
  by subst.

  right; split; simpl; try omega.
  split. done.
  inv TE1.
  eapply match_assign_lval_ptr; try edone.
  inv MENV.
  destruct (me_local id p ENV) as [vk' [ty' [C1 [C2 C3]]]];
    by eapply (eval_var_addr_local tge tenv id p vk').

  Case "StepVarGlobal". 

  intros id ty ek env0 p ENV G st1' M.
  inv M. inv TE.
  left. eexists. split.
  eapply step_weakstep. simpl.
  eapply StepAddrOf.
  inv MENV.
  destruct (me_global id ty); try eassumption.
  inv WT. done.
  eapply (eval_var_addr_global tge tenv id p). eassumption. 
  rewrite <- G. apply symbols_preserved. done. simpl. 
  eapply match_val; try edone.

  right. split. simpl; try omega. 
  split.  done.
  econstructor; try edone. simpl.
  unfold var_get. rewrite AM. by done.
  inv MENV.
  destruct (me_global id ty); try eassumption.
  by inv WT.
  eapply (eval_var_ref_global tge tenv id p c). done.
  rewrite <- G. apply symbols_preserved.
  specialize (H1 c). rewrite AM in H1. done. apply H1. done.

  left. eexists. split.
  eapply step_weakstep. simpl.
  eapply StepAddrOf.
  inv MENV.
  destruct (me_global id ty); try assumption.
  by inv WT.
  eapply (eval_var_addr_global tge tenv id p). eassumption.
  rewrite <- G. apply symbols_preserved. simpl. done.
  eapply match_val; try edone.
  eby eapply match_EKlval_ref. 

  right. split. simpl. try omega.
  split. done.
  eapply match_assign_lval_stutter; try edone.
  inv MENV.
  destruct (me_global id ty). eassumption. 
  by inv WT.
  eapply (eval_var_ref_global tge tenv id p c). done.
  rewrite <- G. apply symbols_preserved. done.
  specialize (H1 c). rewrite AM in H1. apply H1. done.

  right. split. simpl. omega.
  split. done.
  inv TE1.
  eapply match_assign_lval_ptr; try edone.
  inv MENV.
  destruct (me_global id ty); try eassumption.
  by inv WT2. 
  eapply (eval_var_addr_global tge tenv id p). eassumption.
  rewrite <- G. apply symbols_preserved. done. simpl. 

  Case "StepLoadByValue".

  intros p ty' ek env c v typ0 AM TC HT st1' MS. 
  inv MS. inv MK.
  left; eexists; split. 
  eapply step_weakstep. simpl.
  rewrite AM in H7. inv H7.
  eapply StepLoad. done.
  eby eapply match_val.

  left; eexists; split. 
  apply step_weakstep; simpl. 
  rewrite AM in H7. by inv H7.
  eby eapply match_val.
  rewrite AM in AM0. inv AM0. 
  try econstructor; try edone.
  
  eexists; split.
  apply step_weakstep; simpl.
  eapply StepVar; try done. 
  eby eapply match_val.

  Case "StepLoadNotByValue".

  intros p ty' ek env AM st1' MS.

  inv MS. inv MK.
  rewrite H7 in AM; by inv AM.
  right; split; simpl. 
  destruct ek; try omega. simpl. omega.
  simpl; omega.
  split; try done.
  eby eapply match_val.

  inv H5.
  rewrite AM0 in AM. eby inv AM. 

  Case "StepAddr".

  intros e ty ek env0 st1' MS.
  right; split.

  destruct e. simpl. 
  inv MS.

  destruct e; simpl;
    (try destruct ek);
    try (simpl; try omega);
      (try (destruct e); try simpl; try omega);
      destruct e; simpl; try (destruct t0); try omega.

  split. done.
  destruct e. destruct e;
  try (inv MS); try done. 
  inv TE.
  eapply match_lval; try eassumption; try edone.
  by inv WT.
  eapply match_lval; try edone.
  by inv WT.
 
  inv TE. 
  destruct (typeof e) as [] _eqn : F; try discriminate.
  unfold make_intconst in H1.
  monadInv H1. 
  eapply match_lval; try edone; try assumption.    
  by inv WT. simpl.

  by rewrite F, EQ; simpl; rewrite EQ1.
  eapply match_lval; try edone.
  by inv WT. inv H1. simpl.
  by rewrite F.

  Case "StepEcondition".

  intros e1 e2 e3 ty ek env0 st1' MS.
  inv MS. inv TE. inv WT.
  monadInv H1.
  unfold make_boolean.
  destruct (typeof e1) as [] _eqn : T; try done;
    left; eexists; 
    try (split; [ eapply step_weakstep; simpl; econstructor |  
                   econstructor; try edone;
                   try (econstructor; try edone ;  eassumption); inv WT]; done).
  split.
  eapply steptau_weakstep. simpl. econstructor; try edone.
  eapply step_weakstep. simpl. unfold make_floatconst.
  eapply StepBinop1. eapply match_expr; try edone.
  eby eapply match_EKcondition_float; try done.

  Case "StepEconditiontrue".

  intros v ty e2 e3 ek env0 T st1' MS.
  inv MS.  inv MK.
  left. eexists. split.
  eapply step_weakstep. simpl.
  eapply StepIfThenElseTrue.

  inversion T; 
   try (apply Val.bool_of_val_int_true; done); 
   try apply Val.bool_of_val_ptr_true.

  specialize (H15 sz). clarify.
  eapply match_expr; try edone. 

  left. eexists. split.
  eapply steptau_weakstep. simpl. eapply StepBinop2.
  eapply steptau_weakstep. simpl. eapply StepConst.
  eby unfold eval_constant.
  eapply steptau_weakstep. simpl. 
  eapply StepBinop.
  by simpl; inv T; rewrite H2.

  eapply step_weakstep; simpl.
  eapply StepIfThenElseTrue.
  by apply Val.bool_of_val_int_true. 

  eby eapply match_expr.


  Case "StepEconditionfalse".

  intros v ty e2 e3 ek env0 T st1' MS.
  inv MS. inv MK.
  
  left; eexists; split. 
  eapply step_weakstep; simpl.
  eapply StepIfThenElseFalse.
  inv T; try (apply Val.bool_of_val_int_false; done); 
    try apply Val.bool_of_val_ptr_true.
  specialize (H15 sz). done. 
  eapply match_expr; try edone.

  left; eexists; split.
  eapply steptau_weakstep; simpl. 
  eapply StepBinop2.
  eapply steptau_weakstep; simpl. 
  eapply StepConst.
  eby unfold eval_constant. 
  eapply steptau_weakstep; simpl. 
  eapply StepBinop.
  by simpl; inv T; rewrite Float.cmp_ne_eq, H2.

  eapply step_weakstep. simpl.
  eapply StepIfThenElseFalse.
  unfold Vfalse. apply Val.bool_of_val_int_false. 

  eapply match_expr; try edone.


  Case "StepDeref".

  intros e ty ek env0 st1' MS.
  inv MS. inv TE.
  monadInv H1. 
  unfold make_load in EQ0.
  destruct (access_mode ty) as [] _eqn : AM.

  left; esplit; split.
  eapply step_weakstep. simpl.
  inv EQ0. 
  eapply StepLoad1.
  eapply match_expr; try edone.
  eby eapply match_EKlval_load.
  by inv WT. 

  right. split. simpl.
  destruct e; destruct e; try odone.

  split. done.
  eapply match_expr;
    (try edone); (try econstructor); inv WT.
  by left. 
  eassumption.
  done. 
  by rewrite <- EQ in EQ0. 

  inv EQ0.


  Case "StepDerefLval".

  intros e ty ek env0 st1' MS.

  right; split; simpl.
  destruct e; try odone;
    try (unfold countDeref); try (unfold countEKlval);
      try (destruct e); try odone; try (destruct ek); try odone;
        try (destruct e); try odone; 
        try (destruct e); try odone.

  split. done.
  inv MS. inv TE. eapply match_expr; try edone.
  by inv WT. 

  eapply match_expr;  try edone; try eassumption.
  eapply match_EKassign1.  eassumption. eby eassumption. 
  inv WT1.
  done. 
  unfold Clight.type_to_chunk.  eby rewrite AM.
  edone.
  by inv WT2. 

  Case "StepField".

  intros e id ty ek env0 st1' MS.
  inv MS. inv TE.

  destruct (typeof e) as [] _eqn : T; try done.
  monadInv H1.
  unfold make_load in EQ2.

  destruct (access_mode ty) as [] _eqn : AM.
  left; esplit; split.
  eapply step_weakstep. simpl.
  inv EQ2.
  eapply StepLoad1.
  eapply match_lval; try edone.
  eby eapply match_EKlval_load. 
  inv EQ2. simpl.
  destruct (typeof e) as [] _eqn : TL; 
    simpl; try done; try (inv F; rewrite_discriminate).
  rewrite <- TL in T. rewrite TL in T. inv T.
  inv EQ. rewrite H1. unfold bind.  
  destruct (field_offset id f) as [] _eqn : FO. inv EQ1.
  done.

  done. 

  right. split. odone.
  split. done.
  inv EQ2.
  eapply match_lval;
    (try edone); try econstructor.
  by left. edone.

  inv EQ1. simpl.
  destruct (typeof e) as [] _eqn : TL; 
    simpl; try done; try (inv F; rewrite_discriminate).
  rewrite <- TL in T. rewrite TL in T. inv T.
  inv EQ. rewrite H1. unfold bind.  
  destruct (field_offset id f) as [] _eqn : FO. 
  by rewrite H2.
  by rewrite H2.

  done.

  unfold make_load in H1.
  destruct (access_mode ty) as [] _eqn : AM.
  monadInv H1. 
  left; eexists; split.
  apply step_weakstep; simpl.
  eapply StepLoad1. 
  eapply match_lval; try edone.
  eapply match_EKlval_load; try edone. 

  inv EQ. simpl.
  destruct (typeof e) as [] _eqn : TL; 
    simpl; try done; try (inv F; rewrite_discriminate).
 
  right. split. 
  simpl; destruct e; try done;
    destruct ek; try done;
    destruct e; try done;
    (try destruct ek); try odone.
  split. done.
  eapply match_lval; try edone.
  eapply match_EKlval_ref; try edone. left. done.

  simpl.
  destruct (typeof e) as [] _eqn : TL; 
    simpl; try done; try (inv F; rewrite_discriminate).
  by monadInv H1. 

  monadInv H1. 


  Case "StepFstruct1".

  intros e id ty ek env0 delta id' fld TY F st1' MS.

  inv MS. inv TE.
  destruct (typeof e) as [] _eqn : TL; try done.
  monadInv H1. 
  left; eexists; split.
  eapply step_weakstep. simpl.
  eapply StepBinop1.
  eapply match_lval; try edone.
  inv F. inv TY. rewrite H1 in EQ1. inv EQ1.
  eapply match_EKfield_exp; try edone.
  by inv WT. 

  inv TE1. inv TE2.
  destruct (typeof e) as [] _eqn : TL; try done.
  monadInv H1.
  left; eexists; split.
  eapply step_weakstep. simpl.
  eapply StepBinop1.
  eapply match_lval; try edone.
  inv F. inv TY. rewrite H1 in EQ1. inv EQ1.
  eapply match_EKfield_exp.
  eapply match_EKassign1; try done; try eassumption.
  unfold Clight.type_to_chunk; by rewrite AM.
  by inv WT2. 

  Case "StepFstruct2".

  intros p delta ek env0 P P' st1' MS.

  inv MS. inv MK.
  left; eexists; split.
  eapply steptau_weakstep. simpl.
  eapply StepBinop2.
  eapply steptau_weakstep. simpl.
  eapply StepConst.
  by unfold eval_constant.
  eapply step_weakstep; simpl.
  eapply StepBinop.
  unfold eval_binop. unfold Cminorops.eval_binop. done.
  unfold Ptr.offset. destruct p.  eapply match_val; try edone.


  Case "StepFunion".

  intros e id ty ek env0 id' phi TE st1' MS.

  right; split; simpl. 
  destruct e; try odone; destruct e; try odone.
  destruct ek; try odone.
  split; trivial.

  inv MS. inv TE0.
  rewrite TE in H1.
  eapply match_lval; try edone.
  by inv WT. 

  eapply match_lval; try edone.
  eapply match_EKassign1; try edone. 
  unfold Clight.type_to_chunk; by rewrite AM. 
  by inv WT2.

  rewrite <- TE1; simpl. 
  by rewrite TE.

  Case "StepSizeOf".

  intros ty' ty ek env0 v size st1' MS.
  inv MS. inv TE.  
  left; eexists; split. 
  unfold make_intconst.
  eapply step_weakstep. simpl.
  eapply StepConst.
  eby unfold eval_constant.
  eapply match_val; try edone; try done.

  Case "StepUnop1".

  intros op1 e ty ek env0 st1' MS.
  inv MS. inv TE.
  monadInv H1.
  inv EQ. unfold transl_unop in EQ0.
  destruct op1 as [] _eqn : OP; try discriminate;
    unfold make_notbool in EQ0;
      destruct (typeof e) as []_eqn : D; try done;
        left; eexists; split;
          try (eapply step_weakstep); simpl;
            inv EQ0; try (unfold make_floatconst); try (eapply StepBinop1);
              try (eapply StepUnop1); try (eapply match_expr); 
               try (eassumption); try done;
                try (eapply match_EKunop); try (eapply match_EKunop_float); simpl; auto;
                  try eassumption; try (inv WT); try done.

  Case "StepUnop".

  intros v op1 ty ek env0 v' unop st1' MS.
  inv MS. inv MK.
  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepUnop.
  unfold match_unop in H9;
    destruct op1; try done;
    destruct ty; try done; try discriminate; simpl;
      try (unfold Clight.sem_unary_operation in unop);
        try (unfold Clight.sem_notbool in unop);
          try (unfold Clight.sem_notint in unop);
            destruct v; try discriminate;
              inv H9; simpl; 
                try (rewrite unop; edone);
                  try (rewrite <- unop; reflexivity);
                    try (unfold  Int.not; rewrite <- unop; reflexivity).
  eby eapply match_val.

  left; eexists; split.
  eapply steptau_weakstep; simpl.
  eapply StepBinop2. eapply steptau_weakstep; simpl.
  eapply StepConst; simpl; edone.
  eapply step_weakstep; simpl.
  eapply StepBinop.
  unfold Clight.sem_unary_operation in unop;
    unfold Clight.sem_notbool in unop;
      destruct v; try done; try discriminate;
        unfold eval_binop; unfold Cminorops.eval_binop;
          eby rewrite unop.
  eby eapply match_val.


  Case "StepBinop1".
 
  apply (Sim_StepBinop1 _ _ _ st1 t st2 H). 

  Case "StepBinop2".

  apply (Sim_StepBinop2 _ _ _ st1 t st2 H). 

  Case "StepBinop".

  apply (Sim_StepBinop _ _ _ st1 t st2 H). 

  Case "StepCast1".

  apply (Sim_StepCast1 _ _ _ st1 t st2 H). 

  Case "StepCast2".

  apply (Sim_StepCast2 _ _ _ st1 t st2 H). 

  Case "StepAndbool".

  intros e1 e2 ty ek env0 n1 n0 N0 N1 st1' MS.
  
  inv MS. inv TE. monadInv H1.
  unfold make_andbool.
  right. split.
  simpl; destruct ek; try omega. simpl; omega.
  split; try done.
  eapply match_expr; try edone.
  inv WT.
  apply wt_Econdition; try (apply wt_Econdition); try done;
  apply wt_Econst_int.
  simpl. by rewrite EQ, EQ1.


  Case "StepOrbool".

  intros e1 e2 ty ek env0 n1 n0 N0 N1 st1' MS.
  
  inv MS. inv TE. monadInv H1.
  unfold make_orbool.
  right. split.
  simpl; destruct ek; try omega. simpl. omega.
  split; try done.
  eapply match_expr; try edone.
  inv WT.
  apply wt_Econdition; try (apply wt_Econdition); try done;
  apply wt_Econst_int.
  simpl. by rewrite EQ, EQ1.


  Case "StepThread".

  intros e1 e2 k env0 st1' MS.

  inv MS. inv TS. monadInv H1.
  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepThread. inv WT.
  eapply match_expr; try edone. 
  eby eapply match_EKthread1.


  Case "StepThreadFn".

  intros p e2 k env0 st1' MS.

  inv MS. inv MK.
  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepThreadFn.
  eapply match_expr; try edone.
  eby eapply match_EKthread2. 


  Case "StepThreadEvt".

  intros v p k env0 st1' MS.

  inv MS. inv MK.
  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepThreadEvt.
  eapply match_stmt; try edone; vauto.

  Case "StepAssign1".

  intros e1 e2 k env0 st1' MS.
  inv MS. inversion TS. 
  destruct (is_variable e1) as []_eqn : A.
  monadInv H1.

  unfold var_set in EQ0.
  destruct (access_mode (typeof e1)) as []_eqn : AM;
    try done.
  inv EQ0.
  unfold is_variable in A.
   destruct e1; try done;
   destruct e; try done.
  inv A.
  right; eexists; try odone.
  split; try done.
  eapply match_assign_lval_id; try edone. inv TS. monadInv H1.
  eby inv WT. by inv WT.  
  unfold Clight.type_to_chunk.
  by rewrite AM.

  monadInv H1. 
  unfold make_store in EQ2.
  destruct (access_mode (typeof e1)) as []_eqn : AM;
    try done.

  inv EQ2.
  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepStore1.
  eapply match_assign_lval_step; try edone.
  eby inv WT.
  eby inv WT.

  Case "StepAssign2".  

  intros v1 ty e2 k env0 st1' MS.
  inv MS. inv MK.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepStore2.
  eapply match_expr; try edone.
  eby eapply match_EKassign2_exp.

  left; eexists; split.
  eapply steptau_weakstep; simpl.
  eapply StepAddrOf. edone.
  eapply step_weakstep; simpl.
  eapply StepStore2.  
  eapply match_expr; try edone. 
  eby eapply match_EKassign2_exp. 

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepAssign1.
  eapply match_expr; try edone. 
  eby eapply match_EKassign2_var.
 
  Case "StepAssign".

  intros v2 p1 ty1 k env0 c v1 TC CVC st1' MS.

  inv MS. inv MK.
  left; eexists; split.
  eapply step_weakstep; simpl.

  unfold Clight.type_to_chunk in TC.
  rewrite H10 in TC. inv TC.
  eapply StepStore.
  eapply match_stmt; try edone; vauto.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepAssign. 
  rewrite TC in H10. inv H10; edone.
  eapply match_stmt; try edone; vauto.

  Case "StepSeq". 

  intros s1 s2 k env0 st1' MS.
  inv MS. inv TS. monadInv H1.
  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepSeq.
  eapply match_stmt; try edone. 
  eapply match_Kseq; try edone; by inv WT.
  by inv WT.  

  Case "StepCall".

  intros lhs e' es k env0 st1' MS.

  inv MS. inv TS. 
  destruct (classify_fun (typeof e')) as [] _eqn : CF. 
  monadInv H1.
  
  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepCall.
  eapply match_expr; try edone.
  eapply match_EKcall; try inv WT; try edone.
  by destruct lhs as [[id ty]|]; inv EQ.
  by inv WT.
  done.

  Case "StepCallargsnone".

  intros v opt_lhs ty k env0 fd G Etfd st1' MS.
  inv MS. inv MK.
  destruct TRANSF.
  unfold Genv.find_funct in *; destruct v; try discriminate.  
  specialize (H1 p); rewrite G in H1.
  destruct (Genv.find_funct_ptr (fst tge) p) as [] _eqn : K.

  inv H4.
  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepEmptyCall.
  unfold Genv.find_funct.  unfold Csharpminor.ge. edone.
  eby eapply sig_translated.
  eapply match_call; try edone.
  eapply functions_well_typed; try edone.
  by inv G; apply Genv.find_funct_find_funct_ptr.

  done.

  Case "StepCallArgs1".

  intros v opt ty e es k env0 st1' MS.
  inv MS. inv MK. 
  inv H4. monadInv H1.
  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepCallArgs1.
  eapply match_expr; try edone.
  eapply match_EKargs; try edone.  
  eby inv H6. 
  eby inv H6.  

  case "StepCallArgs2".

  intros A S. intros v1 opt v ty vs e es k env0 st1' MS.
  inv MS. inv MK. 
  inv H11. monadInv H1.
  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepCallArgs2.
  eapply match_expr; try edone.
  eapply match_EKargs; try edone.  
  eby inv H13.  eby inv H13.

  case "StepCallFinish".

  intros A S. intros v' opt v ty vs k env0 fd G Etfd st1' MS.
  inv MS. inv MK. 
  inv H11. 
  destruct TRANSF.
  unfold Genv.find_funct in *; destruct v; try discriminate.
  specialize (H1 p); rewrite G in H1.  
  destruct (Genv.find_funct_ptr (fst tge) p) as [] _eqn : K.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepCallArgs. 
  unfold Genv.find_funct. unfold Csharpminor.ge. edone.
  eby eapply sig_translated.
  eapply match_call; try edone.
  eapply functions_well_typed; try edone. 
  inv G. apply Genv.find_funct_find_funct_ptr.

  done.

  Case "StepAtomic".
  
  intros until 1. inv MS.
  inv TS. 
  monadInv H1. monadInv EQ0. inv WT. inv H4.
  
  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepAtomic.
  eapply match_expr; try edone.
  eapply match_EKatargs; try edone.
  by destruct opt_lhs as [[id ty]|]; inv EQ.

  Case "StepAtomicArgs".
  
  intros until 1. inv MS. inv MK. monadInv H10. inv H13.

  left; eexists; split.
    by eapply step_weakstep; simpl; apply StepAtomicArgs. 
  by eapply match_expr; try edone; vauto.

  Case "StepAtomicFinishNone".

  intros until 0. intros SAS HT st1' MS. inv MS. inv MK. inv H10. 
  destruct ret'; [done|].

  left; eexists; split.
  eapply step_weakstep; simpl.
    eby eapply StepAtomicFinishNone; [eapply sem_atomic_statement_correct|]. 
  by econstructor; try edone; vauto.

  Case "StepAtomicFinishSome".

  intros until 0. intros SAS HT st1' MS. inv MS. inv MK. inv H10. inv WTLHS.
  destruct ret'; [inv H14|done].

  left; eexists; split.
  eapply step_weakstep; simpl.
    eby eapply StepAtomicFinishSome; [eapply sem_atomic_statement_correct|].
  eby econstructor. 

  Case "StepFence".
  
  intros until 1. inv MS. monadInv TS.
  left; eexists; split.
  eapply step_weakstep; simpl.
    eby eapply StepFence.
  eby econstructor; vauto. 
  
  Case "StepContinue".

  intros s k env0 st1' MS.
  inv MS. inv MK. inv TS.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepExitSeq.
  eby eapply match_stmt.


  Case "StepBreak".

  intros s k env0 st1' MS.
  inv MS. inv MK. inv TS.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepExitSeq.
  eby eapply match_stmt.

  Case "StepIfThenElse".

  intros e s1 s2 k env0 st1' MS.
  inv MS. inv TS. monadInv H1. 
  unfold make_boolean.
  destruct (typeof e) as [] _eqn : T; try done;
    left; eexists;
    try (split; [ eapply step_weakstep; simpl; eapply StepCond | 
                  eapply match_expr; try edone; 
                    try (eapply match_EKcond; try edone); by inv WT]).

  split.
  eapply steptau_weakstep. simpl. econstructor; try edone.
  eapply step_weakstep. simpl. unfold make_floatconst.
  eapply StepBinop1. 
  eapply match_expr; try edone.
  eapply match_EKcond_float; try edone; by inv WT.
  by inv WT.


  case "StepIfThenElseTrue".

  intros A S v ty s1 s2 k env0 T st1' MS.
  inv MS. inv MK.

  left. eexists. split.
  eapply step_weakstep. simpl.
  eapply StepCondTrue.

  inversion T; 
   try (apply Val.bool_of_val_int_true; done); 
   try apply Val.bool_of_val_ptr_true.

  specialize (H15 sz). clarify.
  eby eapply match_stmt.

  left. eexists. split.
  eapply steptau_weakstep. simpl. eapply StepBinop2.
  eapply steptau_weakstep. simpl. eapply StepConst.
  unfold eval_constant. eauto.
  eapply steptau_weakstep. simpl. eapply StepBinop.
  by inv T; simpl; rewrite H2.

  eapply step_weakstep. simpl.
  eapply StepCondTrue.
  unfold Vtrue.  apply Val.bool_of_val_int_true. done.
  eby eapply match_stmt.
 
  case "StepIfThenElseFalse".

  intros A S v ty s1 s2 k env0 T st1' MS.
  inv MS.  inv MK.

  left. eexists. split.
  eapply step_weakstep. simpl.
  eapply StepCondFalse.

  inversion T; 
   try (apply Val.bool_of_val_int_false; done); 
   try apply Val.bool_of_val_ptr_true.

  specialize (H15 sz). clarify.
  eby eapply match_stmt.

  left. eexists. split.
  eapply steptau_weakstep. simpl. eapply StepBinop2.
  eapply steptau_weakstep. simpl. eapply StepConst.
  unfold eval_constant. eauto.
  eapply steptau_weakstep. simpl. eapply StepBinop.
  by inv T; simpl; rewrite Float.cmp_ne_eq, H2.

  eapply step_weakstep. simpl.
  eapply StepCondFalse.
  unfold Vfalse. apply Val.bool_of_val_int_false. 
  eby eapply match_stmt.


  case "StepWhile".

  intros A S. intros e s k env0 st1' MS.
  inv MS. inv TS. monadInv H1. 
  generalize EQ; intros EX.

   unfold exit_if_false in EQ. unfold bind in EQ.
   destruct (transl_expr e) as []_eqn : TE.
   inversion EQ.
   unfold make_boolean in *.
   destruct (typeof e) as []_eqn : TY; try done;
   left; eexists;
   try (split;
         [ eapply steptau_weakstep; simpl;  try (eapply StepBlock);
           eapply steptau_weakstep; simpl;  try (eapply StepLoop);
           eapply steptau_weakstep; simpl;  try (eapply StepSeq);
           try (eapply step_weakstep; simpl; try (eapply StepCond))
        | eapply match_expr; try edone;
          try (eapply match_EKwhile; try edone); try (intros; rewrite TY; done);
          eby inv WT ]).

  split.
  eapply steptau_weakstep; simpl; try (eapply StepBlock);
  eapply steptau_weakstep; simpl; try (eapply StepLoop);
  eapply steptau_weakstep; simpl; try (eapply StepSeq);
  eapply steptau_weakstep; simpl; try (eapply StepCond).
  eapply step_weakstep; simpl. eapply StepBinop1.
  unfold make_floatconst.  eapply match_expr; try edone; try eby inv WT.
  eapply match_EKwhile_float; try edone; try eby inv WT. 
  inv EQ.

  unfold exit_if_false in H5. monadInv H5.
  destruct (typeof e) as []_eqn : T;
  unfold make_boolean;
  left; eexists; 
  try (split;
       [ eapply step_weakstep; simpl; try (eapply StepCond)
       |  eapply match_expr; try edone; try (eapply match_EKwhile); try (by inv WT);
          unfold exit_if_false; unfold bind;
          try (rewrite EQ); try (rewrite T); unfold make_boolean; edone ]).

  split.
  eapply steptau_weakstep; simpl; try (eapply StepCond);
  eapply step_weakstep; simpl;    try (eapply StepBinop1).
  unfold make_floatconst.
  eapply match_expr; try edone.
  eapply match_EKwhile_float; try edone; try eby inv WT. 
  unfold exit_if_false; unfold bind.
  rewrite EQ; rewrite T; unfold make_boolean; edone. eby inv WT.

  case "StepWhileTrue".

  intros A S v e s k env0 CL st1' MS.
  inv MS.  inv MK.

  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepCondTrue.
  inversion CL; try (apply Val.bool_of_val_int_true; done);
    try apply Val.bool_of_val_ptr_true.
  specialize (H14 sz). by rewrite <- H0 in H14.
  eapply steptau_weakstep; simpl. eapply StepNext.
  eapply step_weakstep; simpl; try eapply StepBlock.
  eapply match_stmt; try edone; 
  eby eapply match_Kwhile.

  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepBinop2.
  eapply steptau_weakstep; simpl; try eapply StepConst; try edone.
  eapply steptau_weakstep; simpl; try eapply StepBinop. 
    unfold eval_binop; unfold Cminorops.eval_binop.
  by rewrite H13 in CL; inv CL; simpl; rewrite H2.

  eapply steptau_weakstep; simpl; try eapply StepCondTrue. 
  unfold Vtrue. apply Val.bool_of_val_int_true; done.
  eapply steptau_weakstep; simpl. eapply StepNext.
  eapply step_weakstep; simpl; try eapply StepBlock.
  eapply match_stmt; try edone. 
  eby eapply match_Kwhile.

  Case "StepWhileFalse".

  intros v e s k env0 CL st1' MS.
  inv MS.  inv MK.

  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepCondFalse.
  inversion CL; try (by apply Val.bool_of_val_int_false).
    by specialize (H14 sz); rewrite <- H0 in H14.
  eapply steptau_weakstep; simpl;  try eapply StepExitSeq.
  eapply steptau_weakstep; simpl;  try eapply StepExitSeq.
  eapply step_weakstep; simpl; try  eapply StepExitBlock.
  eapply match_stmt; try edone. by eapply wt_Sskip.

  left; eexists; split.
  eapply steptau_weakstep; simpl; try  eapply StepBinop2.
  eapply steptau_weakstep; simpl; try  eapply StepConst; try edone.
  eapply steptau_weakstep; simpl; try  eapply StepBinop. 
    unfold eval_binop; unfold Cminorops.eval_binop.
  by rewrite H13 in CL; inv CL; simpl; rewrite Float.cmp_ne_eq, H2.

  eapply steptau_weakstep; simpl; try eapply StepCondFalse.
  unfold Vfalse. apply Val.bool_of_val_int_false; try done.
  eapply steptau_weakstep; simpl; try eapply StepExitSeq.
  eapply steptau_weakstep; simpl; try eapply StepExitSeq.
  eapply step_weakstep; simpl; try  eapply StepExitBlock.
  eapply match_stmt; try edone;  by eapply wt_Sskip.

  Case "StepContinueWhile".

  intros e s k env0 st1' MS.

  inv MS. inv TS. inv MK.
  generalize H4; intros.

  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepExitBlock.
  eapply steptau_weakstep; simpl. eapply StepNext.
  eapply steptau_weakstep; simpl; try eapply StepLoop.
  eapply step_weakstep; simpl;    try eapply StepSeq.
  unfold exit_if_false in H4. monadInv H4.
  eapply match_while; try edone; by apply wt_Swhile.
  
  Case "StepBreakWhile".

  intros e s k env0 st1' MS.

  inv MS. inv TS. inv MK.
  generalize H4; intros.

  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepExitBlock1.
  eapply steptau_weakstep; simpl; try eapply StepExitSeq.
  eapply step_weakstep; simpl;    try eapply StepExitBlock.
  eapply match_stmt; try edone;  by apply wt_Sskip.

  Case "StepDoWhile".

  intros s e k env0 st1' MS.

  inv MS. inv TS. monadInv H1.
  generalize EQ; intros EX.

  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepBlock.
  eapply steptau_weakstep; simpl; try eapply StepLoop.
  eapply steptau_weakstep; simpl; try eapply StepSeq.
  eapply step_weakstep; simpl;    try eapply StepBlock.
  eapply match_stmt; try edone; try by inv WT.
  eapply match_Kdowhile; try edone; by inv WT.

  left; eexists; split.
  eapply step_weakstep; simpl; try eapply StepBlock.
  eapply match_stmt; try edone; try by inv WT.
  eapply match_Kdowhile; try edone; by inv WT.


  Case "StepDoWhileTrue".

  intros v s e k env0 CL st1' MS.

  inv MS.  inv MK.
  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepCondTrue.
  inversion CL;
    try (apply Val.bool_of_val_int_true; done);
    try apply Val.bool_of_val_ptr_true.
  specialize (H14 sz). by rewrite <- H0 in H14.
  eapply steptau_weakstep; simpl. eapply StepNext.
  eapply steptau_weakstep; simpl; try eapply StepLoop.
  eapply step_weakstep; simpl; try eapply StepSeq.
  eapply match_dowhile; try edone; try by inv WT.
  by apply wt_Sdowhile. 

  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepBinop2.
  eapply steptau_weakstep; simpl; try eapply StepConst; try edone.
  eapply steptau_weakstep; simpl; try eapply StepBinop. 
    unfold eval_binop; unfold Cminorops.eval_binop.
  by rewrite H13 in CL; inv CL; simpl; rewrite H2.

  eapply steptau_weakstep; simpl; try eapply StepCondTrue. 
  unfold Vtrue. apply Val.bool_of_val_int_true; done.
  eapply steptau_weakstep; simpl. eapply StepNext.
  eapply steptau_weakstep; simpl; try eapply StepLoop.
  eapply step_weakstep; simpl;    try eapply StepSeq.
  eapply match_dowhile; try edone; try by inv WT. 
  by eapply wt_Sdowhile.

  Case "StepDoWhileFalse".

  intros v e s k env0 CL st1' MS.
  inv MS. inv MK.

  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepCondFalse.
  inversion CL;
    try (apply Val.bool_of_val_int_false; done).
    by specialize (H14 sz); rewrite <- H0 in H14.
  eapply steptau_weakstep; simpl; try eapply StepExitSeq.
  eapply step_weakstep; simpl;    try eapply StepExitBlock.
  eapply match_stmt; try edone.
  by eapply wt_Sskip.

  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepBinop2.
  eapply steptau_weakstep; simpl; try eapply StepConst; try edone.
  eapply steptau_weakstep; simpl; try eapply StepBinop. 
    unfold eval_binop; unfold Cminorops.eval_binop.
  by rewrite H13 in CL; inv CL; simpl; rewrite Float.cmp_ne_eq, H2.

  eapply steptau_weakstep; simpl; try eapply StepCondFalse. 
  unfold Vfalse. apply Val.bool_of_val_int_false; done.
  eapply steptau_weakstep; simpl; try eapply StepExitSeq.
  eapply step_weakstep; simpl; try eapply StepExitBlock.
  eapply match_stmt; try edone.
  by eapply wt_Sskip.


  Case "StepDoContinueWhile".

  intros s e k env0 st1' MS.

  inv MS. inv TS. inv MK.
  generalize H4; intros.

  unfold exit_if_false in H4. monadInv H4.
  unfold make_boolean in *.
  destruct (typeof e) as []_eqn : TE; try done;
  left; eexists; 
  try (split;
        [  eapply steptau_weakstep; simpl;  try (eapply StepExitBlock);
           eapply steptau_weakstep; simpl;  try (eapply StepNext);
           eapply step_weakstep; simpl; eapply StepCond
        |  try (eapply match_expr); try edone;
           eapply match_EKdowhile; try edone; 
           try (by inv WT); try (intros; rewrite TE; edone) ]).

  split; [  eapply steptau_weakstep; simpl; try eapply StepExitBlock;
            eapply steptau_weakstep; simpl; try eapply StepNext;
            eapply steptau_weakstep; simpl; try eapply StepCond;
            eapply step_weakstep; simpl;    try eapply StepBinop1
         |  eapply match_expr; try edone; try by inv WT;
            try (eapply match_EKdowhile_float); try edone; try by inv WT ].


  Case "StepDoBreakWhile".

  intros s e k env0 st1' MS.

  inv MS. inv TS. inv MK.
  generalize H4; intros.

  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepExitBlock1.
  eapply steptau_weakstep; simpl; try eapply StepExitSeq.
  eapply steptau_weakstep; simpl; try eapply StepExitSeq.
  eapply step_weakstep; simpl;    try eapply StepExitBlock.
  eapply match_stmt; try edone.
  by apply wt_Sskip.


  Case "StepForInit".

  intros s1 e2 s3 s k env0 st1' MS.
  inv MS. inv TS. 

  destruct (is_Sskip s1). 
  monadInv H1.
  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepBlock.
  eapply step_weakstep; simpl;    try eapply StepLoop.
  eapply match_forCond; try edone.

  monadInv H1.
  left; eexists; split.
  eapply step_weakstep; simpl; try eapply StepSeq.
  eapply match_stmt; try edone; try by inv WT.
  eapply match_KforCond; try edone; by inv WT.


  Case "StepForCond".

  intros e2 s3 s0 k env0 st1' MS.
  inv MS. inv MK. inv TS.

  generalize H4; intros.
  unfold exit_if_false in H4. unfold bind in H4.
  destruct (transl_expr e2) as []_eqn: TE.
  inv H4.
  unfold make_boolean. 
  destruct (typeof e2) as []_eqn : TY;
  left; eexists; 
  try (split;
        [ eapply steptau_weakstep; simpl; try (eapply StepNext);
          eapply steptau_weakstep; simpl; try (eapply StepBlock);
          eapply steptau_weakstep; simpl; try (eapply StepLoop);
          eapply steptau_weakstep; simpl; try (eapply StepSeq);
          eapply step_weakstep; simpl; eapply StepCond
        | try (eapply match_expr); try edone;
          eapply match_EKforTest; try edone; try (intros; rewrite TY; edone) ]).

  split; [ eapply steptau_weakstep; simpl; try eapply StepNext;
           eapply steptau_weakstep; simpl; try eapply StepBlock;
           eapply steptau_weakstep; simpl; try eapply StepLoop;
           eapply steptau_weakstep; simpl; try eapply StepSeq;
           eapply steptau_weakstep; simpl; try eapply StepCond;
           eapply step_weakstep; simpl;    try eapply StepBinop1
         |  eapply match_expr; try edone;
            try (eapply match_EKforTest_float); simpl; edone ].
  done.

  inv TS.
  generalize H4; intros.
  unfold exit_if_false in H4; monadInv H4.
  unfold make_boolean. 
  destruct (typeof e2) as []_eqn : TY;
  left; eexists; 
  try (split;
        [ eapply steptau_weakstep; simpl;  try(eapply StepNext);
          eapply steptau_weakstep; simpl;  try (eapply StepLoop);
          eapply steptau_weakstep; simpl;  try (eapply StepSeq);
          eapply step_weakstep; simpl;  eapply StepCond
        | try (eapply match_expr); try edone;
          eapply match_EKforTest; try edone;
          try (intros; rewrite TY; edone) ]).

  split; [  eapply steptau_weakstep; simpl; try eapply StepNext;
            eapply steptau_weakstep; simpl; try eapply StepLoop;
            eapply steptau_weakstep; simpl; try eapply StepSeq;
            eapply steptau_weakstep; simpl; try eapply StepCond;
            eapply step_weakstep; simpl;    try eapply StepBinop1
         |  eapply match_expr; try edone;
            try (eapply match_EKforTest_float); simpl; edone ].

  generalize H6; intros. 
  unfold exit_if_false in H6; monadInv H6.
  unfold make_boolean. 
  destruct (typeof e2) as []_eqn : TY;
  left; eexists; 
  try (split;
        [ eapply steptau_weakstep; simpl;  try (eapply StepSeq);
          eapply step_weakstep; simpl; eapply StepCond
        | try (eapply match_expr); try inv WT; try edone ;
          eapply match_EKforTest; simpl; try edone; try (intros; rewrite TY); edone ]).


  split; [ eapply steptau_weakstep; simpl; try eapply StepSeq;
           eapply steptau_weakstep; simpl; try eapply StepCond;
           eapply step_weakstep; simpl;    try eapply StepBinop1
         |  eapply match_expr; inv WT; try edone ;
            try (eapply match_EKforTest_float); simpl; edone ].
    
  Case "StepForTrue".

  intros v e2 s3 s0 k env0 CL st1' MS.
  
  inv MS. inv MK.
  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepCondTrue.
  inversion CL; 
   try (apply Val.bool_of_val_int_true; done); 
   try apply Val.bool_of_val_ptr_true.
  specialize (H17 sz); clarify.
  rewrite H0 in H17; intuition.
  eapply steptau_weakstep; simpl; try eapply StepNext.
  eapply steptau_weakstep; simpl; try eapply StepSeq.
  eapply step_weakstep; simpl;    try eapply StepBlock.
  eapply match_stmt; try edone.
  eby eapply match_KforIncr.
  
  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepBinop2.
  eapply steptau_weakstep; simpl; try eapply StepConst; try edone.
  eapply steptau_weakstep; simpl; try eapply StepBinop.
    unfold eval_binop; unfold Cminorops.eval_binop.
  by rewrite H13 in CL; inv CL; simpl; rewrite H2.

  eapply steptau_weakstep; simpl; try eapply StepCondTrue.  
  unfold Vtrue. apply Val.bool_of_val_int_true; done.
  eapply steptau_weakstep; simpl; try eapply StepNext.
  eapply steptau_weakstep; simpl; try eapply StepSeq.
  eapply step_weakstep; simpl;    try eapply StepBlock.
  eapply match_stmt; try edone; try by inv WT.
  eapply match_KforIncr; try edone; 
  by inv WT.

  Case "StepForFalse".

  intros v e2 s3 s0 k env0 CL st1' MS.
  inv MS.  inv MK.

  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepCondFalse.
  inversion CL;
    try (apply Val.bool_of_val_int_false; done).
    by specialize (H17 sz); rewrite <- H0 in H17.
  eapply steptau_weakstep; simpl; try eapply StepExitSeq.
  eapply steptau_weakstep; simpl; try eapply StepExitSeq.
  eapply step_weakstep; simpl;    try eapply StepExitBlock.
  eapply match_stmt; try edone.
  by eapply wt_Sskip.

  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepBinop2.
  eapply steptau_weakstep; simpl; try eby eapply StepConst. 
  eapply steptau_weakstep; simpl; try eapply StepBinop. 
    unfold eval_binop; unfold Cminorops.eval_binop.
  by rewrite H13 in CL; inv CL; simpl; rewrite Float.cmp_ne_eq, H2.

  eapply steptau_weakstep; simpl; try eapply StepCondFalse. 
  unfold Vfalse. by apply Val.bool_of_val_int_false.
  eapply steptau_weakstep; simpl; try eapply StepExitSeq.
  eapply steptau_weakstep; simpl; try eapply StepExitSeq.
  eapply step_weakstep; simpl;    try eapply StepExitBlock.
  eapply match_stmt; try edone.
  by eapply wt_Sskip.

  Case "StepForIncr".

  intros e2 s3 s0 k env0 st1' MS.
  inv MS. inv MK. inv TS.

  left; eexists; split.
  eapply steptau_weakstep; simpl;  try eapply StepSkipBlock.
  eapply step_weakstep; simpl;     try eapply StepNext.
  eapply match_stmt; try edone.
  eby eapply match_KforCondIncr.

  Case "StepForBreak".

  intros e2 s3 s k env0 st1' MS.
  inv MS.  inv TS. inv MK.
 
  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepExitBlock1;
  eapply steptau_weakstep; simpl; try eapply StepExitSeq;
  eapply steptau_weakstep; simpl; try eapply StepExitSeq;
  eapply step_weakstep;    simpl; try eapply StepExitBlock.
  eapply match_stmt; try edone.
  eby apply wt_Sskip.


  Case "StepForContinue".

  intros e2 s3 s k env0 st1' MS.
  inv MS. inv TS. inv MK.

  left; eexists; split.
  eapply steptau_weakstep; simpl; try eapply StepExitBlock;
  eapply step_weakstep;    simpl; try eapply StepNext.
  eapply match_stmt; try edone.
  eby eapply match_KforCondIncr.

  Case "StepReturnNone".
  intros k envp ps fn envpp k' CC R PS st1' MS.
  inv MS. inv TS.

  pose proof 
    (match_cont_call_cont _ _ _ _
       (typeEnvOfCont prog (Clight.call_cont k)) 
       _ _ _ _ _ nbrk ncnt MK) 
    as MKCC.
  rewrite CC in MKCC. inv MKCC.
  inv H5. monadInv H1. 
  unfold match_lhs in H11.
   destruct o'; try done.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepReturnNone. rewrite <- H4. edone.
  unfold transl_function in EQ. monadInv EQ. simpl.
  unfold opttyp_of_type. rewrite R; try discriminate. done.
  eapply match_stmt; try edone.
  pose proof (match_sorted_pointers _ typEnv envp tenv MENV).
  rewrite H0.
  eapply match_Kfree; try edone. 
  eapply wt_Sskip.

  Case "StepReturn1".

  intros p ps opt_v k env0 st1' MS.
  inv MS. inv TS. inv MK.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepFree; try edone.
  eapply match_stmt; try edone; vauto.

  Case "StepReturnSome".

  intros until 0. intros <- GFD R st1' MS.
  destruct (Clight.call_cont k) as [] _eqn : CC; inv GFD; [].
  inv MS. inv TS. monadInv H1.

  pose proof (match_cont_call_cont _ _ _ _
                (typeEnvOfCont prog (Clight.call_cont k)) _ _ _ _ _ nbrk ncnt MK) 
    as MKCC.
  rewrite CC in MKCC. inv MKCC.
  inv H5.   monadInv H1. 
  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepReturnSome; try edone.
  rewrite <- H4; edone.
  unfold transl_function in EQ0; monadInv EQ0; simpl.
  unfold opttyp_of_type.
  destruct (fn_return fn); try discriminate.
  intuition.
  eapply match_expr; try edone.
  eapply match_EKreturn; try edone. inv WT. by inv H1.

(*
  intros e k envp ps p ty fn envpp k' CC R PS st1' MS.
  inv MS. inv TS. monadInv H1.

  pose proof (match_cont_call_cont _ _ _ _
                (typeEnvOfCont prog (Clight.call_cont k)) _ _ _ _ _ nbrk ncnt MK) 
    as MKCC.
  rewrite CC in MKCC. inv MKCC.
  destruct o'; try done. 
  inv H5.   monadInv H1. 
  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepReturnSome; try edone.
  rewrite <- H4; edone.
  unfold transl_function in EQ0; monadInv EQ0; simpl.
  unfold opttyp_of_type.
  destruct (fn_return fn); try discriminate.
  intuition.
  eapply match_expr; try edone.
  pose proof (match_sorted_pointers _ typEnv envp tenv MENV).
  rewrite H0.
  eapply match_EKreturn; try edone.
  inv WT. 
  by inv H1.
*)

  Case "StepReturnSome1".  

  intros v k env0 ps Eps st1' MS.
  inv MS. inv MK.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepReturnSome1; try edone.
  eapply match_stmt; try edone.
  rewrite (match_sorted_pointers _ typEnv env0 tenv MENV).
  eapply match_Kfree; try edone.
  apply wt_Sskip.

  Case "StepSwitch".

  intros e ls k env0 st1' MS.
  inv MS. inv TS. monadInv H1.

  left; eexists; split.
  eapply steptau_weakstep; simpl.
  eapply StepBlock.
  eapply step_weakstep; simpl.
  eapply StepSwitch.
  eapply match_expr; try edone; try by inv WT.
  eapply match_EKswitch; try edone.
  by inv WT.

  left; eexists; split.  
  eapply step_weakstep; simpl.
  eapply StepSwitch.
  eapply match_expr; try edone.
  eapply match_EKswitch; try edone.
  by inv WT. by inv WT.

  Case "StepSelectSwitch".

  intros n ls k env0 s0 SO st1' MS.
  inv MS. inv MK.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepSelect.
  eapply match_stmt; try edone.
  eapply match_Kswitch; try edone.
  apply wt_seq_of_labeled_statement.  
  by apply wt_select_switch. 
  apply transl_lbl_stmt_2.
  by apply transl_lbl_stmt_1. 

  Case "StepBreakSwitch".

  intros k env0 st1' MS.
  inv MS. inv MK. inv TS.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepExitBlock.
  eapply match_stmt; try edone.
  eapply wt_Sskip.

  Case "StepContinueSwitch".

  intros k env0 st1' MS.
  inv MS. inv MK. inv TS.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepExitBlock1.
  eby eapply match_stmt.

  Case "StepLabel".

  intros l s0 k env0 st1' MS.
  inv MS. inv TS. monadInv H1.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepLabel.
  eapply match_stmt; try edone. 
  by inv WT.

  Case "StepGoto".

  intros l k env0 s' k'' k' vn CC GF FL st1' MS.
  inv MS. inv TS. inv GF.

  pose proof (match_cont_call_cont _ _ _ _ typEnv _ nbrk ncnt k tk 
                   1%nat 0%nat MK) as MKCC.
  inversion MKCC;
    try (rewrite <- H7 in H1; try done);
    try (rewrite <- H0 in H1; try done).
 
  unfold transl_fundef in H3. clarify.
  unfold Clight.get_fundef in H1. rewrite <- H0 in WTB. inv H1.
   destruct (Clight.call_cont k); try discriminate. monadInv H3.
  unfold transl_function in EQ. monadInv EQ.  
  simpl in WTB.

  pose proof (transl_find_label _ _ l _ _ typEnv  (Csyntax.fn_body vn) 
                1%nat 0%nat 
                (Clight.Kcall o0 f e c)  x2 (call_cont tk)
                WTB EQ1 MKCC).

   rewrite FL in H1.
   generalize H1.
   intros [ts' [tk' [nbrk'0 [ncnt'0 [ F [ T [ M W ]]]]]]].

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepGoto; try edone.
  rewrite <- H2; edone.
  inversion H0; unfold fn_body; edone.
  eapply match_stmt. apply MENV.
  rewrite <- (match_call_cont_label l 
               (Csyntax.fn_body vn) s' 
               (Clight.Kcall o0 f e c) k'' FL). rewrite <- H0.
  simpl. done. edone. done. done.

  Case "StepFunctionInternal".
   
  intros vs opt_lhs_p fd env0 k args fn ARGS FD st1' MS.
  inv MS. inversion H8. monadInv H1.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepFunctionInternal. edone.
  inv WT. inv H2.
  unfold transl_function in EQ.  monadInv EQ.
  inv H8.  monadInv H3.
  pose proof (transl_names_norepet 
                (Csyntax.fn_params fn) (Csyntax.fn_vars fn) 
                (signature_of_function fn) x0 x1 x2 H0 EQ0 EQ).  edone.
  apply (match_Alloc _ _ (global_typenv prog) _ _ nbrk ncnt).
  apply (match_globalenv_match_env_empty _ (global_typenv prog) MG).
  unfold transl_function in EQ. monadInv EQ.
  by apply (transl_fn_variables _ _ (signature_of_function fn) _ _ x2).
  intros id ty INp. right.
  apply in_or_app. by left.
  inv WT. inv H2. unfold var_names in H0. by rewrite map_app. 
  inv WT. by inv H2. done.
  eby eapply match_Kcall.
  
  Case "StepAllocLocal".

  intros vs id ty args k env p n n' st1' MS.
  inv MS. inv MK; try edone.
  inv H12. monadInv H1.
  unfold transl_function in TF. monadInv TF. 

  pose proof (transl_fn_variables (Csyntax.fn_params fn) (Csyntax.fn_vars fn)
                   (signature_of_function fn) x x0 x1 EQ0 EQ2).

  inv H0. inv TV. 
  destruct (var_kind_of_type ty) as [c|]_eqn : VK'; monadInv H1; simpl.

  left; eexists; split.
  eapply step_weakstep; simpl.
  pose proof (sizeof_var_kind_of_type ty c).
  rewrite VK' in H0.  intuition. rewrite <- H1.
  apply StepAllocLocal.
  apply (match_Alloc _ _ (Ctyping.add_var typEnv (id,ty))
                         (tenv ! id <- (p, c))
                         (env ! id <- p) nbrk ncnt).
  apply match_env_set. 
  unfold match_var_kind.  
  destruct ty; try done;
    simpl in VK'; try destruct i; try destruct s; 
      try destruct f; simpl; try by inv VK'.
  done. done.
  intros id0 ty0 IN.
  destruct (PARS _ _ IN) as [[TE NIN'] | IN'].
    left. split. unfold add_var. rewrite PTree.gso. done. 
      intros ->. apply NIN'. by left.
    intro. elim NIN'. by right.
  simpl in IN'. destruct IN' as [E | IN'].
    inv E.
    left. split.
      unfold add_var. simpl. by rewrite PTree.gss.
    by inv ND.
  by right. 
  by inv ND. 
  done.  done.
  eapply match_Kcall; try edone.
  simpl. unfold bind. rewrite EQ. done.

  Case "StepBindArgsStart".

  intros vs lhs fd envp k envpp fn args ARGS FD ST MS.
  inv MS. inv MK.
  inv H5. inv TV. inv H13. monadInv H1.
  
  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepBindArgsStart; try edone.
  apply (match_Bind _ _ typEnv _ _ nbrk ncnt); try edone.
  unfold transl_function in TF. monadInv TF. done.
  intros id ty IN. by destruct (PARS _ _ IN) as [[? _]|?]. 
  eapply match_Kcall; try edone. simpl.
   unfold bind. by rewrite TF.

  Case "StepBindArgs".

  intros fn v vs id ty args k env0 p c v2 L TC CVC st1' MS.
  inv MS. inv MK.
  unfold transl_fundef in H12. monadInv H12.

  inv ARGS. destruct (chunk_of_type ty); try done. 
   monadInv H1. simpl. 

  left; eexists; split.
  eapply step_weakstep; simpl.

  apply StepBindArgs; try done.
  specialize (PARS _ _ (in_eq _ _)).
  inv MENV. destruct (me_local id p L)  as [vk' [ty' [C1 [C2 C3]]]]. 
  rewrite PARS in C1. inv C1. unfold match_var_kind in C2.
  unfold Clight.type_to_chunk in TC. destruct access_mode; try done; [].
  by inv TC.
  apply (match_Bind _ _ typEnv _ _ nbrk ncnt); try edone. 
   intros id' ty' IN'; apply PARS, in_cons, IN'.
  eapply match_Kcall; try edone.
  simpl. unfold bind. rewrite EQ; done.

  Case "StepTransferFun".

  intros fn k env0 s B st1' MS.
  inv MS. inv MK.

  left; eexists; split.
  eapply step_weakstep; simpl.
  destruct targs; [|done]. simpl.
  eapply StepTransferFun.
  eapply match_stmt; try edone.
  eapply match_Kcall; try edone.
  inv H12. monadInv H1. 
  unfold transl_function in EQ. monadInv EQ.
  eby simpl.

  Case "StepExternalCall".

  intros vs opt_lhs_p fd env k id evs tys ty T FD vs' st1' MS.
  inv MS. 

  left; eexists; split.
  eapply step_weakstep; simpl.
  unfold transl_fundef in H8. inv H8.
  eapply StepExternalCall. done.
  eapply match_ext_call; try edone.

  Case "StepExternalReturn".
  
  intros opt_lhs_p fd k env typ0 evl v id tys ty HT FD OPT ve st1' MS.
  inv MS.

  left; eexists; split.
  eapply step_weakstep; simpl.
  unfold transl_fundef in H6. inversion H6.
  inv H0. rewrite H6.
  eapply StepExternalReturn.  done.  rewrite H6 in HT. edone. done.
  eby eapply match_ext_ret.

  Case "StepExternalStoreSomeLocal".
 
  intros id ty v k env p c v2 ENV TC CVC st1' MS.
  inv MS.
  
    left; eexists; split.
    eapply step_weakstep; simpl.
    destruct topt_lhs. 2 : done. inv H5.
    eapply StepExternalStoreSome.
    inv MENV.
    inv WTS. destruct (me_local _ _ ENV) as [vk [ty' (TYPENV & VK & TENV)]].
    unfold Clight.type_to_chunk in TC. unfold match_var_kind in VK.
    rewrite H1 in TYPENV; inv TYPENV.
    destruct access_mode; try done; []. inv TC.
    by apply eval_var_ref_local. 
    by econstructor; try edone; vauto.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepAssign. 
  inv MENV.
  inv WTS. destruct (me_local _ _ ENV) as [vk [ty' (TYPENV & VK & TENV)]].
  unfold Clight.type_to_chunk in TC. unfold match_var_kind in VK.
  rewrite H1 in TYPENV; inv TYPENV.
  destruct access_mode; try done; []. inv TC.
  by apply eval_var_ref_local. 
  by econstructor; try edone; vauto.

  Case "StepExternalStoreSomeGlobal".
  
  intros id ty v k env p c v2 ENV GE TC CVC st1' MS.
  inv MS.
  
    left; eexists; split.
    eapply step_weakstep; simpl.
    destruct topt_lhs. 2 : done. inv H5.
    eapply StepExternalStoreSome.
    inv MENV.
    inv WTS. destruct (me_global _ _ ENV H1) as [TE CHUNK].
    unfold Clight.type_to_chunk in TC. specialize (CHUNK c).
    destruct access_mode; try done; []. inv TC.
    apply eval_var_ref_global. done. unfold Csharpminor.ge. 
    by rewrite (symbols_preserved ge). 
    by auto. by econstructor; try edone; vauto. 

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepAssign.
  inv MENV.
  inv WTS. destruct (me_global _ _ ENV H1) as [TE CHUNK].
  unfold Clight.type_to_chunk in TC. specialize (CHUNK c).
  destruct access_mode; try done; []. inv TC.
  apply eval_var_ref_global. done. unfold Csharpminor.ge. 
  by rewrite (symbols_preserved ge). 
  by auto. by econstructor; try edone; vauto. 

  Case "StepExternalStoreNone".
  
  intros v k env st1' MS.
  inv MS. left; eexists; split. eapply step_weakstep. 
  simpl. destruct topt_lhs; [done|].  
  eapply StepExternalStoreNone. 
  by econstructor; try edone; vauto.

  Case "StepSkip".
  
  intros s2 k env st1' MS.
  inv MS. inv TS. inv MK.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepNext.
  eby eapply match_stmt.

  Case "StepWhileLoop".

  intros e s k env st1' MS.
  inv MS. inv TS. inv MK.

  left; eexists; split.
  eapply steptau_weakstep; simpl.
  eapply StepSkipBlock.
  eapply steptau_weakstep; simpl.
  eapply StepNext.
  eapply steptau_weakstep; simpl.
  eapply StepLoop.
  eapply step_weakstep; simpl.
  eapply StepSeq.
  eapply match_while; try edone; vauto.

  Case "StepDoWhileLoop".

  intros s e k env st1' MS.
  inv MS. inv TS. inv MK.

  generalize H4; intros.
  unfold exit_if_false in H4. monadInv H4.
  unfold make_boolean in *.
  destruct (typeof e) as []_eqn : TE; try done;
  left; eexists; 
  try (split;
        [  eapply steptau_weakstep; simpl;  try (eapply StepSkipBlock);
           eapply steptau_weakstep; simpl;  try (eapply StepNext);
           eapply step_weakstep; simpl; eapply StepCond
        |  try (eapply match_expr); try edone;
           eapply match_EKdowhile; try edone; 
           try (by inv WT); try (intros; rewrite TE; edone) ]).

  split; [  eapply steptau_weakstep; simpl; try eapply StepSkipBlock;
            eapply steptau_weakstep; simpl; try eapply StepNext;
            eapply steptau_weakstep; simpl; try eapply StepCond;
            eapply step_weakstep; simpl;    try eapply StepBinop1
         |  eapply match_expr; try edone; try by inv WT;
            try (eapply match_EKdowhile_float); try edone; try by inv WT ].

  Case "StepSkipSwitch".

  intros k env st1' MS.
  inv MS. inv TS. inv MK.

  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepSkipBlock.
  eby eapply match_stmt.

  Case "StepReturnNoneFinish".
  intros until fd. intros CC st1' MS.
  inv MS. inv MK. inv TS.

  apply (match_cont_call_cont _ _ _ _ typEnv _ _ _ _ _ nbrk ncnt) in MK0. 
   rewrite CC in MK0. inv MK0.
   destruct o'. done.
  left; eexists; split.
  eapply step_weakstep. simpl.
  eapply StepReturnNoneFinish. symmetry. edone.
  eapply match_stmt; try edone; vauto.

  Case "StepReturnSomeFinishLocal".

  intros until 0. intros TC ENV CC CVC st1' MS.
  inv MS. inv MK. inv TS.

  apply (match_cont_call_cont _ _ _ _ typEnv _ _ _ _ _ nbrk ncnt) in MK0. 
   rewrite CC in MK0. inv MK0.
   destruct o'. 2 : done.
  left; eexists; split.
  eapply step_weakstep. simpl.
  eapply StepReturnSomeFinish. eby symmetry.
  inv H14.
  inv WTS. destruct (me_local _ _ ENV) as [vk [ty' (TYPENV & VK & TENV)]].
  unfold Clight.type_to_chunk in TC. unfold match_var_kind in VK.
  rewrite H1 in TYPENV; inv TYPENV.
  destruct access_mode; try done; []. inv TC. inv H11.
  by apply eval_var_ref_local. 
  by econstructor; try edone; vauto.

  Case "StepReturnSomeFinishGlobal".

  intros until 0. intros TC ENV GS CC CVC st1' MS.
  inv MS. 
   inv MK. inv TS.
   apply (match_cont_call_cont _ _ _ _ typEnv _ _ _ _ _ nbrk ncnt) in MK0. 
    rewrite CC in MK0. inv MK0.
    destruct o'. 2 : done.
   left; eexists; split.
     eapply step_weakstep. simpl.
     eapply StepReturnSomeFinish. eby symmetry.
   inv H14.
  inv WTS. destruct (me_global _ _ ENV H1) as [TE CHUNK].
  unfold Clight.type_to_chunk in TC. specialize (CHUNK c).
  destruct access_mode; try done; []. inv TC. inv H11.
  apply eval_var_ref_global. done. unfold Csharpminor.ge. by rewrite (symbols_preserved ge). 
  by auto. by econstructor; try edone; vauto.

  Case "StepStop".

  intros env st1' MS.
  inv MS. inv TS. inversion MK. rewrite <- H6 in MK.
  
  left; eexists; split.
  eapply step_weakstep; simpl.
  eapply StepStop.
  eby eapply match_stmt.
Qed.


(** The following lemmas establish the matching property
  between the global environments constructed at the beginning
  of program execution. *)

Definition globvarenv 
    (gv: gvarenv)
    (vars: list (ident * list init_data * var_kind)) :=
  List.fold_left
    (fun gve x => match x with (id, init, k) => PTree.set id k gve end)
    vars gv.

Definition type_not_by_value (ty: type) : Prop :=
  match access_mode ty with
  | By_value _ => False
  | _ => True
  end.

Lemma add_global_funs_charact:
  forall fns tyenv,
  (forall id ty, tyenv!id = Some ty -> type_not_by_value ty) ->
  (forall id ty, (add_global_funs tyenv fns)!id = Some ty -> type_not_by_value ty).
Proof.
  induction fns; simpl; intros.
  eauto.
  apply IHfns with (add_global_fun tyenv a) id.
  intros until ty0. destruct a as [id1 fn1]. 
  unfold add_global_fun; simpl. rewrite PTree.gsspec.
  destruct (peq id0 id1). 
  intros. inversion H1. 
  unfold type_of_fundef. destruct fn1; exact I.
  eauto.
  auto.
Qed.

Definition global_fun_typenv :=
  add_global_funs (PTree.empty type) prog.(prog_funct).

Lemma add_global_funs_match_global_env:
  match_globalenv global_fun_typenv (PTree.empty var_kind).
Proof.
  intros; red; intros.
  assert (type_not_by_value ty).
    apply add_global_funs_charact with (prog_funct prog) (PTree.empty type) id.
    intros until ty0. rewrite PTree.gempty. congruence.
    assumption.
  red in H1. rewrite H0 in H1. contradiction.
Qed.

Lemma add_global_var_match_globalenv:
  forall vars tenv gv tvars,
  match_globalenv tenv gv ->
  map_partial Ast.prefix_var_name transl_globvar vars = OK tvars ->
  match_globalenv (add_global_vars tenv vars) (globvarenv gv tvars).
Proof.
  induction vars; simpl.
  intros. inversion H0. assumption.
  destruct a as [[id init] ty]. intros until tvars; intro.
  caseEq (transl_globvar ty); simpl; try congruence. intros vk VK. 
  caseEq (map_partial Ast.prefix_var_name transl_globvar vars); simpl; try congruence. intros tvars' EQ1 EQ2.
  inversion EQ2; clear EQ2. simpl. 
  apply IHvars; auto.
  red. intros until chunk. repeat rewrite PTree.gsspec. 
  destruct (peq id0 id); intros.
  inversion H0; clear H0; subst id0 ty0. 
  generalize (var_kind_by_value _ _ H2). 
  unfold transl_globvar in VK. congruence.
  red in H. eauto. 
Qed.

Lemma match_global_typenv:
  match_globalenv (global_typenv prog) (global_var_env tprog).
Proof.
  change (global_var_env tprog)
    with (globvarenv (PTree.empty var_kind) (prog_vars tprog)).
  unfold global_typenv.
  apply add_global_var_match_globalenv.
  apply add_global_funs_match_global_env. 
  unfold transl_program in TRANSL. monadInv TRANSL. auto.
Qed.

(** Forward simulation in a neat packaging. *)
Lemma cshmgen_forward_sim:
  match_globalenv (global_typenv prog) (snd tge) ->
  @forward_sim _ lts tlts match_states order.
Proof.
  intro MGE.
  split. (* wellfoundedness *)
    exact (well_founded_ltof _ measure).
  (* forward simulation *)
  intros s t l s' ST MS.
  destruct (cshmgen_step_correct _ _ _ ST MGE _ MS)
    as [WS | (MLT & Ltau & MS')].
  - by right; left.
  - by right; right.
Qed.

(** Backward per-thread simulation relation and well_founded order. *)
Definition bsim_rel := @bsr _ lts tlts match_states.
Definition bsim_order := @bsc _ tlts.

(** And a proof of the simulation... *)
Lemma cshmgen_backward_sim:
  match_globalenv (global_typenv prog) (snd tge) ->
  @backward_sim _ lts tlts false bsim_rel bsim_order.
Proof.
  intro MGE.
  eapply forward_to_backward_sim; unfold lts.
  - unfold receptive. apply ( Clight.cl_sem.(SEM_receptive) ge).
  - unfold determinate. apply (cs_sem.(SEM_determinate) tge).
  - apply (Clight.cl_sem.(SEM_progress_dec)).
  - apply cshmgen_forward_sim. apply MGE.
Qed.


Lemma length_pars_eq:
  forall p,
    length (typlist_of_typelist (type_of_params p)) = length p.
Proof.
  induction p as [|[] p IH]. done. 
  simpl; eauto.
Qed.  

(** Initialisation of the per-thread simulation. *)
Lemma cshmgen_init:
  forall p vs,
    match_globalenv (global_typenv prog) (snd tge) ->
    match Clight.cl_init ge p vs, cs_init tge p vs with
      | Some s, Some t => match_states s t
      | None, None => True
      | _, _ => False
    end.
Proof.
  intros p vs MGE.
  unfold Clight.cl_init, cs_init, Csharpminor.ge.
  pose proof TRANSF as [_ FP]. specialize (FP p).
  destruct (Genv.find_funct_ptr ge p) as [] _eqn : Ef;
    destruct (Genv.find_funct_ptr (fst tge) p); try done; [].
  destruct f; destruct f0; try done; pose proof FP as FP'; monadInv FP.
    destruct f; destruct f0; try done. monadInv EQ. simpl.
  rewrite !length_pars_eq. destruct beq_nat; [|done].
  eapply match_call with (typEnv := (global_typenv prog))
                         (nbrk := 0%nat)(ncnt := 0%nat); vauto. 
  - exact (match_globalenv_match_env_empty _ (global_typenv prog) MGE).
  - inv WTPROG. destruct (globenv_fn_in _ _ Ef) as [id IN].
    eby eapply wt_program_funct.
Qed.

End CLIGHT_CSHM_SIM.

(** Full relation of global environments. *)
Definition full_genv_rel (sge : Clight.cl_sem.(SEM_GE)) (tge : cs_sem.(SEM_GE)) :=
  genv_rel sge (fst tge) /\
  exists prog, 
    match_globalenv (global_typenv prog) (snd tge) /\
    wt_program prog /\
    (forall p f,
       Genv.find_funct_ptr sge p = Some f ->
       exists id : ident, In (id, f) (prog_funct prog)) /\
    exists tprog,
      transl_program prog = OK tprog.

(** Program matching. *)
Definition cl_cs_match_prg (prog : Clight.cl_sem.(SEM_PRG)) 
                           (tprog : cs_sem.(SEM_PRG)) : Prop := 
  typecheck_program prog /\ transl_program prog = OK tprog.

(** Full backward per-thread simulation: it also packages the Clight program
    and necessary well-formedness properties of the program. *)
Definition full_bsim_rel (ge : SEM_GE Clight.cl_sem) (tge : SEM_GE cs_sem)
                         (css : SEM_ST cs_sem) (cls : SEM_ST Clight.cl_sem) :=
  exists prog, 
    match_globalenv (global_typenv prog) (snd tge) /\
    wt_program prog /\
    (forall p f,
       Genv.find_funct_ptr ge p = Some f ->
       exists id : ident, In (id, f) (prog_funct prog)) /\
    bsim_rel prog ge tge css cls.

(** Whole-system simulation theorem. *)
Theorem clight_cshm_sim Mm : 
  Sim.sim Mm Mm Clight.cl_sem cs_sem cl_cs_match_prg.
Proof.
  eapply (MCsim.sim (false_pure_load_cond Mm) _ _ 
            full_genv_rel full_bsim_rel (fun _ => bsim_order)); intros; simpl.
  - destruct GENVR as [[GR FR] _].
    rewrite GR.
    by rewrite (transform_partial_program2_main _ _ _ (proj2 MP)).
  - destruct INIT as [GEINIT Evk]. simpl in *.
    destruct MP as [WT MP].
    unfold cl_cs_match_prg, transl_program in MP.
    pose proof (transform_partial_program2_match _ _ _ MP) as MPRG.
    destruct (Genv.exists_matching_genv_and_mem_rev MPRG GEINIT)
      as [sge (SGEINIT & GENVM)].
    exists sge.
    split. exact SGEINIT.
    split. exact GENVM.
    exists src_prog. 
    split. rewrite Evk. by apply match_global_typenv.
    split. by apply typecheck_program_correct. 
    split.
      intros p f FF.
      refine (Genv.find_funct_ptr_prop
        (fun f => exists id, In (id, f) src_prog.(prog_funct)) SGEINIT _ FF). 
      intros id' f' IN. eby eexists.
    by exists tgt_prog.
  - destruct GENVR as [GER [prog (MGE & WT & INP & _)]].
    pose proof (cshmgen_init _ _ _ WT GER INP fnp args MGE) as SHI.
    simpl in INIT; rewrite INIT in SHI.
    destruct (Clight.cl_init sge fnp args) as [shi|]; [|done].
    exists shi. split. done. 
    exists prog. 
    repeat (split; [done|]).
    by apply fsr_in_bsr. 
  - destruct GENVR as [GER [prog (MGE & WT & INP & _)]].
    pose proof (cshmgen_init _ _ _ WT GER INP fnp args MGE) as SHI.
    simpl in INITF; rewrite INITF in SHI.
    by destruct Clight.cl_init.
  - destruct GENR as [GER [prog (MGE & WT & INP & [tprog MP])]].
    split. 
      by destruct (cshmgen_backward_sim prog sge tge WT GER INP MGE).
    split. 
      intros until 0. intros STUCK SIM.
      destruct SIM as [p' (MGE' & WT' & INP' & BS')].
      destruct (cshmgen_backward_sim p' sge tge WT' GER INP' MGE')
        as (_ & SS & _).
      eby eapply SS.
    intros until 0. intros ST BR.
    destruct BR as [p' (MGE' & WT' & INP' & BS')].
    destruct (cshmgen_backward_sim p' sge tge WT' GER INP' MGE')
      as (_ & _ & SIM).
    destruct (SIM _ _ _ _ ST BS') as [[s' [TAU SR]] | [(ISTAU & SR & ORD) | 
      [(? & PSEUDOTAU) | [(ISFENCE & l0 & TS & SR)|ERROR]]]].
    + by left; exists s'; split; [|exists p'].
    + by right; left; split; [|split; [by exists p'|]].
    + done. 
    + by right; right; right; left; split; [edone|eexists; vauto].
    by right; right; right; right.
Qed.

