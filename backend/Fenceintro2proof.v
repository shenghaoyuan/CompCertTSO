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
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Fenceintro2.
Require Import Memcomp Traces.
Require Import Simulations MCsimulation.
Require Import Libtactics.

Definition genv_rel : genv -> genv -> Prop :=
 (fun x y => Genv.genv_match (fun a b => transf_fundef a = b) y x).

Section PRESERVATION.

(** Assume fixed global environments that are related: *)
Variables (ge tge : genv).
Hypothesis TRANSF: genv_rel ge tge.

Let s_lts := (mklts thread_labels (rtl_step ge)).
Let t_lts := (mklts thread_labels (rtl_step tge)).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof.
  intros; pose proof (proj2 TRANSF v).
  destruct (Genv.find_funct_ptr ge v);
   destruct (Genv.find_funct_ptr tge v); try done.
  clarify; eexists; done.
Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof.
  intros; destruct v as [| |p|]; try done; simpl in *.
  apply function_ptr_translated; done.
Qed.

Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. by intros; destruct TRANSF. Qed.

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof. by intros [|]. Qed.

Lemma find_function_translated:
  forall ros ls f,
  find_function ge ros ls = Some f ->
  find_function tge ros ls = Some (transf_fundef f).
Proof.
  intros [l|] ls f; simpl.
    destruct (ls # l); try done; apply functions_translated; done.
  rewrite symbols_preserved; destruct (Genv.find_symbol ge i); try done.
  apply function_ptr_translated; done.
Qed.

Lemma function_ptr_translated_back:
  forall v f,
  Genv.find_funct_ptr tge v = Some f ->
  exists f', Genv.find_funct_ptr ge v = Some f' /\ f = (transf_fundef f').
Proof.
  intros; pose proof (proj2 TRANSF v).
  destruct (Genv.find_funct_ptr ge v);
    destruct (Genv.find_funct_ptr tge v); clarify; vauto. 
Qed.

Lemma functions_translated_back:
  forall v f,
  Genv.find_funct tge v = Some f ->
  exists f', Genv.find_funct ge v = Some f' /\ f = (transf_fundef f').
Proof.
  by intros [| |p|]; intros; clarify; apply function_ptr_translated_back.
Qed.

Lemma find_function_translated_back:
  forall ros ls f,
  find_function tge ros ls = Some f ->
  exists f', find_function ge ros ls = Some f' /\ f = (transf_fundef f').
Proof.
  intros [l|] ls f; simpl.
    destruct (ls # l); try done; apply functions_translated_back; done.
  rewrite symbols_preserved; destruct (Genv.find_symbol ge i); try done.
  apply function_ptr_translated_back; done.
Qed.

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
   match_stackframe_intro:
      forall res c sp pc rs x y z,
    match_stackframes
        (Stackframe res c sp pc rs)
        (Stackframe res (transf_code x y z c) sp pc rs).

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s c sp pc rs s' x y z
           (STACKS: list_forall2 match_stackframes s s'),
      match_states (State s c sp pc rs)
                   (State s' (transf_code x y z c) sp pc rs)
  | match_states_call:
      forall s f args s',
      list_forall2 match_stackframes s s' ->
      match_states (Callstate s f args)
                   (Callstate s' (transf_fundef f) args)
  | match_states_return:
      forall s s' v,
      list_forall2 match_stackframes s s' ->
      match_states (Returnstate s v)
                   (Returnstate s' v)
  | match_states_blocked:
      forall s s' v,
      list_forall2 match_stackframes s s' ->
      match_states (Blockedstate s v)
                   (Blockedstate s' v).

Lemma get_transf_code:
  forall x y z c (pc: positive) d, 
    c ! pc = Some d -> match d with Inop _ => False | _ => True end ->
    (transf_code x y z c) ! pc = Some d.
Proof.
  unfold transf_code; intros.
  rewrite PTree.gmap, H; simpl; destruct d; clarify.
Qed.

Lemma get_transf_code_nop:
  forall x y z c (pc: positive) d, 
    c ! pc = Some (Inop d) ->
    (transf_code x y z c) ! pc = Some (Inop d) 
    \/ (transf_code x y z c) ! pc = Some (Ifence d).
Proof.
  unfold transf_code; intros.
  rewrite PTree.gmap, H; simpl.
  destruct (in_inops); vauto.
  destruct (x # pc); vauto.
  destruct (y # pc); vauto.
  destruct (x # p); vauto.
Qed.

Lemma get_transf_code_back:
  forall x y z c (pc: positive) d, 
    (transf_code x y z c) ! pc = Some d ->
    c ! pc = Some d \/ exists next, c ! pc = Some (Inop next) /\ d = Ifence next.
Proof.
  unfold transf_code; intros.
  rewrite PTree.gmap in H.
  destruct (c ! pc) as [[]|] _eqn: C; simpl in *; vauto. 
  destruct (in_inops); vauto.
  destruct (x # pc); vauto.
  destruct (y # pc); vauto.
  destruct (x # p); vauto.
Qed.

Lemma sim_eval_addressing:
  forall sp addr args,
    eval_addressing tge sp addr args = eval_addressing ge sp addr args.
Proof.
  by intros; destruct addr; destruct args; clarify;
     try (destruct v0; clarify; destruct args; clarify); simpl in *; 
     rewrite <- symbols_preserved. 
Qed.

Lemma sim_eval_operation:
  forall sp op args,
    eval_operation tge sp op args = eval_operation ge sp op args.
Proof.
  intros; destruct op; destruct args; clarify;
  try (destruct v0; clarify; destruct args; clarify); simpl in *;
  apply sim_eval_addressing. 
Qed.

Lemma transf_step_correct:
  backward_sim s_lts t_lts false
    (fun t s => match_states s t) (fun _ _ => False).
Proof.
  split; vauto; split; simpl.
  Case "Stuck simulation".
    intros s t STUCK MS; eapply ev_stuck_or_error_stuck; intros s' l' STEP.
    (rtl_step_cases (destruct STEP) SCase); inv MS;
      try (exploit get_transf_code; [eassumption|done|intro]);
      try (exploit get_transf_code_nop; [eassumption|intros [?|?]]);
      try rewrite <- sim_eval_addressing in *;
      try rewrite <- sim_eval_operation in *;
      try (exploit find_function_translated; [eassumption|intro]);
      try (rewrite <- sig_preserved in *);
      try (first [SCase "exec_function_internal_nonempty"|by 
        try (rewrite <- sig_preserved in *); eapply STUCK; simpl; vauto]).
    SCase "exec_function_internal_nonempty".
      by eapply (STUCK _ (TEmem (MEalloc stk _ _))); vauto.
     SCase "exec_return". by inv H2; inv H1; eapply STUCK; vauto.
    SCase "exec_return_exit". by inv H2; eapply STUCK; vauto.
  Case "Normal simulation".
  Ltac kill := 
    by left; repeat split; try done; 
       eexists; split; [eexists; split; [eapply taustar_refl|]; simpl; vauto|]; simpl; vauto.
  (rtl_step_cases (destruct 1) SCase); inversion 1; intros; clarify;
    try (exploit get_transf_code_back; [eassumption|intro; des; clarify]);
    try rewrite sim_eval_addressing in *;
    try rewrite sim_eval_operation in *;
    try (exploit find_function_translated_back; [eassumption|intros (?&?&?)]; clarify);
    try rewrite sig_preserved in *;
    try kill.
  SCase "exec_Ifence". right; right; right; kill.
  SCase "exec_function_internal_empty". destruct f0; simpl in *; clarify; kill.
  SCase "exec_function_internal_nonempty". destruct f0; simpl in *; clarify; kill.
  SCase "exec_function_external_call". destruct f; simpl in *; clarify; kill.
  SCase "exec_return". inv H2; inv H4; kill.
  SCase "exec_return_exit". inv H2; kill.
Qed.

Lemma init_sim_succ:
  forall {p vals tinit} (INIT: rtl_init tge p vals = Some tinit),
    exists sinit, rtl_init ge p vals = Some sinit /\ match_states sinit tinit.
Proof.
  unfold rtl_init; intros.
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  destruct (Genv.find_funct_ptr tge p) as [[[]|]|]; try done;
    destruct (Genv.find_funct_ptr ge  p) as [[[]|]|]; try done; []; simpl in *.
  inv MF. destruct beq_nat; try done; [].
  eexists; split; try done; inv INIT; vauto.
Qed.

Lemma init_sim_fail:
  forall {p vals},
    rtl_init tge p vals = None ->
    rtl_init ge p vals = None.
Proof.
  intros p vals INIT. unfold rtl_init in *.
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  destruct (Genv.find_funct_ptr tge p) as [[[]|]|]; try done;
    destruct (Genv.find_funct_ptr ge  p) as [[[]|]|]; try done; []; simpl in *.
  inv MF. by destruct beq_nat.
Qed.

End PRESERVATION.

Definition fenceintro2_match_prg (p  : rtl_sem.(SEM_PRG))
                               (p' : rtl_sem.(SEM_PRG)) : Prop :=
  transf_program p = p'.

Theorem fenceintro2_sim Mm : Sim.sim Mm Mm rtl_sem rtl_sem fenceintro2_match_prg.
Proof.
  eapply (MCsim.sim (false_pure_load_cond Mm) rtl_sem rtl_sem genv_rel
    (fun ge tge s t => match_states t s) (fun _ _ _ _ => False)); intros; simpl in *.
  - by inv MP; destruct GENVR as [GR _]. 
  - eapply Genv.exists_matching_genv_and_mem_rev
      with (match_var := fun a b => a = b), INIT.
    by apply transform_program_match, MP.
  - by destruct (init_sim_succ _ _ GENVR INIT) as [si [INIT' MS]]; vauto.
  - eby eapply init_sim_fail.
  - eby eapply transf_step_correct.
Qed.
