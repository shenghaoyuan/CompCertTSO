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
Require Import Events.
Require Import Values.
Require Import Simulations.
Require Import Classical.
Require Import Libtactics.

(** * General construction of a small-step LTS from a trace-step LTS *)

Section CONSTRUCT_SMALL_STEP.

Variable S : Type.
Variable trace_step : S -> list thread_event -> S -> Prop.

Inductive small_step_state : Type :=
  | SSState : S -> list thread_event -> small_step_state
  | SSStuck : small_step_state.

Inductive small_step : small_step_state -> thread_event -> small_step_state -> Prop :=
  | Step1: forall stA ta te
     (NT: te<>TEtau)
     (TS: exists stB, exists te', exists tb, trace_step stA (ta++te::te'::tb) stB),
     small_step (SSState stA ta) te (SSState stA (ta++(te::nil)))
  | Step2: forall stA ta te stB
     (NT: te<>TEtau)
     (TS: trace_step stA (ta++te::nil) stB),
     small_step (SSState stA ta) te (SSState stB nil)
  (* new; will need fixup elsewhere *)
  | Step3: forall stA stB
     (TS: trace_step stA nil stB),
     small_step (SSState stA nil) TEtau (SSState stB nil).

(** Step 1
<<
stA --ta--> . ----te-----> . ----te'--> . --tb--> stB

         stA,ta --te--> stA,ta++[te] 
>>

Step2
<<
stA --ta--> . ----te----->  stB

         stA,ta --te--> stB,nil
>>

Step3
<<
stA     --nil--> stB

stA,nil --nil--> stB,nil
>>
*)

  (** Variant construction that is receptive by fiat, adding transitions
      to [SSStuck] as required. *)

Inductive small_step_Recep : small_step_state -> thread_event -> small_step_state -> Prop :=
  | StepRecep1: forall stA ta te
     (NT: te<>TEtau)
     (TS: exists stB, exists te', exists tb, trace_step stA (ta++te::te'::tb) stB),
     small_step_Recep (SSState stA ta) te (SSState stA (ta++(te::nil)))
  | StepRecep1r: forall stA ta te teR 
     (NT: te<>TEtau)
     (SAME: te_samekind teR te)
     (NEQ: ~(te=teR))
     (TS: exists stB, exists te', exists tb, trace_step stA (ta++te::te'::tb) stB)
     (TSR: ~ exists stB, exists tb, trace_step stA (ta++teR::tb) stB),
     small_step_Recep (SSState stA ta) teR SSStuck
  | StepRecep2: forall stA ta te stB
     (NT: te<>TEtau)
     (TS: trace_step stA (ta++te::nil) stB),
     small_step_Recep (SSState stA ta) te (SSState stB nil)
  | StepRecep2r: forall stA ta te teR stB
     (NT: te<>TEtau)
     (SAME: te_samekind teR te)
     (NEQ: ~(te=teR))
     (TS: trace_step stA (ta++te::nil) stB)
     (TSR: ~ exists stB, exists tb, trace_step stA (ta++teR::tb) stB),
     small_step_Recep (SSState stA ta) teR SSStuck
  | StepRecep3: forall stA stB
     (TS: trace_step stA nil stB),
     small_step_Recep (SSState stA nil) TEtau (SSState stB nil).

Ltac des :=
  clarify; repeat (match goal with H : (exists n, _) |- _ => destruct H end; clarify).

Hint Constructors small_step_Recep.

Lemma te_samekind_tran : 
  forall l l' l'', te_samekind l l' -> te_samekind l' l'' -> te_samekind l l''.
Proof.
  destruct l as [[]|[] | | | | | |];
  destruct l' as [[]|[] | | | | | |]; simpl; try done; 
  destruct l'' as [[]|[] | | | | | |]; simpl; try done; 
  intuition congruence.
Qed.

Definition te_wf (te : thread_event ) := 
  match te with
    | TEmem (MEread p c v) => Val.has_type v (Ast.type_of_chunk c)
    | TEmem (MErmw p c v rmwi) => Val.has_type v (Ast.type_of_chunk c)
    | TEext (Ereturn t ev) => Val.has_type (val_of_eval ev) t
    | _ => true
  end.

Lemma te_samekind_sym : 
  forall l l', te_samekind l' l -> te_wf l -> te_samekind l l'.
Proof.
  destruct l as [[]|[] | | | | | |];
  destruct l' as [[]|[] | | | | | |]; simpl; try done; 
  intuition congruence.
Qed.

Lemma te_samekind_nottau :
  forall l l', te_samekind l' l -> l <> TEtau -> l' <> TEtau.
Proof. by red; intros; clarify; destruct l as [[]|[]| | | | | |]. Qed.

Hint Immediate te_samekind_tran.
Hint Resolve te_samekind_nottau.

Lemma small_step_receptive :
  receptive (mklts thread_labels small_step_Recep).
Proof.
  red; intros; simpl in *.
  destruct (thread_event_eq_dec l l'); vauto.
  inv H;
  try destruct (classic (exists stB, exists tb, trace_step stA (ta ++ l' :: tb) stB)); eauto;
  try destruct (thread_event_eq_dec te l'); clarify; eauto;
  try (by destruct H as (? & [] & ?); eauto 8).
  destruct l' as [[]|[]| | | | | |]; clarify.
Qed.

Lemma app_cons1: forall T x (y: T) z, x ++ y :: z = (x ++ y :: nil) ++ z.
Proof. by intros; rewrite app_ass. Qed.

Lemma small_step_determinate :
  forall
    (SL: forall st t teA tA stA stB,
         trace_step st (t++teA::tA) stA ->
         trace_step st t stB ->
         False)
    (SK: forall st t teA tA stA teB tB stB,
         trace_step st (t++teA::tA) stA ->
         trace_step st (t++teB::tB) stB ->
         te_samekind teA teB)
    (WT: forall st t te tA stA,
         trace_step st (t++te::tA) stA ->
         te_wf te = true)
    (D: forall st t stA stB,
         trace_step st t stA ->
         trace_step st t stB ->
         stA = stB),
  determinate (mklts thread_labels small_step_Recep).
Proof.
  red; intros; simpl in *.
  inv H; inv H0; try (split; [try done|congruence]);
  repeat (match goal with H : exists x, _ |- _ => destruct H end); 
  try (match goal with 
    H1: trace_step ?s (?t ++ ?l :: _) _ , 
    H2: trace_step ?s (?t ++ ?l' :: _) _ |- _ => pose proof (SK _ _ _ _ _ _ _ _ H1 H2);
      pose proof (SK _ _ _ _ _ _ _ _ H2 H1) end);
  try done;
  try (eby eelim SL);
  try split; eauto; try done;
  try (intro; clarify);
  try (by elim TSR; eauto); 
  try (by rewrite app_cons1, <- app_nil_end in *; byContradiction; eauto);
  try (match goal with 
    H1: trace_step ?s ?t _ , 
    H2: trace_step ?s ?t _ |- _ => by rewrite (D _ _ _ _ H1 H2) end);
  try (eapply te_samekind_tran; try eassumption; []);
  try (eby eapply te_samekind_sym; eauto; eapply WT).
Qed.

End CONSTRUCT_SMALL_STEP.
