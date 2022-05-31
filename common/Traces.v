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

(** This file defines traces of a program, as well as measured and 
    weak-tau whole-system upward simulations, proving that they imply
    trace inclusion. *)

Require Import Coqlib.
Require Import Relations.Relation_Operators.
Require Import Classical.                   (**r axiom of excluded middle *)
Require Import Coq.Logic.ClassicalEpsilon.  (**r axiom of choice *)
Require Import Wellfounded.
Require Import Values.
Require Import Events.
Require Import Ast.
Require Import Maps.
Require Import Simulations.
Require Import Memcomp.
(*Require Import TSOmachine.*)
Require Import Libtactics.

Set Implicit Arguments.

(** First, we define possibly-infinite traces of events: *)

Section TraceDef.

Variable A : Type.

CoInductive trace: Type :=
  | Send
  | Sinftau
  | Soom
  | Scons (x: A) (t: trace).

Inductive tfin : trace -> Prop :=
  | tfin_end:    tfin Send
  | tfin_inftau: tfin Sinftau
  | tfin_oom:    tfin Soom
  | tfin_cons: forall x t, tfin t -> tfin (Scons x t).

CoInductive tinf : trace -> Prop :=
  | tinf_cons: forall x t, tinf t -> tinf (Scons x t).

Lemma finite_not_infinite: 
  forall t, tfin t -> ~ tinf t.
Proof.
  by red; induction 1; inversion 1.
Qed.

Lemma not_finite_infinite: 
  forall t, ~ tfin t -> tinf t.
Proof.
  cofix X; destruct t; try (by destruct 1; constructor).
  by intros Y; constructor; apply X; intro; destruct Y; constructor.
Qed.

Lemma finite_V_infinite:
  forall t, tfin t \/ tinf t.
Proof.
  intros; destruct (Classical_Prop.classic (tfin t)); [by left|].
  by right; apply not_finite_infinite.
Qed.

(** Concatenation of a finite sequence of events to a trace. *)

Fixpoint appt (l : list A) (t: trace) :=
  match l with
    | nil => t
    | x :: l => Scons x (appt l t)
  end.

Lemma appt_app:
  forall l1 l2 t, appt (l1 ++ l2) t = appt l1 (appt l2 t).
Proof. by intros; induction l1; simpl; f_equal. Qed.

(** Trace expansion to enable Coq simplification. *)

Definition trace_expanded (t: trace) :=
  match t with
  | Send      => Send
  | Sinftau   => Sinftau
  | Soom      => Soom
  | Scons x t => Scons x t
  end.

Lemma trace_expand :
  forall (t: trace), t = trace_expanded t.
Proof. by destruct t. Qed.

Implicit Types p : trace -> Prop.

CoInductive always p: trace -> Prop :=
  | always_end: p Send -> always p Send
  | always_oom: p Soom -> always p Soom
  | always_inftau: p Sinftau -> always p Sinftau
  | always_cons: 
    forall s tr,
      p (Scons s tr) ->
      always p tr ->
      always p (Scons s tr).

Inductive eventual p: trace -> Prop :=
  | eventual_sat: 
    forall tr,
      p tr ->
      eventual p tr
  | eventual_cons: 
    forall s tr,
      eventual p tr ->
      eventual p (Scons s tr).

Lemma always_mon:
  forall p p' (EQ: forall t, p t -> p' t) t (A: always p t), 
    always p' t.
Proof. intros until 1; cofix X; destruct 1; econstructor; eauto. Qed.

Lemma eventual_mon:
  forall p p' (EQ: forall t, p t -> p' t) t (A: eventual p t), 
    eventual p' t.
Proof. induction 2; econstructor (by eauto). Qed.

Lemma eventual_not_always:
  forall p t,
    eventual p t -> 
    ~ always (fun x => ~ p x) t.
Proof. by induction 1; red; inversion 1; clarify. Qed.

Lemma not_always_eventual:
  forall p t,
    ~ always p t ->
    eventual (fun x => ~ p x) t.
Proof.
  intros; apply NNPP; intro; destruct H.
  revert t H0; cofix X; intros.
  destruct (classic (p t)). 
  - destruct t; vauto.
    by constructor; try eassumption; eapply X; clear X; intro; destruct H0; vauto.
  - destruct H0; vauto.
Qed.

Lemma not_eventual_always:
  forall p t,
    ~ eventual p t ->
    always (fun x => ~ p x) t.
Proof.
  intros; eapply NNPP; intro M; destruct H; eapply not_always_eventual in M.
  by eapply eventual_mon; try eassumption; intros; apply NNPP.
Qed.

Lemma always_not_eventual:
  forall p t,
    always p t ->
    ~ eventual (fun x => ~ p x) t.
Proof.
  intros p t ALL EV; destruct (eventual_not_always EV); eapply always_mon; eauto.
Qed.

Lemma eventual_des:
  forall p t, eventual p t ->
    exists l, exists t', t = appt l t' /\ p t'.
Proof.
  induction 1; des; clarify; [exists nil|exists(s::l)]; vauto. 
Qed.

Lemma always_tail:
  forall p x t, always p (Scons x t) -> always p t.
Proof. by inversion 1; eauto. Qed.

Lemma always_fut:
  forall p l t, always p (appt l t) -> always p t.
Proof. by induction l; simpl; eauto using always_tail. Qed.

Definition satf (f: A -> A -> Prop) t :=
  match t with
    | Scons x (Scons y t) => f x y
    | _ => False
  end.

End TraceDef.

Implicit Arguments Send [A].
Implicit Arguments Sinftau [A].
Implicit Arguments Soom [A].

Section TracesDef.

Variable lts : lts event_labels.

(** Below, we define the following state properties:
   - [inftau s]:          the state [s] can perform an infinite traces of tau actions.
   - [infnontau s trace]: the state [s] can perform the infinite [trace] of events
     excluding [Efail] and [Eoutofmemory].
   - [fintrace s l s']:  the state [s] can perform the finite sequence [l] of events 
     and reach state [s'].
   - [traces s trace]: the state [s] can perform the trace [trace].
 *)

CoInductive inftau s: Prop :=
  | inftau_cons: forall s', 
      stepr lts s Etau s' ->
      inftau s' ->
      inftau s.

CoInductive infnontau s : trace event -> Prop :=
  | infnontau_cons: forall s' ev t, 
      taustep lts s (Evisible ev) s' ->
      (ev <> Efail) ->
      infnontau s' t ->
      infnontau s (Scons ev t).

Inductive fintrace s (l : list event) s' : Prop :=
  | fintrace_refl:
      (taustar lts s s') -> l = nil -> fintrace s l s'
  | fintrace_trans: forall ev s'' l'
      (TS: taustep lts s (Evisible ev) s'')
      (EV: ev <> Efail)
      (FIN: fintrace s'' l' s')
      (EQ: l = ev :: l'),
      fintrace s l s'.

Inductive traces s t : Prop :=
  | traces_end: forall l s'
      (PREF: fintrace s l s')
      (STUCK: forall l' s'', ~ stepr lts s' l' s'')
      (TEQ: appt l Send = t),
      traces s t
  | traces_fail: forall l s' s'' t'
      (PREF: fintrace s l s')
      (FAIL: stepr lts s' (Evisible Efail) s'')
      (TEQ: appt l t' = t),
      traces s t
  | traces_inftau: forall l s'
      (PREF: fintrace s l s')
      (INF: inftau s')
      (TEQ: appt l Sinftau = t),
      traces s t
  | traces_oom: forall l s'
      (PREF: fintrace s l s')
      (TEQ: appt l Soom = t),
      traces s t
  | traces_infnontau: forall
      (INF: infnontau s t),
      traces s t.

(** Infinite trace of tau actions perhaps terminated by an error. *)

CoInductive inftau_or_err s : Prop :=
  | inftau_or_err_tau: forall s' 
      (STEP: taustep lts s Etau s')
      (INF: inftau_or_err s'),
      inftau_or_err s
  | inftau_or_err_fail: forall s'
      (FAIL: taustep lts s (Evisible Efail) s'),
      inftau_or_err s.

(** Same, except it's in Type *)

CoInductive tinftau_or_err s : Type :=
  | tinftau_or_err_tau: forall s' 
      (STEP: taustep lts s Etau s')
      (INF: tinftau_or_err s'),
      tinftau_or_err s
  | tinftau_or_err_fail: forall s'
      (FAIL: taustep lts s (Evisible Efail) s'),
      tinftau_or_err s.

(** Witness version of the above. *)

CoInductive inftau_or_err_witness s: trace (St lts) -> Prop :=
  | inftau_or_err_witness_tau: forall s' t
      (STEP: taustep lts s Etau s')
      (INF: inftau_or_err_witness s' t),
      inftau_or_err_witness s (Scons s' t)
  | inftau_or_err_witness_fail: forall s'
      (FAIL: taustep lts s (Evisible Efail) s'),
      inftau_or_err_witness s (Scons s' Send).

Hint Constructors inftau_or_err_witness.

Lemma inftau_or_err_upgrade: 
  forall s (H: inftau_or_err s), tinftau_or_err s.
Proof.
  cofix X; intros.
  destruct (excluded_middle_informative (exists s', taustep lts s (Evisible Efail) s')) as [M|M].
    by destruct (constructive_indefinite_description _ M) as (? & ?); vauto.
  destruct (excluded_middle_informative (exists s', taustep lts s Etau s' /\ inftau_or_err s')) as [N|N].
    by destruct (constructive_indefinite_description _ N) as (? & ? & ?); econstructor (by eauto). 
  destruct N; destruct H; eauto; destruct M; eauto.
Qed.

Lemma inftau_or_err_exists_witness: 
  forall s (H: inftau_or_err s), exists t, inftau_or_err_witness s t.
Proof.
  intros; eapply inftau_or_err_upgrade in H. 
  exists ((cofix Y s (H: tinftau_or_err s) :=
    match H with
      | tinftau_or_err_tau s' STEP INF => Scons s' (Y _ INF)
      | tinftau_or_err_fail s' TAUS => Scons s' Send
    end) _ H).
  revert s H; cofix X; destruct H; simpl; rewrite (trace_expand _); simpl; eauto.
Qed.

(** Same as [inftau], except it's in Type *)

CoInductive tinftau s : Type :=
  | tinftau_cons: forall s' 
      (STEP: stepr lts s Etau s')
      (INF: tinftau s'),
      tinftau s.

(** Witness version of the above. *)

CoInductive inftau_witness: trace (St lts) -> Prop :=
  | inftau_witness_cons: forall s s' t
      (STEP: stepr lts s Etau s')
      (INF: inftau_witness (Scons s' t)),
      inftau_witness (Scons s (Scons s' t)).

Hint Resolve inftau_witness_cons.

Lemma inftau_upgrade: 
  forall s (H: inftau s), tinftau s.
Proof.
  cofix X; intros.
  destruct (excluded_middle_informative (exists s', stepr lts s Etau s' /\ inftau s')) as [N|[]].
    by destruct (constructive_indefinite_description _ N) as (? & ? & ?); econstructor; eauto.
  destruct H; eauto.
Qed.

Lemma inftau_exists_witness: 
  forall s (H: inftau s), exists t, inftau_witness (Scons s t).
Proof.
  intros; eapply inftau_upgrade in H.
  exists ((cofix Y s (H: tinftau s) :=
    match H with
      | tinftau_cons s' STEP INF => Scons s' (Y s' INF)
    end) _ H).
  revert s H; cofix X; destruct H; simpl.
  rewrite (trace_expand (_ s (tinftau_cons s STEP H))); simpl; eauto.
Qed.

(** Infinite trace of non-tau actions, perhaps terminated by an error. *)

CoInductive infnontau_or_err s : trace event -> Prop :=
  | infnontau_or_err_cons: forall s' ev t, 
      taustep lts s (Evisible ev) s' ->
      (ev <> Efail) ->
      infnontau_or_err s' t ->
      infnontau_or_err s (Scons ev t)
  | infnontau_or_err_fail: forall s' t
      (FAIL: taustep lts s (Evisible Efail) s'),
      infnontau_or_err s t.

(** Same, except it's in Type *)

CoInductive tinfnontau_or_err s : trace event -> Type :=
  | tinfnontau_or_err_cons: forall s' ev t, 
      taustep lts s (Evisible ev) s' ->
      (ev <> Efail) ->
      tinfnontau_or_err s' t ->
      tinfnontau_or_err s (Scons ev t)
  | tinfnontau_or_err_fail: forall s' t
      (FAIL: taustep lts s (Evisible Efail) s'),
      tinfnontau_or_err s t.

(** Witness version of the above. *)

CoInductive infnontau_or_err_witness s : trace event -> trace (St lts) -> Prop :=
  | infnontau_or_err_witness_cons: forall s' ev t t', 
      taustep lts s (Evisible ev) s' ->
      (ev <> Efail) ->
      infnontau_or_err_witness s' t t' ->
      infnontau_or_err_witness s (Scons ev t) (Scons s' t')
  | infnontau_or_err_witness_fail: forall s' t
      (FAIL: taustep lts s (Evisible Efail) s'),
      infnontau_or_err_witness s t (Scons s' Send).

CoFixpoint infnontau_or_err_w s t (H: tinfnontau_or_err s t) : trace (St lts) :=
  match H with
  | tinfnontau_or_err_cons s' _ _ _ _ INF => Scons s' (infnontau_or_err_w INF)
  | tinfnontau_or_err_fail s' _ _ => Scons s' Send
  end.

(** Correspondence between the two. *)

Hint Constructors infnontau_or_err_witness.

Lemma infnontau_or_err_upgrade: 
  forall s t (H: infnontau_or_err s t), tinfnontau_or_err s t.
Proof.
  cofix X; intros.
  destruct (excluded_middle_informative (exists s', taustep lts s (Evisible Efail) s')) as [M|M].
    by destruct (constructive_indefinite_description _ M) as (? & ?); vauto.
  destruct (excluded_middle_informative (exists ev, exists s', exists t', taustep lts s (Evisible ev) s'
                /\ ev <> Efail /\ infnontau_or_err s' t' /\ t = Scons ev t')) as [N|N].
    do 3 (eapply constructive_indefinite_description in N; destruct N as (? & N)).
    by decompose [Logic.and] N; clear N; clarify; econstructor (by eauto).
  by destruct N; inv H; [do 3 econstructor; eauto| destruct M; eauto].
Qed.

Lemma infnontau_or_err_exists_witness: 
  forall s t (H: infnontau_or_err s t), exists t', infnontau_or_err_witness s t t'.
Proof.
  intros; apply infnontau_or_err_upgrade in H; exists (infnontau_or_err_w H); revert s t H.
  cofix X; intros; case H; intros; simpl; rewrite trace_expand; simpl; econstructor; eauto.
Qed.

(** The following definition is semantically identical to [inftau], but is quite
    convenient for proofs. *)
CoInductive inftau' s: Prop :=
  | inftau'_cons: forall s', 
      taustep lts s Etau s' ->
      inftau' s' ->
      inftau' s.

Lemma inftau_inftau':
  forall s, inftau s -> inftau' s.
Proof.
  cofix X; destruct 1; econstructor; eauto; econstructor; vauto.
Qed.

Lemma inftau'_inftau:
  forall s, inftau' s -> inftau s.
Proof.
  (* working around Coq's cofix restrictions *)
  assert (X: forall s s', taustar lts s s' -> inftau' s' -> inftau s).
    cofix X; intros s s' [|m n l STEP TAU] [x M INF]. 
    - by destruct (tausteptau_decomp M) as (y & STEP & TAU); econstructor; eauto.
    eby econstructor; eauto; eapply X, INF; eapply taustar_trans, tausteptau_taustar.
  by intros; eapply X; vauto.
Qed.

Lemma fintrace_tauapp: 
  forall s s' s'' l,
    taustar lts s s' -> 
    fintrace s' l s'' ->
    fintrace s l s''.
Proof.
  destruct 2; clarify; 
  eauto using fintrace_trans, fintrace_refl, taustar_trans, taustar_taustep. 
Qed.

Lemma fintrace_app: 
  forall s s' s'' l l',
    fintrace s l s' -> 
    fintrace s' l' s'' ->
    fintrace s (l ++ l') s''.
Proof.
  induction 1; intros; clarify; simpl; eauto using fintrace_trans, fintrace_tauapp. 
Qed.

Lemma fintrace_apptau: 
  forall s s' s'' l,
    fintrace s l s' -> 
    taustar lts s' s'' ->
    fintrace s l s''.
Proof.
  induction 1; intros; clarify; eauto using fintrace_trans, fintrace_refl, taustar_trans.
Qed.

Lemma traces_app: 
  forall s l s' t,
    fintrace s l s' ->
    traces s' t ->
    traces s (appt l t).
Proof.
  destruct 2; clarify; rewrite <- ?appt_app.
  eauto using traces_end, fintrace_app.
  eauto using traces_fail, fintrace_app.
  eauto using traces_inftau, fintrace_app.
  eauto using traces_oom, fintrace_app.
  eapply traces_infnontau.
  revert s H; induction l; intros; simpl in *;
    by (inv H; clarify; destruct INF; 
        eauto using infnontau_cons, taustar_taustep).
Qed.

Lemma traces_inftau_or_err:
  forall s (INF: inftau_or_err s), traces s Sinftau.
Proof.
  intros. eapply inftau_or_err_exists_witness in INF; destruct INF as (t & INF).
  destruct (finite_V_infinite t) as [H|H].

  Case "finite".
  revert s INF; induction H; intros; inv INF;
    try (by destruct FAIL as (? & TAU & ERR);
            eapply traces_fail with (l := nil); simpl; try edone; vauto). 
  eapply traces_app with (l := nil); eauto.
  by econstructor; try eapply tausteptau_taustar.

  Case "infinite".
  eapply traces_inftau with (s' := s); vauto. 
  eapply inftau'_inftau.
  revert s t INF H.
  cofix X.
  inversion 2; clarify.
  inv INF; clarify.
    econstructor; eauto.
  inv H0.
Qed.

Lemma traces_infnontau_or_err:
  forall s t (INF: infnontau_or_err s t), traces s t.
Proof.
  intros; eapply infnontau_or_err_exists_witness in INF; destruct INF as (t' & INF).
  destruct (finite_V_infinite t') as [H|H].

  Case "finite".
  revert s t INF; induction H; intros; inv INF;
    try (by destruct FAIL as (? & TAU & ERR);
            eapply traces_fail with (l := nil); simpl; try edone; vauto). 
  change (Scons ev t1) with (appt (ev::nil) t1).
  by eapply traces_app; eauto; eapply fintrace_trans; try edone; vauto.

  Case "infinite".
  eapply traces_infnontau.
  revert s t t' INF H.
  cofix X.
  inversion 2; clarify.
  inv INF; clarify.
    econstructor; eauto.
  inv H0.
Qed.

Lemma inftau_witness_app:
  forall l s t,
    inftau_witness (Scons s (appt l t)) ->
    exists s', exists t', t = Scons s' t' /\ 
      taustep lts s Etau s' /\ inftau_witness t.
Proof.
  induction l; simpl; intros; inv H.
  eexists; eexists; split; [|split;[eexists|]]; vauto.
  exploit IHl; try eassumption; intro; des; clarify. 
  eexists; eexists; split; split; try done.
  eapply taustar_taustep; try edone; vauto.
Qed.

End TracesDef.

Tactic Notation "traces_cases" tactic(first) tactic(c) :=
    first; [
      c "traces_end" |
      c "traces_fail" |
      c "traces_inftau" |
      c "traces_oom" |
      c "traces_infnontau"].

(* -------------------------------------------------------------------------- *)
(** * Basic upward simulations *)
(* -------------------------------------------------------------------------- *)

(** Valid arguments for the main function *)
Definition valid_arg (v : val) :=
  match v with
    | Vint _ => True
    | Vfloat _ => True
    | _ => False
  end.

Definition valid_args (vs : list val) :=
  forall v, In v vs -> valid_arg v.

Definition prog_traces (Mm: MM) (Sem: SEM) (p: SEM_PRG Sem) args t :=
  exists ge, exists s, Comp.init Mm Sem p args ge s /\
    traces (mklts event_labels (Comp.step Mm Sem ge)) s t.

Module Bsim. Section Bsim.

  Variables (SrcMM TgtMM: MM).
  Variables (Src Tgt: SEM).
  Variable  (match_prg : Src.(SEM_PRG) -> Tgt.(SEM_PRG) -> Prop).

  (** Record [sim] is a witness for an upward TSO-machine simulation. *)
  Record sim := make {
    rel : Src.(SEM_GE) -> Tgt.(SEM_GE) -> Comp.state SrcMM Src -> Comp.state TgtMM Tgt -> Prop ;
    order : Src.(SEM_GE) -> Tgt.(SEM_GE) -> Comp.state TgtMM Tgt -> Comp.state TgtMM Tgt -> Prop ;

    empty :
      forall {sge tge s t}
        (REL: rel sge tge s t)
        (sCONS: Comp.consistent _ _ s)
        (tCONS: Comp.consistent _ _ t)
        (EMPTY: snd t = @PTree.empty _),
        snd s = @PTree.empty _ ;

    init:
      forall {sprg tprg tge args tinit}
        (MP: match_prg sprg tprg)
        (VARGS: valid_args args)
        (INIT: Comp.init TgtMM Tgt tprg args tge tinit),
        exists sge, exists sinit,
          Comp.init SrcMM Src sprg args sge sinit /\
          rel sge tge sinit tinit ;

    step :
      forall {sge tge s t t' e}
        (STEP: Comp.step TgtMM Tgt tge t e t')
        (REL: rel sge tge s t)
        (sCONS: Comp.consistent _ _ s)
        (tCONS: Comp.consistent _ _ t)
        (NOOM: e <> Eoutofmemory),
        (* can reach error *)
        (exists s',
          taustar (mklts event_labels (Comp.step SrcMM Src sge)) s s' /\ 
          can_do_error _ s') \/
        (* or can do the same step *)
        (exists s',
          taustep (mklts event_labels (Comp.step SrcMM Src sge)) s e s' /\ 
          rel sge tge s' t') \/
        (* or can stutter *)
        (e = Etau /\ order sge tge t t' /\ rel sge tge s t') 
  }.

  Variable (SimST: sim).

  Let src_lts sge := (mklts event_labels (Comp.step SrcMM Src sge)).
  Let tgt_lts tge := (mklts event_labels (Comp.step TgtMM Tgt tge)).

  Hint Resolve Comp.step_preserves_consistency
    Comp.taustar_preserves_consistency
    Comp.taustep_preserves_consistency.

  Lemma fintrace_preserves_consistency :
    forall (Mm: MM) (Sem : SEM) (ge : SEM_GE Sem)
      l (s s' : St (mklts event_labels (Comp.step Mm Sem ge))),
      fintrace (mklts event_labels (Comp.step Mm Sem ge)) s l s' ->
      Comp.consistent Mm Sem s -> Comp.consistent Mm Sem s'.
  Proof. induction 1; eauto. Qed.

  Hint Resolve fintrace_preserves_consistency.

  Lemma tau_simulation:
    forall {sge tge s t t'}
      (ST : taustar (tgt_lts tge) t t')
      (REL : rel SimST sge tge s t)
      (sCONS: Comp.consistent _ _ s)
      (tCONS: Comp.consistent _ _ t),
    (exists s', taustar (src_lts sge) s s' /\ can_do_error _ s') \/
    (exists s', taustar (src_lts sge) s s' /\ rel SimST sge tge s' t').
  Proof.
    intros until 1; revert s. 
    induction ST as [|t t'' t' STEP]; intros; [by right; eexists; vauto|].
    destruct (step _ STEP REL sCONS tCONS)
      as [ERR|[(s'' & TAU & REL'')|(_ & ORD & REL'')]]; try done.
    - by left.
    Case "step".
    destruct (IHST _ REL''); des; clarify; simpl in *; eauto.
    - left; eexists; split; try edone; eapply taustar_trans; try edone.
      eby eapply tausteptau_taustar.
    - right; do 2 eexists; [|edone].
      eby eapply taustar_trans; [eapply tausteptau_taustar|].
    Case "stutter".
    destruct (IHST _ REL''); des; clarify; simpl in *; eauto.
  Qed.

  Lemma taustep_simulation:
    forall {sge tge s t e t'}
      (ST : taustep (tgt_lts tge) t e t')
      (REL : rel SimST sge tge s t)
      (sCONS: Comp.consistent _ _ s)
      (tCONS: Comp.consistent _ _ t)
      (NOOM: e <> Eoutofmemory),
    (exists s', taustar (src_lts sge) s s' /\ can_do_error _ s') \/
    (exists s', taustep (src_lts sge) s e s' /\ rel SimST sge tge s' t') \/
    (e = Etau /\ rel SimST sge tge s t').
  Proof.
    intros; destruct ST as (t'' & TAU & STEP).
    destruct (tau_simulation TAU REL); des; clarify; eauto.
    exploit step; try eapply STEP; eauto; intro; des; clarify; eauto.
    - eby left; eexists; split; [eapply taustar_trans|].
    - eby right; left; do 2 eexists; [eapply taustar_taustep|].
    inv H; eauto.
    eby right; left; do 2 eexists; [eapply steptau_taustar_taustep|].
  Qed.

  Lemma fintrace_simulation:
    forall {sge tge s t l t'}
      (FT : fintrace (tgt_lts tge) t l t')
      (REL : rel SimST sge tge s t)
      (sCONS: Comp.consistent _ _ s)
      (tCONS: Comp.consistent _ _ t),
    (exists s', exists s'', exists l1, exists l2, l = l1 ++ l2 /\ fintrace (src_lts sge) s l1 s' 
      /\ taustar (src_lts sge) s' s'' /\ can_do_error _ s'') \/
    (exists s', 
      fintrace (src_lts sge) s l s' /\ rel SimST sge tge s' t') \/
    (l = nil /\ order SimST sge tge t t' /\ rel SimST sge tge s t').
  Proof.
    intros; revert s REL sCONS tCONS.
    induction FT; clarify; intros.
    - eapply tau_simulation in H; try eassumption; try congruence.
      destruct H; des; clarify.
      + by left; do 2 eexists; do 2 exists nil; do 2 eexists; vauto. 
      by right; left; do 2 eexists; try eassumption; vauto. 
    generalize TS; intro TS'; eapply taustep_simulation in TS; try eassumption; try congruence.
    destruct TS as [(? & TAU'' & ERR)|[(? & TAU'' & REL'')|(eNONE & _)]]; clarify.
    - left; eexists; eexists; exists nil; eexists; split; [done|]; split; [|split]; try edone.
      by vauto.
    - simpl in *; specialize (IHFT _ REL'').
      destruct IHFT as [(xx & ? & l1 & l2 & EQ & FT2 & TS2 & ERR)
                       |[(? & FT2 & REL2)|(eNONE & ORD & REL')]]; simpl in *; try done; eauto.
      + by left; eexists; eexists; exists (ev :: l1); eexists l2; simpl;
           split; [congruence|]; split; [|split]; try edone; vauto.
      + by right; left; do 2 eexists; try eassumption; vauto. 
      + subst; right; left; do 2 eexists; try eassumption; vauto.
        eauto using fintrace_trans, fintrace_refl, taustar_refl.
  Qed.

  Lemma steperror_sim:
    forall {sge tge s t t'}
      (STEP: Comp.step TgtMM Tgt tge t (Evisible Efail) t')
      (REL: rel SimST sge tge s t)
      (sCONS: Comp.consistent _ _ s)
      (tCONS: Comp.consistent _ _ t),
    exists s', taustep (src_lts sge) s (Evisible Efail) s'.
  Proof.
    intros; exploit step; try eassumption; try done.
    intros [(s' & TAU & ? & [[]| |] & ? & ERR)|?]; des; vauto.
  Qed.

  Hint Resolve Comp.no_threads_stuck.

  (** Except for the infinite-tau case, basic simulation implies trace 
      inclusion. *)
  Theorem traces_incl:
    forall {sprg tprg args t}
      (MP: match_prg sprg tprg)
      (VARG: valid_args args)
      (T: prog_traces TgtMM Tgt tprg args t)
      (INF: forall sge tge s t
        (INF : inftau (tgt_lts tge) t)
        (tCONS : Comp.consistent TgtMM Tgt t)
        (REL : rel SimST sge tge s t)
        (sCONS : Comp.consistent SrcMM Src s),
         inftau_or_err (src_lts sge) s),
      prog_traces SrcMM Src sprg args t. 
  Proof.
    intros; destruct T as (tge & tinit & INIT & T).
    destruct (init SimST MP VARG INIT) as (sge & sinit & INIT' & REL).
    assert (tCONS := Comp.init_consistent _ _ INIT).
    assert (sCONS := Comp.init_consistent _ _ INIT').

    eexists; eexists; split; try eassumption.
    clear - INF T REL tCONS sCONS; revert sinit t tinit T REL tCONS sCONS.
    intros; (traces_cases (case T) Case); clarify.

  Case "traces_end".
    intros l t'; intros; clarify.
(*    eapply fintrace_apptau in PREF; [clear TAU | by apply TAU]. *)
    assert (t''CONS: Comp.consistent _ _ t') by eauto.
    eapply fintrace_simulation in PREF; try eassumption.
    destruct PREF as [(s' & s'' & l1 & l2 & EQ & FIN & TAU' & s''' & ev & ? & ERR)|
                     [(s' & FIN & REL')|(EQ & ORD & REL')]]; simpl in *; clarify.
    - destruct ev as [[]| |]; clarify; rewrite appt_app.
      eapply traces_fail with (t' := appt l2 Send); try apply ERR; try edone.
      by eapply fintrace_apptau; eauto. 
    - eapply traces_end with (s' := s'); try edone; vauto.
      eapply Comp.stuck_imp_no_threads in STUCK; try done. 
      assert (s'CONS: Comp.consistent _ _ s') by eauto. 
      by pose proof (empty _ REL' s'CONS t''CONS STUCK); simpl; eauto.
    - eapply traces_end with (s' := sinit); try edone; vauto.
      eapply Comp.stuck_imp_no_threads in STUCK; try done.
      by pose proof (empty _ REL' sCONS t''CONS STUCK); simpl; eauto.

  Case "traces_fail".
    intros l t' t'' tt; intros; clarify.
    assert (t''CONS: Comp.consistent _ _ t') by eauto.
    eapply fintrace_simulation in PREF; try eassumption.
    destruct PREF as [(s' & s'' & l1 & l2 & EQ & FIN & TAU' & s''' & ev & ? & ERR)|
                     [(s' & FIN & REL')|(EQ & ORD & REL')]]; simpl in *; clarify.
    - destruct ev as [[]| |]; clarify; rewrite appt_app.
      eapply traces_fail with (t' := appt l2 tt); try apply ERR; try edone.
      by eapply fintrace_apptau; eauto. 
    - destruct (steperror_sim FAIL REL') as (? & ? & TAU & ERR); eauto.
      eapply traces_fail with (t' := tt); try apply ERR; try edone.
      by eauto using fintrace_apptau.
    - destruct (steperror_sim FAIL REL') as (? & ? & TAU & ERR); eauto.
      eapply traces_fail with (t' := tt); try apply ERR; try edone.
      by eauto using fintrace_refl. 

  Case "traces_inftau".
    intros l t'; intros; clarify.
    assert (t'CONS: Comp.consistent _ _ t') by eauto.
    eapply fintrace_simulation in PREF; try eassumption.
    destruct PREF as [(s' & s'' & l1 & l2 & EQ & FIN & TAU' & s''' & ev & ? & ERR)|
                     [(s' & FIN & REL')|(EQ & ORD & REL')]]; simpl in *; clarify.
    - destruct ev as [[]| |]; clarify; rewrite appt_app.
      eapply traces_fail with (t' := appt l2 Sinftau); try apply ERR; try edone.
      by eapply fintrace_apptau; eauto. 
    - by eapply traces_app; try eassumption; eapply traces_inftau_or_err, INF; eauto.
    - by eapply traces_inftau_or_err, INF; eauto.

  Case "traces_oom".
    intros l t'; intros; clarify.
    eapply fintrace_simulation in PREF; try eassumption.
    destruct PREF as [(s' & s'' & l1 & l2 & EQ & FIN & TAU' & s''' & ev & ? & ERR)|
                     [(s' & FIN & REL')|(EQ & ORD & REL')]]; simpl in *; clarify. 
    - destruct ev as [[]| |]; clarify; rewrite appt_app.
      eapply traces_fail with (t' := appt l2 _); try apply ERR; try edone.
      by eapply fintrace_apptau; eauto. 
    - by eauto using traces_oom, taustar_refl, fintrace_refl.
    - by eauto using traces_oom, taustar_refl, fintrace_refl.

  Case "traces_infnontau".
    clear INF; intros; eapply traces_infnontau_or_err. 
    revert REL INF tCONS sCONS; clear - src_lts tgt_lts; revert sinit tinit t; cofix X; intros.
    destruct INF.
    generalize H; intro; eapply taustep_simulation in H; try eassumption; try congruence.
    des; clarify.
    clear X; unfold can_do_error in *; des; clarify; destruct l as [[]| |]; vauto.
    econstructor 1; try edone; eapply X; clear X; eauto.
  Qed.

End Bsim. End Bsim.

(* -------------------------------------------------------------------------- *)
(** * Upward measured simulations *)
(* -------------------------------------------------------------------------- *)

Module Sim. Section Sim.

  Variables (SrcMM TgtMM: MM).
  Variables (Src Tgt: SEM).
  Variable  (match_prg : Src.(SEM_PRG) -> Tgt.(SEM_PRG) -> Prop).

  (** Definition of a measured simulation: it is a basic simulation 
      whose [order] is well-founded. *)
  Record sim := make {
    bsim : Bsim.sim SrcMM TgtMM Src Tgt match_prg ;
    order_wf : forall sge tge, well_founded (fun t t' => Bsim.order bsim sge tge t' t) 
  }.

  Variable (SimST: sim).

  Let src_lts sge := (mklts event_labels (Comp.step SrcMM Src sge)).
  Let tgt_lts tge := (mklts event_labels (Comp.step TgtMM Tgt tge)).

  Lemma inftau_sim_steps:
    forall {sge tge s t}
      (INF: inftau (tgt_lts tge) t)
      (REL: Bsim.rel (bsim SimST) sge tge s t)
      (sCONS: Comp.consistent SrcMM Src s)
      (tCONS: Comp.consistent TgtMM Tgt t),
    (exists s', taustep (src_lts sge) s (Evisible Efail) s')
    \/ (exists s', exists t',
         taustep (tgt_lts tge) t Etau t'
         /\ taustep (src_lts sge) s Etau s'
         /\ Bsim.rel (bsim SimST) sge tge s' t'
         /\ inftau (tgt_lts tge) t').
  Proof.
    intros; revert INF REL; induction (Sim.order_wf SimST sge tge t) as [t _ IH]; simpl.
    intros; destruct INF as [t' STEP INF]; simpl in *.
    edestruct (Bsim.step (bsim SimST) STEP REL)
      as [(s3 & TAU & s''' & [[]| |] & ? & ERR)|[(s3 & TAUS & REL')|(EQ & ORD & REL')]]; 
        simpl in *; clarify. 
    - by left; vauto.
    - by right; do 3 eexists; vauto; eexists; vauto.
    exploit IH; try eassumption; [eby eapply Comp.step_preserves_consistency|].
    intros [?|(? & ? & TAUt & TAUs & REL'' & INF')]; [by left|right].
    do 3 eexists; vauto.
    by eapply taustar_taustep; try eassumption; vauto.
  Qed.

  Lemma inftau1:
    forall sge tge s t
      (INF : inftau (tgt_lts tge) t)
      (REL : Bsim.rel (bsim SimST) sge tge s t)
      (sCONS: Comp.consistent SrcMM Src s)
      (tCONS: Comp.consistent TgtMM Tgt t),
      inftau_or_err (src_lts sge) s.
  Proof.
    cofix X; intros.
    eapply inftau_sim_steps in INF; try eassumption.
    destruct INF as [(? & ERR)|(? & ? & TAUt & TAUs & REL' & INF)]. 
    - eby eapply inftau_or_err_fail.
    by eapply inftau_or_err_tau; try eapply X; clear X;
       eauto using Comp.taustep_preserves_consistency. 
  Qed. 

  (** Main theorem: Our whole-system measured upward simulation implies
      trace inclusion. *)
  Theorem traces_incl:
    forall {sprg tprg args t}
      (MP: match_prg sprg tprg)
      (VARG: valid_args args)
      (T: prog_traces TgtMM Tgt tprg args t),
      prog_traces SrcMM Src sprg args t. 
  Proof.
    intros; eapply Bsim.traces_incl; try edone.
    eby intros; eapply inftau1.
  Qed.

End Sim. End Sim.

(* -------------------------------------------------------------------------- *)
(** * Weak-tau simulations *)
(* -------------------------------------------------------------------------- *)

Module WTsim. Section WTsim.

  Variables (SrcMM TgtMM: MM).
  Variables (Src Tgt: SEM).
  Variable  (match_prg : Src.(SEM_PRG) -> Tgt.(SEM_PRG) -> Prop).

  (** Definition of a weak-tau simulation: it consists of a basic simulation,
      and a weaker relation [wrel] that is preserved by tau-steps satisfying 
      the [order] relation. *)
  Record sim := make {
    bsim : Bsim.sim SrcMM TgtMM Src Tgt match_prg ;
    wrel : Src.(SEM_GE) -> Tgt.(SEM_GE) -> Comp.state SrcMM Src -> Comp.state TgtMM Tgt -> Prop ;
    weaken : 
      forall {sge tge s t} (R: Bsim.rel bsim sge tge s t), wrel sge tge s t ;
    wstep :
      forall {sge tge s t t'}
        (STEP: Comp.step TgtMM Tgt tge t Etau t')
        (REL: wrel sge tge s t)
        (ORD: Bsim.order bsim sge tge t t')
        (sCONS: Comp.consistent _ _ s)
        (tCONS: Comp.consistent _ _ t),
        (* can reach error *)
        (exists s',
          taustar (mklts event_labels (Comp.step SrcMM Src sge)) s s' /\ 
          can_do_error _ s') \/
        (* or can do the same step *)
        (exists s',
          taustep (mklts event_labels (Comp.step SrcMM Src sge)) s Etau s' /\ 
          wrel sge tge s' t')
  }.

  Variable (SimST: sim).

  Let src_lts sge := (mklts event_labels (Comp.step SrcMM Src sge)).
  Let tgt_lts tge := (mklts event_labels (Comp.step TgtMM Tgt tge)).

  Ltac des_err :=
    repeat match goal with
             | H: can_do_error _ _ |- _ =>
               let X := fresh in
                 destruct H as (? & [[]| |] & X & H); clarify; clear X
           end. 

  Hint Resolve Comp.step_preserves_consistency
    Comp.taustar_preserves_consistency
    Comp.taustep_preserves_consistency.

  CoInductive not_EA_order tge order t : Prop :=
  | not_EA_order_cons: forall t' t''
      (TS: taustar (tgt_lts tge) t t')
      (STEP: stepr (tgt_lts tge) t' Etau t'')
      (ORD: ~ order t' t'')
      (U: not_EA_order tge order t''),
      not_EA_order tge order t.

  Lemma not_EA_intro:
    forall tge order t tr,
      ~ eventual (always (satf order)) tr ->
      inftau_witness (tgt_lts tge) (Scons t tr) ->
      not_EA_order (tge:= tge) order t. 
  Proof.
    intros; eapply not_eventual_always, always_mon in H; [|by apply not_always_eventual].
    revert t tr H H0; clear; cofix X.
    destruct 1; (try by inversion 1). 
    eapply eventual_des in H; des.
    rewrite H; intro M.
    eapply inftau_witness_app in M; des; clarify.
    unfold taustep in *; des. 
    inversion H4; subst.
    
    econstructor; try (apply H1); try eassumption.
    eapply taustar_trans; try edone; vauto.
    eapply X; clear X; try eapply INF.
    destruct l; simpl in *; clarify; eauto using always_fut, always_tail.
  Qed.

  Lemma inftau1: 
    forall sge tge s t
      (INF : inftau (tgt_lts tge) t)
      (REL : Bsim.rel (bsim SimST) sge tge s t)
      (sCONS: Comp.consistent _ _ s)
      (tCONS: Comp.consistent _ _ t),
      inftau_or_err (src_lts sge) s.
  Proof.
    intros.
    pose (ults := mklts event_labels 
             (fun t e t' => e=Etau /\ Comp.step TgtMM Tgt tge t Etau t'
                            /\ Bsim.order (bsim SimST) sge tge t t')).
    destruct (inftau_exists_witness INF) as (tr & INF').
    destruct (classic (eventual (always (satf (Bsim.order (bsim SimST) sge tge))) tr)).

  Case "eventually_always_ordered".
    eapply eventual_des in H; des; clarify.
    eapply (inftau_witness_app (lts:=tgt_lts tge)) in INF'.

    destruct INF' as (t'' & t'0 & ? & TAU & INF'); clarify. 
    eapply (tausteptau_taustar (ts:=tgt_lts tge)) in TAU.
    assert (tCONS': Comp.consistent TgtMM Tgt t'') by eauto.
    eapply Bsim.tau_simulation in TAU; try eassumption.
    clear REL INF. destruct TAU as [ERR|(s'' & TAU & REL)]; des; clarify; des_err; vauto.

    cut (inftau_or_err (src_lts sge) s'').
      inv TAU; [done|]; econstructor 1; try eassumption.
      by eapply tausteptau_taustar_taustep; try eassumption; eexists; vauto.

    cut (Comp.consistent SrcMM Src s''); [|by eauto].
    eapply weaken in REL.
    revert H0 INF' REL tCONS'; clear; revert s'' t'' t'0; cofix X.
    intros s t ll ALW INF REL tCONS sCONS; inv INF.
    inversion ALW; simpl in *; clarify.
    generalize STEP; eapply wstep in STEP; try eassumption; des; clarify; des_err; vauto.
    by econstructor 1; [eassumption|eapply X; clear X; eauto].

  Case "not_eventually_always_ordered".
    pose proof (not_EA_intro H INF') as NO.
    clear INF INF'.
    revert s t NO REL tCONS sCONS; clear; cofix X; destruct 1; intros; clarify.
    assert (tCONS': Comp.consistent TgtMM Tgt t') by eauto.
    eapply Bsim.tau_simulation in TS; try eassumption; eauto.
    des; clarify; des_err; simpl in *; vauto.

    assert (Comp.consistent _ _ s') by eauto.

    generalize STEP; intro; eapply (Bsim.step (bsim SimST)) in STEP; try eassumption; clarify. 
    des; clarify; des_err; simpl in *.
    - by econstructor 2; eapply taustar_taustep; try eassumption; vauto.
    by econstructor 1; [eby eapply taustar_taustep|eapply X; clear X; eauto].
  Qed.

  (** Main theorem: Weak-tau simulation implies trace inclusion. *)
  Theorem traces_incl:
    forall {sprg tprg args t}
      (MP: match_prg sprg tprg)
      (VARG: valid_args args)
      (T: prog_traces TgtMM Tgt tprg args t),
      prog_traces SrcMM Src sprg args t. 
  Proof.
    intros; eapply Bsim.traces_incl; try edone.
    eby intros; eapply inftau1.
  Qed.

End WTsim. End WTsim.

