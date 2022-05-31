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
Require Import Libtactics.

Set Implicit Arguments.


(** * Labels structure *)
Record lbls : Type := mklbls 
  { labels        : Type
  ; tau           : labels
  ; pseudotau     : labels -> Prop           (*r unobservable [MEread]s *)
  ; fencetau      : labels -> Prop           (*r memory fences *)
  ; samekind      : labels -> labels -> Prop
  ; tau_1_kind    : forall t, samekind t tau -> t = tau
  ; pseudo_kind   : forall l l', pseudotau l' -> samekind l l' -> pseudotau l
  ; not_pseudo_tau: ~ pseudotau tau
  ; lbl_dec       : forall (x y : labels), {x = y} + {x <> y}
  ; is_error      : labels -> Prop
  }.

(** Instantiate external events as labels for the simulations. *)

Definition event_error (e : fullevent) : Prop :=
  match e with 
    | Evisible Efail => True
    | _ => False
  end.

Program Definition event_labels :=
  {| labels := fullevent
   ; tau := Etau
   ; pseudotau e := False
   ; fencetau e := False 
   ; samekind := event_samekind 
   ; is_error := event_error 
   ; lbl_dec := fullevent_dec    |}.
Solve Obligations using (by destruct t as [[]| |]).

(** Instantiate thread events as labels for the simulations. *)
         
Definition te_pseudotau (e : thread_event) : Prop :=
  match e with 
    | TEmem (MEread _ _ _) => True 
    | _ => False 
  end.

Program Definition thread_labels :=
  {| tau := TEtau
   ; pseudotau := te_pseudotau
   ; fencetau x := x = TEmem MEfence
   ; samekind := te_samekind 
   ; is_error x := x = TEext Efail
   ; lbl_dec := thread_event_eq_dec    |}.
Solve Obligations using 
  (intros; repeat (match goal with t : thread_event |- _ => 
                     destruct t as [[]|[]| | | | | |]; clarify end) ).

Program Definition mm_event_labels :=
  {| tau := MMtau
   ; pseudotau x := False
   ; fencetau  x := False
   ; is_error  x := False
   ; samekind x y := x = y 
   ; lbl_dec := mm_event_dec |}.

(** * Label transition systems *)

Section LTS.

Set Implicit Arguments.

Variable (lbl : lbls). 

Record lts : Type := mklts 
{ St      : Type                           (*r States *)
; stepr   : St -> labels lbl -> St -> Prop (*r step relation *)
}.


Variable ts : lts. 

(** Important definitions *)

(** An LTS is [receptive] if it can transition on any input. *)
Definition receptive : Prop :=
  forall l {l' s s'}, 
    stepr ts s l s' -> 
    samekind lbl l' l ->
    exists s'', stepr ts s l' s''.

(** An LTS is [determinate] if (i) two transitions from the same state
    imply that their labels are the same up to input value (i.e.,
    [samekind]), (ii) if there are two transitions from the same state
    with the same label, then their targets must be equal. *)

Definition determinate : Prop :=
  forall s {s' s'' l l'},
    stepr ts s l s' ->
    stepr ts s l' s'' ->
    (samekind lbl l l' /\
     (l = l' -> s' = s'')).

(** Zero or more tau transitions. *)
Inductive taustar : St ts -> St ts -> Prop :=
  | taustar_refl: forall s, taustar s s
  | taustar_step: 
    forall {s s' s''}, 
      stepr ts s (tau lbl) s' ->
      taustar s' s'' -> 
      taustar s s''.

Definition weakstep (s : St ts) (l : labels lbl) (s' : St ts) : Prop :=
  exists s1, exists s2, taustar s s1 /\ stepr ts s1 l s2 /\ taustar s2 s'.

Definition taustep (s : St ts) (l : labels lbl) (s' : St ts) : Prop :=
  exists s1, taustar s s1 /\ stepr ts s1 l s'.

Definition taureach (s : St ts) (s' : St ts) : Prop :=
  taustar s s' \/ taustar s' s.

Definition stuck (s : St ts) : Prop :=
  forall s' l, stepr ts s l s' -> False.

Lemma taustar_trans:
  forall {s1 s2 s3},
    taustar s1 s2 -> taustar s2 s3 -> taustar s1 s3.
Proof.
  intros s1 s2 s3 TS1 TS2.
  induction TS1 as [s | t1 t2 t3 TS1' TS2' IH]; try done.
  by apply (taustar_step (*_*) TS1'), IH. 
Qed.

Lemma taureach_refl: forall s, taureach s s.
Proof. by left; apply taustar_refl. Qed.

Lemma taureach_sym: forall s1 s2, taureach s1 s2 -> taureach s2 s1.
Proof. by destruct 1; unfold taureach; tauto. Qed.

Lemma weakstep_not_stuck: forall s l s', weakstep s l s' -> stuck s -> False.
Proof. eby intros s l s' (s1 & s2 & [] & ST & _) Stuck; eapply Stuck. Qed.

Lemma taustep_not_stuck: forall s l s', taustep s l s' -> stuck s -> False.
Proof. eby intros s l s' (s1 & [] & ST) Stuck; eapply Stuck. Qed.

Lemma steptau_taustar: forall s1 s2, stepr ts s1 (tau lbl) s2 -> taustar s1 s2.
Proof. intros; vauto. Qed.
  
Lemma weaksteptau_decomp:
  forall s1 s2, 
    weakstep s1 (tau lbl) s2 -> 
    exists s', stepr ts s1 (tau lbl) s' /\ taustar s' s2.
Proof.
  intros s1 s2 WS.
  destruct WS as [is1 [is2 [[s | t1 t2 t3 STt TSt] [ST TS']]]].
  exists is2. tauto.
  exists t2. split. assumption.
  apply steptau_taustar in ST.
  exact (taustar_trans (taustar_trans TSt ST) TS').
Qed.

Lemma tausteptau_decomp:
  forall s1 s2, 
    taustep s1 (tau lbl) s2 -> 
    exists s', stepr ts s1 (tau lbl) s' /\ taustar s' s2.
Proof.
  intros s1 s2 WS.
  destruct WS as [is1 [[s | t1 t2 t3 STt TSt] ST]].
  by exists s2; vauto. 
  exists t2; split; try done.
  eby eapply taustar_trans, steptau_taustar. 
Qed.

Lemma weaksteptau_taustar:
  forall s1 s2,
    weakstep s1 (tau lbl) s2 -> taustar s1 s2.
Proof.
  intros s1 s2 WS. 
  destruct WS as [s' [s'' [TS [ST TS']]]].
  exact (taustar_trans TS (taustar_step (*_*) ST TS')).
Qed.

Lemma tausteptau_taustar:
  forall s1 s2,
    taustep s1 (tau lbl) s2 -> taustar s1 s2.
Proof.
  intros s1 s2 (s' & TS & ST); eapply taustar_trans; try edone; vauto.
Qed.

Lemma taustar_weakstep:
  forall s1 s2 s3 l,
    taustar s1 s2 -> weakstep s2 l s3 -> weakstep s1 l s3.
Proof.
  intros s1 s2 s3 l STT WS.
  destruct WS as [s' [s'' [TS1 [ST TS2]]]].
  exists s'. exists s''.
  repeat split; try assumption.
  exact (taustar_trans STT TS1).
Qed.

Lemma taustar_taustep:
  forall s1 s2 s3 l,
    taustar s1 s2 -> taustep s2 l s3 -> taustep s1 l s3.
Proof.
  intros s1 s2 s3 l STT [s' [TS1 ST]].
  exists s'; split; try done.
  exact (taustar_trans STT TS1).
Qed.

Lemma weakstep_taustar:
  forall s1 s2 s3 l,
    weakstep s1 l s2 -> taustar s2 s3 -> weakstep s1 l s3.
Proof.
  intros s1 s2 s3 l [s' [s'' [TS1 [ST TS2]]]] STT.
  exists s'. exists s''.
  repeat split; try assumption.
  exact (taustar_trans TS2 STT).
Qed.

Lemma steptau_weakstep:
  forall s1 s2 s3 l,
    stepr ts s1 (tau lbl) s2 -> weakstep s2 l s3 -> weakstep s1 l s3.
Proof.
  intros s1 s2 s3 l STT WS.
  destruct WS as [s' [s'' [TS1 [ST TS2]]]].
  exists s'. exists s''.
  repeat split; try assumption.
  exact (taustar_step (*_*) STT TS1).
Qed.

Lemma step_taustar_weakstep: 
  forall s1 s2 s3 l,
    stepr ts s1 l s2 -> taustar s2 s3 -> weakstep s1 l s3.
Proof.
  intros; eexists; eexists.
  repeat split;
    [ apply taustar_refl | eassumption | eassumption]; done.
Qed.

Lemma step_weakstep: 
  forall s1 s2 l, stepr ts s1 l s2 -> weakstep s1 l s2.
Proof.
  intros; eexists; eexists.
  by repeat split;
    [ apply taustar_refl | eassumption | apply taustar_refl ].
Qed.

Lemma step_taustep: 
  forall s1 s2 l, stepr ts s1 l s2 -> taustep s1 l s2.
Proof. intros; eexists; vauto. Qed.


Lemma steptau_taustar_taustep: 
  forall s1 s2 s3, stepr ts s1 (tau lbl) s2 -> taustar s2 s3 -> taustep s1 (tau lbl) s3.
Proof.
  intros s1 s2 s3 STEP TAU.
  revert s1 STEP.
  induction TAU; intros; [by eexists; vauto|].
  by eapply taustar_taustep, IHTAU; try eassumption; vauto.
Qed.

Lemma tausteptau_taustar_taustep: 
  forall s1 s2 s3, taustep s1 (tau lbl) s2 -> taustar s2 s3 -> 
                   taustep s1 (tau lbl) s3.
Proof.
  intros s1 s2 s3 [s' [TAU' ST]] TAU.
  eby eapply taustar_taustep, steptau_taustar_taustep.
Qed.


Definition can_do_error s :=
  exists s', exists l, is_error _ l /\ stepr ts s l s'.

Definition stuck_or_error s := stuck s \/ can_do_error s.

(** Eventually will get stuck or do an errror transition. *)
Inductive ev_stuck_or_error (s: St ts): Prop :=
  | ev_stuck_or_error_stuck: 
    forall 
      (STUCK: stuck s),
      ev_stuck_or_error s
  | ev_stuck_or_error_error: 
    forall l s' (STEP: stepr ts s l s')
       (ISERR: is_error lbl l),
       ev_stuck_or_error s
  | ev_stuck_or_error_tau:
    forall s' 
      (TAUSTEP: stepr ts s (tau lbl) s')
      (ERR: ev_stuck_or_error s'),
      ev_stuck_or_error s
  | ev_stuck_or_error_pseudotau:
    forall l
      (ISPSEUDO: pseudotau lbl l) s'
      (STEP: stepr ts s l s')
      (ERR: forall l s',
        pseudotau lbl l ->
        stepr ts s l s' ->
        ev_stuck_or_error s'),
      ev_stuck_or_error s.

Lemma ev_stuck_or_error_taustar:
  forall s s' (TAU: taustar s s'),
    ev_stuck_or_error s' ->
    ev_stuck_or_error s.
Proof.
  intros; induction TAU; eauto using ev_stuck_or_error.
Qed.

Lemma ev_stuck_or_error1:
  forall s s', 
    taustar s s' -> 
    stuck_or_error s' ->
    ev_stuck_or_error s.
Proof.
  induction 1.
    by intros [?|(? & ? & ? & ?)]; vauto.
  by intro X; specialize (IHtaustar X); vauto.
Qed.

End LTS.



(** * Forward and backward simulation correspondence *)

Section FBSimulations.

(* Labels *)
Variable lbl : lbls.

(* Source and target transition systems *)
Variables (src tgt : lts lbl).

Hypothesis source_receptive : receptive src.
Hypothesis target_determinate : determinate tgt.
Hypothesis source_dec_progress :
  forall s, stuck src s \/
            (exists l, exists s', stepr src s l s'). 

Section ForwardSim.

Variable r : St src -> St tgt -> Prop.
Variable c : St src -> St src -> Prop.

(** Normal (thread-local) forward simulation *)

Definition forward_sim : Prop :=
  well_founded c /\
  (forall s t l s', stepr src s l s' -> r s t ->
     (ev_stuck_or_error src s) \/
     (exists t', weakstep tgt t l t' /\ r s' t') \/
     (l = tau _ /\ r s' t /\ c s' s)).

End ForwardSim.

(** Lockstep (thread-local) forward simulation with pseudotau actions *)

Definition lockstep_forward_sim (allow_pseudotaus:bool) (r : St src -> St tgt -> Prop): Prop :=
  (forall s t l s', stepr src s l s' -> r s t ->
     (exists t', stepr tgt t l t' /\ r s' t') \/
     (allow_pseudotaus /\ pseudotau lbl l /\ (exists t', stepr tgt t (tau lbl) t' /\ 
         (forall l0 s0, samekind lbl l0 l -> stepr src s l0 s0 -> r s0 t')))).

(** (Thread-local) backward simulation *)

Definition backward_sim (allow_pseudotaus : bool)
  (r : St tgt -> St src -> Prop)
  (c : St tgt -> St tgt -> Prop) : Prop :=
  well_founded c /\
  (forall s t, stuck tgt t -> r t s -> ev_stuck_or_error src s) /\
  (forall s t l t', stepr tgt t l t' -> r t s ->
     (exists s', taustep src s l s' /\ r t' s') \/
     (l = tau lbl /\ r t' s /\ c t' t) \/
     (allow_pseudotaus /\ l = tau lbl /\ (exists l0, forall l', samekind lbl l' l0 -> 
                       exists s', taustep src s l' s' /\ pseudotau lbl l' /\ r t' s')) \/
     (fencetau lbl l /\ (exists s', taustep src s (tau lbl) s' /\ r t' s')) \/
     ev_stuck_or_error src s).

(** ** Dealing with lockstep pseudotau forward simulations *)

Section LockstepForwardToBackwardSim.

(* Let us assume that we have a forward simulation ... *)   
Variable allow_pseudotaus : bool.
Variable fsr : St src -> St tgt -> Prop.
Hypothesis fsim : lockstep_forward_sim allow_pseudotaus fsr.

(* The main result: bsr and bsc are backward simulation *)
Theorem lockstep_forward_to_backward_sim:
  backward_sim allow_pseudotaus (fun x y => fsr y x) (fun x y => False).
Proof.
  split; [by constructor|].
  split. (* Stuck state correspondence *)
    intros s t TStuck BSt.
    eapply ev_stuck_or_error_stuck.
    destruct (source_dec_progress s) as [|[l [s' ST]]]; [done|].
    pose proof (@fsim  _ t _ _ ST BSt) as H. 
    eby des; eelim TStuck.

  (* The bulk of the proof is establishing the simulation diagram: *)
  intros s t l t' STtt' BS.
    destruct (source_dec_progress s) as [|[l0 [s0' ST0]]].
      by right; right; right; right; eapply ev_stuck_or_error_stuck.
    destruct (@fsim _ t _ _ ST0 BS) as [ [t'0 [ST0' FS0]] | [? [PSl0 [t'0 [ST0' X]]]]].
      destruct (target_determinate _ _ _ _ _ STtt' ST0') as [SK _].
      destruct (source_receptive _ _ _ _ ST0 SK) as [s' ST].

     left; exists s'; split; [apply step_taustep|]; try done.
     destruct (@fsim _ t _ _ ST BS) as [ [t2 [STtt2 ?]] | [? [PSl [t2 [STtt2 ?]]]]].
       by rewrite (proj2 (target_determinate _ _ _ _ _ STtt' STtt2) (refl_equal _)).
     rewrite (tau_1_kind _ _ (proj1 (target_determinate _ _ _ _ _ STtt' STtt2))) in PSl.
     by apply not_pseudo_tau in PSl.
  (* pseudotau transition *)
  destruct (target_determinate _ _ _ _ _ STtt' ST0') as [SK Y].
  apply tau_1_kind in SK; subst l.
  rewrite <- (Y (refl_equal _)) in *. 
  right; right; left; split; try done.
  split; try done. 
  exists l0; intros l SKll0.
  destruct (source_receptive _ _ _ _ ST0 SKll0) as [s' ST].
  pose proof (X _ _ SKll0 ST) as FS'.
  exists s'; split; [apply step_taustep|split]; try done.
  eby eapply pseudo_kind.
Qed.
     
End LockstepForwardToBackwardSim.

(** ** Converting normal forward simulations *)

Section ForwardToBackwardSim.

(* Let us assume that we have a forward simulation ... *)
Variable fsr : St src -> St tgt -> Prop.
Variable fsc : St src -> St src -> Prop.
Hypothesis fsim : forward_sim fsr fsc.

Lemma fsc_wf:
  well_founded fsc.
Proof. pose proof fsim. unfold forward_sim in *. tauto. Qed.

(** Backward simulation construction. *)
Definition bsr (t : St tgt) (s : St src) : Prop :=
  exists t', fsr s t' /\ taureach tgt t t'.

(** Well-founded relation for the backward simulation. *)
Inductive bsc : St tgt -> St tgt -> Prop :=
  | bsc_nontau : forall t t' t'' l,
      stepr tgt t (tau lbl) t' ->
      stepr tgt t' l t'' ->
      l <> tau lbl ->
        bsc t' t
  | bsc_step : forall t t' t'',
      stepr tgt t (tau lbl) t' ->
      bsc t'' t' -> bsc t' t.

Lemma bsc_impl_taustar:
  forall t t',
    bsc t' t -> stepr tgt t (tau lbl) t'.
Proof.
  intros t t' H.
  induction H; auto.
Qed.

Lemma bsc_unique_pred:
  forall t t' t'',
    bsc t' t -> bsc t'' t -> t' = t''.
Proof.
  intros t t' t'' H1 H2.
  apply bsc_impl_taustar in H1.
  apply bsc_impl_taustar in H2.
  apply (proj2 (target_determinate _ _ _ _ _ H1 H2)).
  reflexivity.
Qed.

Lemma bsc_wf: 
  well_founded bsc.
Proof.
  intro a.
  apply Acc_intro.
  intros y H.
  induction H as [t t' t'' l TS TL Lntau | t t' t'' TS IC IH].
  (* base case - bsc_nontau *)
  apply Acc_intro. intros y H2. apply bsc_impl_taustar in H2.
  pose proof (proj1 (target_determinate _ _ _ _ _ TL H2)) as SKL.
  apply tau_1_kind in SKL. contradiction.
  (* step case - bsc_step *)
  apply Acc_intro. intros y H2.
  rewrite (@bsc_unique_pred _ _ _ IC H2) in *.
  assumption.
Qed.

(* Auxiliary lemmata for the backward simulation proof: *)
Lemma ltaustar_eq:
  forall t1 t2 t3 l,
    stepr tgt t1 l t2 ->
    l <> tau lbl ->
    taustar tgt t1 t3 -> 
    t1 = t3.
Proof.
  intros t1 t2 t3 l ST Lntau TS.
  destruct TS as [|s1 s2 s3 H]. reflexivity.
  pose proof (proj1 (target_determinate _ _ _ _ _ ST H)) as SKL.
  apply tau_1_kind in SKL. 
  byContradiction; auto. 
Qed.

Lemma lweaktaustar:
  forall t1 t2 t3 l,
    weakstep tgt t1 l t2 ->
    l <> tau lbl ->
    taustar tgt t1 t3 -> 
    weakstep tgt t3 l t2.
Proof.
  intros t1 t2 t3 l WS Lntau TS.
  destruct WS as [t' [t'' [TS1 [ST TS2]]]].
  exists t'. exists t''. repeat split; try assumption.
  (* By induction on the first taustar from weakstep t1 l t2 *)
  induction TS1 as [t1 | t1' t2' t3' Stau TS' IH].
  (* taustar_refl case *)
  rewrite <- (@ltaustar_eq _ _ _ _ ST Lntau TS).
  apply taustar_refl.
  (* taustar_step case *)
  destruct TS as [u | u1 u2 u3 Htau Hts].
  exact (taustar_step Stau TS').
  apply IH; try assumption.
  rewrite (proj2 (target_determinate _ _ _ _ _ Stau Htau)); auto.
Qed.

Lemma lweakbothtep:
  forall t1 t2 t3 l,
    taureach tgt t1 t2 ->
    l <> tau lbl ->
    weakstep tgt t2 l t3 -> 
    weakstep tgt t1 l t3.
Proof.
  intros t1 t2 t3 l TR Lntau WS.
  destruct TR as [TS | TS].
  (* -> direction of taureach *)
  destruct WS as [t' [t'' [TS1 [TS2 TS3]]]].
  exists t'. exists t''.
  repeat split; try assumption.
  exact (taustar_trans TS TS1).
  (* <- direction of taureach - just use the previous lemma *)
  apply (@lweaktaustar _ _ _ _ WS Lntau TS).
Qed.

Lemma taustar2_taureach:
  forall t1 t2 t3,
    taustar tgt t1 t2 -> taustar tgt t1 t3 -> taureach tgt t2 t3.
Proof.
  intros t1 t2 t3 TS1 TS2.
  induction TS1 as [t1 | t1' t2' t3' Stau TS' IH].
  left; assumption.
  destruct TS2 as [t1 | t1' t2'' t3'' Stau' TS''].
  right. apply (taustar_step Stau TS').
  rewrite (proj2 (target_determinate _ _ _ _ _ Stau Stau') 
                 (refl_equal (tau lbl))) in *.
  apply IH. assumption.
Qed.

Lemma taureach_taustar_taureach:
  forall t1 t2 t3,
    taureach tgt t1 t2 -> taustar tgt t2 t3 -> taureach tgt t1 t3.
Proof.
  intros t1 t2 t3 TR TS.
  destruct TR as [TS' | TS']. left. exact (taustar_trans TS' TS).
  exact (@taustar2_taureach _ _ _ TS' TS).
Qed.

Lemma taustar_labels:
  forall t1 t2 t3 t4 t5 l l', 
    l <> tau lbl ->
    l' <> tau lbl ->
    taustar tgt t1 t2 -> stepr tgt t2 l t3 ->
    taustar tgt t1 t4 -> stepr tgt t4 l' t5 ->
    t2 = t4 /\ samekind lbl l l' /\ (l = l' -> t3 = t5).
Proof.
  intros t1 t2 t3 t4 t5 l l' Lntau Lntau' TS1 ST1 TS2 ST2.
  pose proof (@taustar2_taureach _ _ _ TS1 TS2) as TR.
  assert (T2_eq_T4: t2 = t4).
  destruct TR as [TS3 | TS3].
    apply (@ltaustar_eq _ _ _ _ ST1 Lntau TS3).
    symmetry; apply (@ltaustar_eq _ _ _ _ ST2 Lntau' TS3).
    split. assumption.
  rewrite T2_eq_T4 in *.
  exact (target_determinate _ _ _ _ _ ST1 ST2).
Qed.

Lemma forward_progress:
  forall s t
    (SIMst : fsr s t),
    (ev_stuck_or_error src s \/
     exists sm, exists tm, exists s', exists t', exists l,
       taustar src s sm /\ stepr src sm l s' /\
       taustar tgt t tm /\ weakstep tgt tm l t' /\
       fsr sm tm /\ fsr s' t').
Proof.
  induction s as [s IH] using (well_founded_ind fsc_wf); intros.
  destruct (source_dec_progress s) as [Stuck | Step]. 
  (* If we are stuck then it is easy... *)
    by left; eapply ev_stuck_or_error_stuck.
  (* otherwise s can do step... *)
  destruct Step as [l [s' Step]].
  (* ... so use the forward simulation, so: *)
  destruct fsim as [_ FS].
  destruct (FS s t l s' Step SIMst) as 
    [Err | [[t' TStep] | [Ltau [FS' FSCss]]]]; clear FS. 
  (* a. If error, then still easy *)
     by left.
  (* b. we can do matching step in target, so we are done: *)
    right. exists s. exists t. exists s'. exists t'. exists l.
    by repeat split; try tauto; apply taustar_refl.
  (* c. we can do tau step in target and stutter in source, so we use
        the induction hypothesis. *)
    specialize (IH s' FSCss t FS').
    destruct IH as [STUCK | 
                    [sm [tm [sp [tp [lp [TSsp [STp [TStm [WStp [FSm FSp]]]]]]]]]]].
    (* either we got stuck in the IH *)
    eby clarify; left; eapply ev_stuck_or_error_tau.
    (* or we can do step in IH *)
    right. exists sm. exists tm. exists sp. exists tp. exists lp.
    repeat split; try assumption.
    by rewrite Ltau in Step; apply (taustar_step Step).
Qed.

(** This is the fundamental lemma that uses receptiveness to force 
   the source lts to do the same step as the target lts. All this is 
   wrapped up in an inductive argument to get around the pesky tau 
   actions (using the old trick with determinacy). *)
Lemma forward_progress_nontau_aux:
  forall t1 t2,
    taustar tgt t1 t2 ->
    forall t3 s t l,
      fsr s t ->
      taustar tgt t1 t ->
      stepr tgt t2 l t3 ->
      l <> tau lbl ->
        ev_stuck_or_error src s \/
        (exists s1, exists s2, exists t5,
          taustar src s s1 /\ stepr src s1 l s2 /\
            taustar tgt t3 t5 /\ fsr s2 t5).
Proof.
  intros t1 t2 TSt1t2.
  induction TSt1t2 as [t1 | t1 t2 t3 STt1t2 TSt2t3 IH].
  (* Base case *)
  intros t4 s t l FSst TSt1t STt1t3 Lntau.
  pose proof (@ltaustar_eq _ _ _ _ STt1t3 Lntau TSt1t); clear TSt1t; subst t.
  (* Force one step through forward_progress *)
  destruct (@forward_progress _ _ FSst) as [Stuck |
    [sm [tm [s' [t' [l' [TSssm [STsms' [TStm [WSt1t' [FSstm FSst']]]]]]]]]]].
  (* if stuck, it is trivial *)    
  by left.
  (* otherwise, do case analysis on l' being tau *)
  destruct (lbl_dec lbl l' (tau lbl)) as [Ltau' | Lntau'].
    subst l'.
    destruct (weaksteptau_decomp (taustar_weakstep TStm WSt1t')) as [it [STit _]].
    elim Lntau; apply tau_1_kind.
    by apply (proj1 (target_determinate _ _ _ _ _ STt1t3 STit)).
  (* l' <> tau *)
  destruct WSt1t' as [t5 [t6 [TSt1t5 [STt5t6 TSt6t']]]].
  pose proof (@ltaustar_eq _ _ _ _ STt1t3 Lntau TStm) as t1_eq_tm; clear TStm; subst tm. 
  pose proof (@ltaustar_eq _ _ _ _ STt1t3 Lntau TSt1t5) as t1_eq_t5; clear TSt1t5; subst t5.
  pose proof (proj1 (target_determinate _ _ _ _ _ STt1t3 STt5t6)) as SK.

  destruct (source_receptive _ _ _ _ STsms' SK) as [s2 STsms2].
    clear STsms' STt5t6 SK Lntau' l'.
    destruct fsim as [_ FS].
    destruct (FS sm t1 l s2 STsms2 FSstm) as 
        [Err | 
         [[t2 [[t7 [t8 [TSt1t7 [STt7t8 TSt8t2]]]] FSs2t2]] | 
         [Ltau [FS' FSCss]]]]. 
    (*1*) eby left; eapply ev_stuck_or_error_taustar. 
    (*2*) 
      right.
      pose proof (@ltaustar_eq _ _ _ _ STt1t3 Lntau TSt1t7) as t1_eq_t7; clear TSt1t7; subst t7. 
      exists sm. exists s2. exists t2.
      rewrite <- (proj2 (target_determinate _ _ _ _ _ STt1t3 STt7t8) 
        (refl_equal l)) in TSt8t2.
      repeat split; try tauto. 
    (*3*) contradiction.
 
  (* Induction step is quite similar to the base case *)
  intros t4 s t l FSst TSt1t STt1t3 Lntau. 
  (* Force one step through forward_progress *)
  destruct (@forward_progress _ _ FSst) as [Stuck |
    [sm [tm [s' [t' [l' [TSssm [STsms' [TStm [WStmt' [FSstm FSst']]]]]]]]]]].
  (* if stuck, it is trivial *)    
  by left. 
  (* otherwise do case analysis on l' being tau *)
  destruct (lbl_dec lbl l' (tau lbl)) as [Ltau' | Lntau'].
    (* l' = tau case *)
    subst l'.
    (* Here we differ from the base case -> we go to the induction hypothesis *)
    destruct (weaksteptau_decomp (taustar_weakstep TSt1t (taustar_weakstep TStm WStmt')))  
      as [it [STit TSit]].
    rewrite (proj2 (target_determinate _ _ _ _ _ STt1t2 STit) 
                   (refl_equal (tau lbl))) in *.
    specialize (IH t4 s' t' l FSst' TSit STt1t3 Lntau).
    destruct IH as [Stuck | [sp1 [sp2 [tp2 [TSsp [STsp 
                      [TStp FSp]]]]]]].
    (* Stuck case *)
    left; eapply ev_stuck_or_error_taustar, Stuck.
    by apply (taustar_trans TSssm), (taustar_step STsms'), taustar_refl.
    (* Step case: *)
    right. exists sp1. exists sp2. exists tp2.
    repeat split; try assumption. 
    by apply (taustar_trans TSssm); apply (taustar_step STsms').

    (* l' is not tau *)  
    destruct WStmt' as [t5 [t6 [TStmt5 [STt5t6 TSt6t']]]].
    pose proof (taustar_step STt1t2 TSt2t3) as TSt1t3.
    pose proof (taustar_trans TSt1t (taustar_trans TStm TStmt5)) as TSt1t5.
    pose proof (proj1 (@taustar_labels _ _ _ _ _ _ _ 
       Lntau Lntau' TSt1t3 STt1t3 TSt1t5 STt5t6)) as t3_eq_t5; subst t3.
    pose proof (proj1 (target_determinate _ _ _ _ _ STt1t3 STt5t6)) as SK.
    destruct (source_receptive _ _ _ _ STsms' SK) as [s2 STsms2].
    destruct fsim as [_ FS].
    clear STt1t2 TSt2t3 IH t2.
    destruct (FS sm tm l s2 STsms2 FSstm) as 
      [Err | 
       [[t2 [[t7 [t8 [TStmt7 [STt7t8 TSt8t2]]]] FSs2t2]] | 
       [Ltau _]]]; 
      try contradiction. 
    eby left; eapply ev_stuck_or_error_taustar. 
    right. exists sm. exists s2. exists t2.
    pose proof (taustar_trans TSt1t (taustar_trans TStm TStmt7)) as TSt1t7.
    pose proof (proj1 (@taustar_labels _ _ _ _ _ _ _ 
       Lntau Lntau TSt1t5 STt1t3 TSt1t7 STt7t8)) as t5_eq_t7; subst t5.
    by rewrite <- (proj2 (target_determinate _ _ _ _ _ STt1t3 STt7t8) 
      (refl_equal l)) in TSt8t2.
Qed.

(* Cleaner formulation of the previous lemma: *)
Lemma sourcesim_nontau:
  forall s t t1 t2 l, 
    fsr s t ->
    l <> tau lbl ->
    taustar tgt t t1 ->
    stepr tgt t1 l t2 ->
      ev_stuck_or_error src s \/
      (exists s1, exists s', exists t',
         taustar src s s1 /\ stepr src s1 l s' /\
         taustar tgt t2 t' /\
         fsr s' t').
Proof.
  eauto using forward_progress_nontau_aux, taustar_refl.
Qed.

(* Single tau step followed by non-tau weakstep implies order *)
Lemma stau_ts_impl_order:
  forall t t' t'' l
    (STEP: stepr tgt t (tau lbl) t')
    (WS: taustep tgt t' l t''),
    l <> tau lbl ->
    bsc t' t.
Proof.
  intros; destruct WS as [t1 [TStt1 STt1t2]].
  revert t STEP; induction TStt1; eauto using bsc.
Qed.  

Lemma stau_ws_impl_order:
  forall t t' t'' l
    (STEP: stepr tgt t (tau lbl) t')
    (WS: weakstep tgt t' l t''),
    l <> tau lbl ->
    bsc t' t.
Proof.
  intros; destruct WS as [t1 [t2 [TStt1 [STt1t2 _]]]].
  revert t STEP; induction TStt1; eauto using bsc.
Qed.

(* The following two lemmata are useful for simulating stuck states *)
Lemma taustar_stuck_sim:
  forall s t ts,
    fsr s ts ->
    taustar tgt t ts ->
    stuck tgt t ->
    ev_stuck_or_error src s.
Proof.
  intros s t ts FS TS Stuck.
  destruct (@forward_progress _ _ FS) as [Stuck' | 
    [sm [tm [s' [tp [l [TSs [STsm [TStp [WStm _]]]]]]]]]]; try done.  
  byContradiction.
  exact (weakstep_not_stuck (taustar_weakstep (taustar_trans TS TStp)  WStm) 
                            Stuck).
Qed.

Lemma taustar_stuck_sim2:
  forall t t',
    taustar tgt t t' ->
    forall s ts,
      fsr s ts ->
      taustar tgt t ts ->
      stuck tgt t' ->
      ev_stuck_or_error src s.
Proof.
  intros t t' TStt'.
  induction TStt' as [t | t t1 t2 ST TS IH].
  (* Base case *)
  intros s ts FS TSts Stuck.
  exact (@taustar_stuck_sim _ _ _ FS TSts Stuck).
  
  (* Induction step *)  
  intros s ts FS TSts Stuck.
  destruct TSts as [t | t t3 ts STtt3 TSt3t4].
    (* We have run out of taus before the simulation, so 
     we have to force progress *) 
    destruct (@forward_progress _ _ FS) as [Stuck' | 
      [sm [tm [s' [tp [l [TSs [STsm [TStp [WStm [FS1 FS2]]]]]]]]]]].  
    assumption. 
    destruct (lbl_dec lbl l (tau lbl)) as [Ltau | Lntau].
      subst l.
      destruct (weaksteptau_decomp (taustar_weakstep TStp WStm))
        as [ti [STtau TSti]].
      pose proof (proj2 (target_determinate _ _ _ _ _ ST STtau) 
          (refl_equal (tau lbl))) as t1_eq_ti; rewrite <- t1_eq_ti in *.
      eapply ev_stuck_or_error_taustar, (IH _ _ FS2 TSti Stuck). 
      exact (taustar_trans TSs (taustar_step STsm (taustar_refl _ _))).
    pose proof (@lweaktaustar _ _ _ _ (taustar_weakstep TStp WStm) 
      Lntau (taustar_step ST TS)) as WSt2tp.
    byContradiction. exact (weakstep_not_stuck WSt2tp Stuck).

  (* We have one step, so we just go to the IH *)
  pose proof (proj2 (target_determinate _ _ _ _ _ ST STtt3) 
      (refl_equal (tau lbl))) as t1_eq_t3; rewrite <- t1_eq_t3 in *.
  exact (IH _ _ FS TSt3t4 Stuck).
Qed.

Lemma fsr_in_bsr:
  forall s t,
    fsr s t -> bsr t s.
Proof.
  intros; exists t; split; vauto. 
Qed.

(** The main result: bsr and bsc are a backward simulation. *)
Theorem forward_to_backward_sim:
  backward_sim false bsr bsc.
Proof.
  split; [exact bsc_wf|].

  split. (* Stuck state correspondence *)
  intros s t TStuck BSt. destruct BSt as [t' [FSst' TR]].
  destruct TR as [TSttp | TStpt].
  exact (@taustar_stuck_sim _ _ _ FSst' TSttp TStuck).
  exact (@taustar_stuck_sim2 _ _ TStpt _ _ FSst' (taustar_refl _ t') TStuck).
  
  (* The bulk of the proof is establishing the simulation diagram: *)
  intros s t l t' STtt' BS.
  destruct BS as [t'' [FS TRttpp]].
  destruct (lbl_dec lbl l (tau lbl)) as [Ltau | Lntau].
  (* Case l = tau *)
      subst l.
      (* Force progress *)
      destruct (@forward_progress _ _ FS) as [Stuck |
        [sm [tm [s1 [t1 [l [TSssm [STsms' [TStm [WSt1t' [FSstm FSst']]]]]]]]]]].
      (* Stuck case is easy *) tauto.
      apply taureach_sym in TRttpp.
      pose proof (taureach_sym (@taureach_taustar_taureach _ _ _ TRttpp 
        (steptau_taustar _ _ _ STtt'))) as TRtptpp.
      (* pose proof (taureach_taustar_taureach _ _ _ TRttpp TStm) as TRttm.  *)
      destruct (lbl_dec lbl l (tau lbl)) as [Ltau | Lntau].
        subst l. 
        left. exists s1. split.
        by exists sm. 
        exists t1. split. assumption.
      exact (@taureach_taustar_taureach _ _ _ TRtptpp 
        (weaksteptau_taustar (taustar_weakstep TStm WSt1t'))).
      pose proof (@lweakbothtep _ _ _ _ TRtptpp Lntau (taustar_weakstep TStm 
                                                                       WSt1t'))
        as WStpt1.
      right; left; split. reflexivity.
      split. exists t''. split; assumption. 
      exact (@stau_ws_impl_order _ _ _ _ STtt' WStpt1 Lntau). 

  (* Case l <> tau *)
      assert (TStppt: taustar tgt t'' t).  
        destruct TRttpp as [TS | TS]; [|done].
        by rewrite (@ltaustar_eq _ _ _ _ STtt' Lntau TS); apply taustar_refl.
      destruct (@sourcesim_nontau s t'' t t' l FS Lntau TStppt STtt')
        as [Stuck | [s1 [s2 [t1 [TSss1 [STs1s2 [TStpt1 FS2]]]]]]]. 
      tauto. 
      left. exists s2. split.
      by exists s1. 
      by exists t1; vauto. 
Qed.
     
End ForwardToBackwardSim.

End FBSimulations.


(** * Simulation with undefs *)

Section ForwardToBackwardUndefSim.

(** Labels *)
Variable lbl : lbls.

(** Source and target transition systems *)
Variables (src tgt : lts lbl).

(** Assumptions on the transition systems *)
Hypothesis source_receptive : receptive src.
Hypothesis target_determinate : determinate tgt.
Hypothesis source_dec_progress :
  forall s, stuck src s \/
            (exists l, exists s', stepr src s l s'). 

(** Less defined comparison in output values.
    In essence, this only relates write of an undefined value to a write
    of defined value to the same memory location. *)

Variable ldo : labels lbl -> labels lbl -> Prop.

(** Less defined comparison in input labels. Note that unlike
    [ldo], [ldi] is reflexive. *)

Variable ldi : labels lbl -> labels lbl -> Prop.

(** Assumptions on [ldi] and [ldo]. *)

Hypothesis ldo_samekind_eq: 
  forall l1 l2 l, samekind _ l1 l2 ->
                  ldo l l2 ->
                  l1 = l2.

Hypothesis ldo_not_tau:
  forall l1, ldo l1 (tau _) -> False.

Hypothesis ldi_refl:
  forall l, ldi l l.

(** Forward simulation with undefined values *)

Definition forward_sim_with_undefs
  (r : St src -> St tgt -> Prop)
  (c : St src -> St src -> Prop) : Prop :=
  well_founded c /\
  (forall s t l s', 
    stepr _ s l s' -> r s t ->
     (ev_stuck_or_error _ s) \/
     (l = tau _ /\ r s' t /\ c s' s) \/
     (exists t', (exists l', ldo l l' /\ weakstep tgt t l' t' /\ r s' t') \/
                 (weakstep tgt t l t' /\
                  forall l'', ldi l'' l -> exists s'', 
                    stepr _ s l'' s'' /\
                    r s'' t'))).

(** Backward simulation with undefined values *)

Definition backward_sim_with_undefs
  (r : St tgt -> St src -> Prop)
  (c : St tgt -> St tgt -> Prop) : Prop :=
  well_founded c /\
  (forall s t, stuck tgt t -> r t s ->
    ev_stuck_or_error _ s) /\
  (forall s t l t', 
    stepr tgt t l t' -> r t s ->
     (l = tau lbl /\ r t' s /\ c t' t) \/
     (ev_stuck_or_error _ s) \/
     (exists s', exists l', 
       ldo l' l /\ taustep src s l' s' /\ r t' s') \/
     (forall l'', ldi l'' l -> exists s',
       taustep src s l'' s' /\ r t' s')).

Section ForwardToBackwardSim.

(** Let us assume that we have a forward simulation ... *)   
Variable fsr : St src -> St tgt -> Prop.
Variable fsc : St src -> St src -> Prop.
Hypothesis fsim : forward_sim_with_undefs fsr fsc.

Lemma fscu_wf: well_founded fsc.
Proof. pose proof fsim. unfold forward_sim_with_undefs in *. tauto. Qed.

Lemma forward_progress_with_undef:
  forall s t, 
    fsr s t ->
    (ev_stuck_or_error _ s \/
     exists sm, exists tm, exists t', exists l,
       taustar src s sm /\ taustar tgt t tm /\ fsr sm tm /\
       weakstep tgt tm l t' /\
       ((exists l', exists s', 
           ldo l' l /\ stepr src sm l' s' /\ fsr s' t') \/
        (forall l'', ldi l'' l -> exists s'',
           stepr src sm l'' s'' /\ fsr s'' t'))).
Proof.
  induction s as [s IH] using (well_founded_ind fscu_wf).
  intros t SIMst.
  destruct (source_dec_progress s) as [Stuck | Step]. 
  (* If we are stuck then it is easy... *)
  by vauto. 
  (* otherwise s can do step... *)
  destruct Step as [l [s' Step]].
  (* ... so use the forward simulation, so: *)
  destruct fsim as [_ FS].
  destruct (FS s t l s' Step SIMst) as 
    [Err | [[Ltau [FS' FSCss]] | [t' TStep]]]. 
  clear FS.
  (* a. If error, then still easy *)
  by vauto. 
  (* b. we can do tau step in target and stutter in source, so we use
        the induction hypothesis. *)
  clear FS. specialize (IH s' FSCss t FS').
  destruct IH as [Stuck | 
                  [sm [tm [tp [lp [TSsm [TSt [FSm [WStp Cases]]]]]]]]].
  (* either we got stuck in the IH *)
  left; eapply ev_stuck_or_error_taustar, Stuck; subst. 
  exact (taustar_step Step (taustar_refl _ _)).
  (* or we can do step in IH *)
  right. exists sm. exists tm. exists tp. exists lp.
  repeat split; try assumption.
  rewrite Ltau in Step.
  exact (taustar_step Step TSsm). 
  (* b. we can do matching step in target, so we are done: *)
  right. exists s. exists t. exists t'. 
  destruct TStep as [[l' LDOStep] | [WStltp LDIStep]].
  (* ldo step *)
  exists l'.
  repeat split; try tauto; try apply taustar_refl.
  left; exists l; exists s'; tauto.
  (* ldi step *)
  exists l. repeat split; try tauto; try apply taustar_refl.
Qed.

Lemma weakstep_samekind:
  forall t1 t2 t3 l l',
    l <> tau lbl ->
    l' <> tau lbl ->
    weakstep tgt t1 l t2 ->
    weakstep tgt t1 l' t3 ->
    samekind lbl l l'.
Proof.
  intros t1 t2 t3 l l' Lntau Lpntau
    [t4 [t5 [TSt1t4 [STt4 _]]]]
    [t6 [t7 [TSt1t6 [STt6 _]]]].
  by destruct (@taustar_labels _ _ target_determinate _ _ _ _ _ _ _
     Lntau Lpntau TSt1t4 STt4 TSt1t6 STt6) as [_ [SK _]].
Qed.

Lemma forward_progress_nontau_aux_with_undef:
  forall t1 t2,
    taustar tgt t1 t2 ->
    forall t3 s t l,
      fsr s t ->
      taustar tgt t1 t ->
      stepr tgt t2 l t3 ->
      l <> tau lbl ->
        ev_stuck_or_error _ s \/
        (exists s1, exists t5,
          taustar src s s1 /\ taustar tgt t3 t5 /\
          ((exists l', exists s2, ldo l' l /\ stepr src s1 l' s2 /\ 
                                  fsr s2 t5) \/
           (forall l', ldi l' l -> exists s2, stepr src s1 l' s2 /\ 
                                  fsr s2 t5))).
Proof.
  set (ltauseq := @ltaustar_eq _ _ target_determinate).
  intros t1 t2 TSt1t2.
  induction TSt1t2 as [t1 | t1 t2 t3 STt1t2 TSt2t3 IH].
  (* Base case *)
  intros t4 s t l FSst TSt1t STt1t3 Lntau. 
  pose proof (@ltaustar_eq _ _ target_determinate _ _ _ _ STt1t3 Lntau TSt1t) as Eq_t1_t.
  rewrite <- Eq_t1_t in *.
  (* Force one step through forward_progress *)
  destruct (@forward_progress_with_undef _ _ FSst) as [Stuck |
    [sm [tm [t' [l' [TSssm [TStm [FSstm [WStmt' Cases]]]]]]]]].
  (* if stuck, it is trivial *)    
  by vauto. 
  (* otherwise do case analysis on l' being tau *)
  destruct (lbl_dec lbl l' (tau lbl)) as [Ltau' | Lntau'].
    rewrite Ltau' in *.

    destruct (weaksteptau_decomp (taustar_weakstep TStm WStmt')) as [it [STit _]].
    elim Lntau. apply tau_1_kind.
    apply (proj1 (target_determinate _ _ _ _ _ STt1t3 STit)).

    assert (WSt1_to_TSt4: forall tx, weakstep _ t1 l tx -> taustar _ t4 tx).
      intros tx WStx. destruct WStx as [tx1 [tx2 [TSt1tx1 [STtx1tx2 TStx2tx]]]].
      rewrite <- (ltauseq _ _ _ _ STt1t3 Lntau TSt1tx1) in STtx1tx2.
      by rewrite <- (proj2 (target_determinate _ _ _ _ _ STt1t3 STtx1tx2) 
        (refl_equal l)) in TStx2tx. 

    pose proof WStmt' as WStmtp.
    destruct (WStmt') as [t5 [t6 [TSt1t5 [STt5t6 TSt6t']]]]. 
    pose proof (ltauseq _ _ _ _ STt1t3 Lntau TStm) as t1_eq_tm. 
    rewrite <- t1_eq_tm in *.
    pose proof (ltauseq _ _ _ _ STt1t3 Lntau TSt1t5) as t1_eq_t5. 
    rewrite <- t1_eq_t5 in *.
    pose proof (proj1 (target_determinate _ _ _ _ _ STt1t3 STt5t6)) as SK.
    destruct Cases as [[lp [s' [Ldo [STsms' FSstp]]]] | LDI].
    (* LDO case. easier, but tedious. *)
    right. exists sm. exists t'.
    rewrite (@ldo_samekind_eq _ _ _ SK Ldo) in *.
    rewrite <- (proj2 (target_determinate _ _ _ _ _ STt1t3 STt5t6) 
      (refl_equal l')) in *. 
    repeat split; try assumption; try apply taustar_refl.
    left. exists lp. exists s'.  repeat split; try assumption.
    (* LDI case. *)
    destruct (LDI _ (ldi_refl l')) as [s'' [STsmlpspp FSspptp]].
    destruct (source_receptive _ _ _ _ STsmlpspp SK) as [s2 STsms2].
    destruct fsim as [_ FS].
    destruct (FS sm t1 l s2 STsms2 FSstm) as
      [Err | 
       [[Ltau [FS' FSCss]] |
        [t2 [[l2p [LDO2 [WSlp2 FSs2t2]]] | [WSt1lt2 LDI2]]]]]; clear FS.
    eby left; eapply ev_stuck_or_error_taustar.
    contradiction.
    assert (L2pntau: l2p <> tau _). intro L2ptau. rewrite L2ptau in *.
      apply ldo_not_tau in LDO2. assumption.
    pose proof (@ldo_samekind_eq _ _ _
      (@weakstep_samekind _ _ _ _ _ Lntau' L2pntau WStmtp WSlp2) LDO2) as Eq_lp_l2p.
    rewrite <- Eq_lp_l2p in *.
    pose proof (@ldo_samekind_eq _ _ _ SK LDO2) as Eq_l_lp. rewrite <- Eq_l_lp in *.
    right. exists sm. exists t2.
    rewrite <- (proj2 (target_determinate _ _ _ _ _ STt1t3 STt5t6) 
      (refl_equal l)) in *.
    repeat split. assumption. apply (WSt1_to_TSt4 _ WSlp2).
    left. exists l. exists s2.  repeat split; try assumption.
    right. exists sm. exists t2.
    repeat split. assumption. apply (WSt1_to_TSt4 _ WSt1lt2).
    right. assumption.

  (* Induction step is quite similar to the base case *)
  intros t4 s t l FSst TSt1t STt1t3 Lntau. 
  (* Force one step through forward_progress *)
  destruct (@forward_progress_with_undef _ _ FSst) as [Stuck |
    [sm [tm [t' [l' [TSssm [TStm [FSstm [WStmt' Cases]]]]]]]]].
  (* if stuck, it is trivial *)    
  by vauto. 
  (* otherwise do case analysis on l' being tau *)
  destruct (lbl_dec lbl l' (tau lbl)) as [Ltau' | Lntau'].
    (* l' = tau case *)
    rewrite Ltau' in *.
    (* Here we differ from the base case -> we go to the induction hypothesis *)
    destruct (weaksteptau_decomp (taustar_weakstep TSt1t (taustar_weakstep TStm WStmt')))  
      as [it [STit TSit]].
    rewrite (proj2 (target_determinate _ _ _ _ _ STt1t2 STit) 
                   (refl_equal (tau lbl))) in *.
    destruct Cases as [[lp [sp [LDO _]]] | WStmtp].
    apply ldo_not_tau in LDO. contradiction.
    destruct (WStmtp (tau _) (ldi_refl _)) as [s' [STsms' FSst']].
    specialize (IH t4 s' t' l FSst' TSit STt1t3 Lntau).
    destruct IH as [Stuck | [sp1 [tp1 [TSsp1 [TStp1  Cases]]]]].
    (* Stuck case *)
    left; eapply ev_stuck_or_error_taustar, Stuck.
    exact (taustar_trans TSssm (taustar_step STsms' (taustar_refl _ _))).
    (* Step case *)
    right. exists sp1. exists tp1. 
    repeat split; try assumption. 
    exact (taustar_trans TSssm (taustar_step STsms' TSsp1)).

    (* l' is not tau *)  
    pose proof WStmt' as WStmtp.
    destruct WStmt' as [t5 [t6 [TStmt5 [STt5t6 TSt6t']]]].
    pose proof (taustar_step STt1t2 TSt2t3) as TSt1t3.
    pose proof (taustar_trans TSt1t (taustar_trans TStm TStmt5)) as TSt1t5.
    pose proof (proj1 (@taustar_labels _ _ target_determinate _ _ _ _ _ _ _
       Lntau Lntau' TSt1t3 STt1t3 TSt1t5 STt5t6)) as t3_eq_t5.
    rewrite t3_eq_t5 in *.
    pose proof (proj1 (target_determinate _ _ _ _ _ STt1t3 STt5t6)) as SK.
    (* Now the same gymnastics as in the base case *)

    destruct Cases as [[lp [s' [Ldo [STsms' FSstp]]]] | LDI].
    (* LDO case. easier, but tedious. *)
    right. exists sm. exists t'.
    rewrite (@ldo_samekind_eq _ _ _ SK Ldo) in *.
    rewrite <- (proj2 (target_determinate _ _ _ _ _ STt1t3 STt5t6) 
      (refl_equal l')) in *. 
    repeat split; try assumption; try apply taustar_refl.
    left. exists lp. exists s'.  repeat split; try assumption.
    (* LDI case. *)
    destruct (LDI _ (ldi_refl l')) as [s'' [STsmlpspp FSspptp]].
    destruct (source_receptive _ _ _ _ STsmlpspp SK) as [s2 STsms2].
    destruct fsim as [_ FS].
    destruct (FS sm tm l s2 STsms2 FSstm) as
      [Err | 
       [[Ltau [FS' FSCss]] |
        [t2p [[l2p [LDO2 [WSlp2 FSs2t2]]] | [WSt1lt2 LDI2]]]]]; clear FS.
    eby left; eapply ev_stuck_or_error_taustar. 
    contradiction.
    assert (L2pntau: l2p <> tau _). intro L2ptau. rewrite L2ptau in *.
      apply ldo_not_tau in LDO2. assumption.
    pose proof (@ldo_samekind_eq _ _ _
      (@weakstep_samekind _ _ _ _ _ Lntau' L2pntau WStmtp WSlp2) LDO2) as Eq_lp_l2p.
    rewrite <- Eq_lp_l2p in *.
    pose proof (@ldo_samekind_eq _ _ _ SK LDO2) as Eq_l_lp. rewrite <- Eq_l_lp in *.
    right. exists sm. exists t'.
    rewrite <- (proj2 (target_determinate _ _ _ _ _ STt1t3 STt5t6) 
      (refl_equal l)) in *.
    repeat split; try done; try apply taustar_refl. (* apply (WSt1_to_TSt4 _ WSlp2). *)
    by right.
    right. exists sm. exists t2p.
    repeat split. assumption. 
    destruct WSt1lt2 as [tmx [tmy [TStmtmx [STtmxtmy TStmyt2p]]]].
    by rewrite (proj2 (proj2 (@taustar_labels _ _ target_determinate _ _ _ _ _ _ _ 
      Lntau Lntau TStmtmx STtmxtmy TStmt5 STt1t3)) (refl_equal l)) in TStmyt2p.
    by right. 
Qed.

(* Cleaner formulation of the previous lemma: *)
Lemma sourcesim_nontau_with_undefs:
  forall s t t1 t2 l, 
    fsr s t ->
    l <> tau lbl ->
    taustar tgt t t1 ->
    stepr tgt t1 l t2 ->
    ev_stuck_or_error _ s \/
    (exists s1, exists t',
      taustar src s s1 /\ taustar tgt t2 t' /\
      ((exists l', exists s', ldo l' l /\ stepr src s1 l' s' /\ 
                                  fsr s' t') \/
      (forall l', ldi l' l -> exists s', stepr src s1 l' s' /\ 
                                  fsr s' t'))).
Proof.
  eauto using forward_progress_nontau_aux_with_undef, taustar_refl.
Qed.

(* The following two lemmata are useful for simulating stuck states *)
Lemma taustar_stuck_sim_with_undefs:
  forall s t ts,
    fsr s ts ->
    taustar tgt t ts ->
    stuck tgt t ->
    ev_stuck_or_error _ s.
Proof.
  intros s t ts FS TS Stuck.
  destruct (@forward_progress_with_undef _ _ FS) as [Stuck' | 
    [sm [tm [tp [l [TSssm [TSttm [FSsmtm [WStm _]]]]]]]]].  
  assumption.
  byContradiction.
  exact (weakstep_not_stuck (taustar_weakstep (taustar_trans TS TSttm)  WStm) 
                            Stuck).
Qed.

Lemma taustar_stuck_sim2_with_undef:
  forall t t',
    taustar tgt t t' ->
    forall s ts,
      fsr s ts ->
      taustar tgt t ts ->
      stuck tgt t' ->
      ev_stuck_or_error _ s.
Proof.
  intros t t' TStt'.
  induction TStt' as [t | t t1 t2 ST TS IH].
  (* Base case *)
  intros s ts FS TSts Stuck.
  exact (@taustar_stuck_sim_with_undefs _ _ _ FS TSts Stuck).
  
  (* Induction step *)  
  intros s ts FS TSts Stuck.
  destruct TSts as [t | t t3 ts STtt3 TSt3t4].
  (* We have run out of taus before the simulation, so 
     we have to force progress *) 
  destruct (@forward_progress_with_undef _ _ FS) as [Stuck' | 
    [sm [tm [tp [l [TSssm [TSttm [FSsmtm [WStmtp 
      [[lp [sp [LDO [STsmsp FSsptp]]]] | LDI]]]]]]]]]].
  (* Stuck case *)  
  assumption. 
  (* ldo case *)
  destruct (lbl_dec lbl l (tau lbl)) as [Ltau | Lntau].
  rewrite Ltau in *.
  apply ldo_not_tau in LDO. contradiction.
  pose proof (@lweaktaustar _ _ target_determinate _ _ _ _ 
    (taustar_weakstep TSttm WStmtp) 
    Lntau (taustar_step ST TS)) as WSt2tp.
  byContradiction. exact (weakstep_not_stuck WSt2tp Stuck).
  (* ldi case *)
  destruct (LDI _ (ldi_refl _)) as [spp [STsmspp FSspptp]].
  destruct (lbl_dec lbl l (tau lbl)) as [Ltau | Lntau].
  rewrite Ltau in *.
  destruct (weaksteptau_decomp (taustar_weakstep TSttm WStmtp))
    as [ti [STtau TSti]].
  pose proof (proj2 (target_determinate _ _ _ _ _ ST STtau) 
      (refl_equal (tau lbl))) as t1_eq_ti; rewrite <- t1_eq_ti in *.
  eapply ev_stuck_or_error_taustar, (IH _ _ FSspptp TSti Stuck).
  exact (taustar_trans TSssm (taustar_step STsmspp (taustar_refl _ _))).
  pose proof (@lweaktaustar _ _ target_determinate _ _ _ _ 
    (taustar_weakstep TSttm WStmtp) 
    Lntau (taustar_step ST TS)) as WSt2tp.
  byContradiction. exact (weakstep_not_stuck WSt2tp Stuck).
  (* We have one step, so we just go to the IH *)
  pose proof (proj2 (target_determinate _ _ _ _ _ ST STtt3) 
      (refl_equal (tau lbl))) as t1_eq_t3; rewrite <- t1_eq_t3 in *.
  exact (IH _ _ FS TSt3t4 Stuck).
Qed.



(** The main result: bsr and bsc are backward simulation with undefs. *)
Theorem forward_to_backward_sim_with_undefs:
  backward_sim_with_undefs (@bsr _ _ _ fsr) (@bsc _ _).
Proof.
  split.
  (* Well-foundedness *)
  exact (@bsc_wf _ _ target_determinate).

  split. (* Stuck state correspondence *)
  intros s t TStuck BSt. destruct BSt as [t' [FSst' TR]].
  destruct TR as [TSttp | TStpt].
  exact (@taustar_stuck_sim_with_undefs _ _ _ FSst' TSttp TStuck).
  exact (@taustar_stuck_sim2_with_undef _ _ TStpt _ _ 
    FSst' (taustar_refl _ t') TStuck).
  
  (* The bulk of the proof is establishing the simulation diagram: *)
  intros s t l t' STtt' BS.
  destruct BS as [t'' [FS TRttpp]].
  destruct (lbl_dec lbl l (tau lbl)) as [Ltau | Lntau].
  (* Case l = tau *)
      rewrite Ltau in *; clear Ltau l.
      (* Force progress *)
      destruct (@forward_progress_with_undef _ _ FS) as [Stuck | 
        [sm [tm [t1 [l [TSssm [TSttm [FSsmtm [WStmt1 
          [[lp [sp [LDO [STsmsp FSspt1]]]] | LDI]]]]]]]]]].
      (* Stuck case is easy *)
      tauto.
      (* ldo case *)
      apply taureach_sym in TRttpp.
      pose proof (taureach_sym (@taureach_taustar_taureach _ _ target_determinate
        _ _ _ TRttpp (steptau_taustar _ _ _ STtt'))) as TRtptpp.
      (* pose proof (taureach_taustar_taureach _ _ _ TRttpp TStm) as TRttm.  *)
      destruct (lbl_dec lbl l (tau lbl)) as [Ltau | Lntau].
      rewrite Ltau in *; clear Ltau l. 
      apply ldo_not_tau in LDO. contradiction.
      pose proof (@lweakbothtep _ _ target_determinate  
        _ _ _ _ TRtptpp Lntau (taustar_weakstep TSttm WStmt1))
        as WStpt1.
      left. split. reflexivity.
      split. exists t''. split; assumption.
      exact (@stau_ws_impl_order _ _ _ _ _ _ STtt' WStpt1 Lntau). 
      (* ldi case *)
      apply taureach_sym in TRttpp.
      pose proof (taureach_sym (@taureach_taustar_taureach _ _ target_determinate
        _ _ _ TRttpp (steptau_taustar _ _ _ STtt'))) as TRtptpp.
      destruct (lbl_dec lbl l (tau lbl)) as [Ltau | Lntau].
      rewrite Ltau in *; clear Ltau l.
      right. right. right. intros l'' LDI2. 
      destruct (LDI _ LDI2) as [s'' [STsmspp FSsppt1]].
      exists s''. split.
      by exists sm. 
      exists t1. split. assumption.
      exact (@taureach_taustar_taureach _ _ target_determinate _ _ _ TRtptpp  
        (weaksteptau_taustar (taustar_weakstep TSttm WStmt1))).
      pose proof (@lweakbothtep _ _ target_determinate
        _ _ _ _ TRtptpp Lntau (taustar_weakstep TSttm WStmt1)) as WStpt1.
      left; split. reflexivity.
      split. exists t''. split; assumption. 
      exact (@stau_ws_impl_order _ _ _ _ _ _ STtt' WStpt1 Lntau). 
  (* Case l <> tau *)
      assert (TStppt: taustar tgt t'' t).  
      destruct TRttpp as [TS | TS].
      rewrite (@ltaustar_eq _ _ target_determinate
        _ _ _ _ STtt' Lntau TS); apply taustar_refl.
      assumption.
      destruct (@sourcesim_nontau_with_undefs s t'' t t' l FS Lntau TStppt STtt')
        as [Stuck | [s1 [t1 [TSss1 [TStpt1 
          [[lp [s2 [LDO [STs1s2 FS2]]]] | LDI]]]]]].
      (* Stuck case *)
      tauto. 
      (* LDO *)
      right. right. left. exists s2. exists lp. split. assumption.
      split. eby eexists. 
      by eexists; vauto. 
      (* LDI *)
      right; right; right. intros l'' LDI2.
      destruct (LDI _ LDI2) as [s2 [STs1s2 FSs2t1]].
      exists s2. 
      split. by exists s1. 
      by exists t1; vauto. 
Qed.

End ForwardToBackwardSim.

End ForwardToBackwardUndefSim.

(** * Simpler interface to per-thread forward simulation *)

Section ForwardThreadEventUndefSim.

  Variable src tgt : lts thread_labels.

  Variable r : St src -> St tgt -> Prop.
  Variable c : St src -> St src -> Prop.
 
  Definition forward_sim_with_undefs2 :=  
     forall s t l s', 
       stepr _ s l s' -> r s t ->
         (ev_stuck_or_error _ s) \/
         (match l with
            | TEmem (MEread p c v) =>
                (exists t', weakstep tgt t (TEmem (MEread p c v)) t' 
                  /\ forall v', Val.lessdef v' v -> exists s'', 
                    stepr _ s (TEmem (MEread p c v')) s'' /\ r s'' t')
            | TEmem (MErmw p c v f) =>
                (exists t', weakstep tgt t (TEmem (MErmw p c v f)) t' 
                  /\ forall v', Val.lessdef v' v -> exists s'', 
                    stepr _ s (TEmem (MErmw p c v' f)) s'' /\ r s'' t')
            | TEtau => (c s' s /\ r s' t) \/ (exists t', weakstep tgt t TEtau t' /\ r s' t')
            | TEmem (MEwrite p c v) =>
                   (exists t', exists v', Val.lessdef v v'
                       /\ weakstep tgt t (TEmem (MEwrite p c v')) t' /\ r s' t')
            | TEstart p v =>
                   (exists t', exists v', Val.lessdef_list v v'
                       /\ weakstep tgt t (TEstart p v') t' /\ r s' t')
            | TEstartmem p v =>
                   (exists t', exists v', Val.lessdef_listsum v v'
                       /\ weakstep tgt t (TEstartmem p v') t' /\ r s' t')
            | _ =>  (exists t', weakstep tgt t l t' /\ r s' t')
          end).

  Lemma mk_forward_sim_with_undefs:
    forall 
      (WF: well_founded c)
      (FSIM: forward_sim_with_undefs2),
    @forward_sim_with_undefs thread_labels src tgt te_ldo te_ldi r c.
  Proof.
    split; [done|].
    intros s t l s' H1 H2.
    specialize (FSIM s t l s' H1 H2).
    case FSIM; clear FSIM; intro FSIM; [left; done|right]; simpl.
    (destruct l as [[]|[]| | | | | |]); simpl;
    try
      (by revert FSIM; intros [t' [WS R]];
       right; exists t'; right; split; [apply WS|];
       intros [[]|[]| | | | | |]; try done; simpl; intros; clarify;
         repeat match goal with H: _ /\ _ |- _ => destruct H end; 
           clarify; eauto).  
   Case "MEwrite".
   revert FSIM; intros [t' [v' [? [? ?]]]].
   eby right; exists t'; left; eexists (TEmem (MEwrite _ _ v')); repeat split. 
   Case "TEtau".
   destruct FSIM as [[? ?]|[t' [? ?]]]; [left; done|].
   right; exists t'; right; split; [done|].
   eby intros [[]|[]| | | | | |]; try done; simpl; intros; clarify; eexists.
   Case "TEstart".
   revert FSIM; intros [t' [v' [? [? ?]]]].
   eby right; exists t'; left; eexists (TEstart _ v'); repeat split. 
   Case "TEstartmem".
   revert FSIM; intros [t' [v' [? [? ?]]]].
   eby right; exists t'; left; eexists (TEstartmem _ v'); repeat split. 
  Qed. 

End ForwardThreadEventUndefSim.
