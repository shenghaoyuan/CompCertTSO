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
Require Import Integers.
Require Import Values.
Require Import Pointers.
Require Import Events.
Require Import Mem.
Require Import Memaux.
Require Import Memeq.
Require Import Ast.
Require Import Globalenvs.
Require Import Maps.
Require Import Simulations.
Require Import Classical.
Require Import Libtactics.

(** * Interface for thread semantics *)

Structure SEM := mkSEM 
  {
    SEM_ST : Type ;
    SEM_GE : Type ;
    SEM_PRG : Type ;
    SEM_ge_init : SEM_PRG -> SEM_GE -> mem -> Prop ;
    SEM_main_fn_id : SEM_PRG -> ident ;
    SEM_find_symbol : SEM_GE -> ident -> option pointer ;
    SEM_step : SEM_GE -> SEM_ST -> thread_event -> SEM_ST -> Prop ;
    SEM_init : SEM_GE -> pointer -> list val -> option SEM_ST ;
    SEM_progress_dec :
      forall ge s, (forall s' l', ~ SEM_step ge s l' s') \/
        (exists l', exists s', SEM_step ge s l' s') ;
    SEM_receptive : 
      forall ge, receptive (mklts thread_labels (SEM_step ge));
    SEM_determinate :
      forall ge, determinate (mklts thread_labels (SEM_step ge))
  }.

(** * Interface for memory model semantics *)


Structure MM := mkMM 
  {
    MM_ST : Type ;
    MM_step : MM_ST -> mm_event -> MM_ST -> Prop ;
    MM_init : mem -> MM_ST ;
    MM_inv : PTree.t unit -> MM_ST -> Prop ;
    MM_inv_init : 
      forall m tid, 
        MM_inv ((PTree.empty _) ! tid <- tt) (MM_init m) ;
    MM_inv_step :
      forall s ev s' 
        (STEP: MM_step s ev s') a
        (INV: MM_inv a s) a'
        (OTH: match ev with
              | MMmem tid' _        
              | MMreadfail tid' _ _ 
              | MMfreefail tid' _ _ 
              | MMoutofmem tid' _ _ => a' = a /\ a ! tid' = Some tt
              | MMtau               => a' = a
              | MMstart t1 t2       => a' = a ! t2 <- tt /\ a ! t1 = Some tt 
              | MMexit tid'         => a' = PTree.remove tid' a /\ a ! tid' = Some tt
              end),
        MM_inv a' s' ;
    MM_no_threads_stuck :
      forall s 
        (INV: MM_inv (PTree.empty _) s) s'
        (STEP: MM_step s MMtau s'),
        False ;
    MM_can_move:
      forall a s
        (INV: MM_inv a s) e, 
        match e with
          | MMmem tid (MEread p c v) =>
            exists s', 
              (exists v', taustep (mklts mm_event_labels MM_step) s (MMmem tid (MEread p c v')) s' /\
                 samekind thread_labels (TEmem (MEread p c v')) (TEmem (MEread p c v))) \/
               taustep (mklts mm_event_labels MM_step) s (MMreadfail tid p c) s'
          | MMmem tid (MEwrite p c v) =>
            exists s', 
              taustep (mklts mm_event_labels MM_step) s (MMmem tid (MEwrite p c v)) s' \/
              taustep (mklts mm_event_labels MM_step) s (MMreadfail tid p c) s'
          | MMmem tid (MErmw p c v f) =>
            exists s', 
              (exists v', taustep (mklts mm_event_labels MM_step) s (MMmem tid (MErmw p c v' f)) s' /\
                 samekind thread_labels (TEmem (MErmw p c v' f)) (TEmem (MErmw p c v f))) \/
              taustep (mklts mm_event_labels MM_step)  s (MMreadfail tid p c) s'
          | MMmem tid (MEfree p k) =>
            exists s', 
              taustep (mklts mm_event_labels MM_step) s e s' \/
              taustep (mklts mm_event_labels MM_step) s (MMfreefail tid p k) s'
          | MMmem tid (MEalloc p i k) =>
            exists s', 
              (exists p', taustep (mklts mm_event_labels MM_step) s (MMmem tid (MEalloc p' i k)) s') \/
              taustep (mklts mm_event_labels MM_step) s (MMoutofmem tid i k) s'
          | MMmem _ MEfence 
          | MMstart _ _
          | MMexit _ => exists s', taustep (mklts mm_event_labels MM_step) s e s'
          | _ => True
        end ;
    MM_fence_tau :
      forall s tid s' 
        (STEP: MM_step s (MMmem tid MEfence) s'),
        s' = s
  }.


Definition MM_pure_load_condition (Mm: MM) :=
  forall a s (INV: MM_inv Mm a s) tid p c,
    (exists v, MM_step Mm s (MMmem tid (MEread p c v)) s 
              /\ Val.has_type v (type_of_chunk c)) \/
    (exists s', taustep (mklts mm_event_labels (MM_step Mm)) s (MMreadfail tid p c) s').


(** * Composition semantics *)

Module Comp.

(* must be defined outside of the section *)
Definition consistent (Mm: MM) (Sem: SEM) (s : MM_ST Mm * PTree.t (SEM_ST Sem)) : Prop :=
  match tt with tt => MM_inv Mm (PTree.map (fun _ _ => tt) (snd s)) (fst s) end.

Section MMsemantics.

(** NB: The composition semantics is parametric w.r.t. the memory
  model and the thread semantics. *)
Variables (Mm : MM) (Sem : SEM).

Notation mm_state := (MM_ST Mm).
Notation mm_step := (MM_step Mm).

Notation ST := (SEM_ST Sem).
Notation Sem_step := (SEM_step Sem).
Notation consistent := (consistent Mm Sem).

(** State of the overall system consists of a state of the
    TSO machine and states of individual threads. *)
Definition state : Type := (mm_state * PTree.t ST) % type.

(** Predicate [init p args ge lts] is satisfied if
   [lts] is the initial state of the parallel composition for the program [p]
   with [args] being the arguments to its main function, and [ge] is the 
   global environment for the program. *)
Definition init (p : Sem.(SEM_PRG)) (main_args : list val)
                (*bl : mem_restr*) (ge : Sem.(SEM_GE)) (lts : state) : Prop :=
  exists mainst, exists maintid, exists initmem, exists main_ptr,
    Sem.(SEM_ge_init) p ge (*bl*) initmem /\
    Sem.(SEM_find_symbol) ge (Sem.(SEM_main_fn_id) p) = Some main_ptr /\
    Sem.(SEM_init) ge main_ptr main_args = Some mainst /\
    lts = (Mm.(MM_init) initmem, (PTree.empty _) ! maintid <- mainst).

Section MMstep.

Variable (ge : Sem.(SEM_GE)).

(** [mm_arglist tso t locs vals tso'] holds if in state [tso], reading values [vals]
    from locations [locs] in thread [t] results in state [tso']. *)
Inductive mm_arglist (tso: mm_state) (t: thread_id) :
    list (pointer * memory_chunk + val) -> list val -> mm_state -> Prop :=
| mm_arglist_refl: 
    mm_arglist tso t nil nil tso
| mm_arglist_val:  forall locs vals tso' v
    (MA: mm_arglist tso t locs vals tso'),
    mm_arglist tso t (inr (pointer * memory_chunk) v :: locs) (v :: vals) tso'
| mm_arglist_read: forall p c v tso' locs vals tso''
    (RD : mm_step tso (MMmem t (MEread p c v)) tso')
    (MA: mm_arglist tso' t locs vals tso''),
    mm_arglist tso t (inl val (p, c) :: locs) (v :: vals) tso''.

Inductive mm_ext_arglist (tso: mm_state) (t: thread_id) :
    list (pointer * memory_chunk + eventval) -> list eventval -> mm_state -> Prop :=
| mm_ext_arglist_refl:
    mm_ext_arglist tso t nil nil tso
| mm_ext_arglist_val:  forall locs vals tso' v
    (MA: mm_ext_arglist tso t locs vals tso'),
    mm_ext_arglist tso t (inr (pointer * memory_chunk) v :: locs) (v :: vals) tso'
| mm_ext_arglist_read: forall p c v tso' locs vals tso'' ev
    (RD : mm_step tso (MMmem t (MEread p c v)) tso')
    (EV : val_of_eval ev = v)
    (MA: mm_ext_arglist tso' t locs vals tso''),
    mm_ext_arglist tso t (inl eventval (p, c) :: locs) (ev :: vals) tso''.

(** [mm_arglist_fail tso t locs] holds if in state [tso], reading values from 
    locations [loc] in thread [t] can lead to an error 
    (reading from unallocated or unaligned memory). *)
Inductive mm_arglist_fail (tso: mm_state) (t: thread_id) :
    list (pointer * memory_chunk + val) -> Prop :=
| mm_arglist_fail_err: forall tso' p c rest
    (TST: mm_step tso (MMreadfail t p c) tso'),
    mm_arglist_fail tso t (inl val (p, c) :: rest)
| mm_arglist_fail_val:  forall locs v
    (MA: mm_arglist_fail tso t locs),
    mm_arglist_fail tso t (inr (pointer * memory_chunk) v :: locs)
| mm_arglist_fail_read: forall p c v tso' locs
    (RD : mm_step tso (MMmem t (MEread p c v)) tso')
    (MA: mm_arglist_fail tso' t locs),
    mm_arglist_fail tso t (inl val (p, c) :: locs).

Inductive mm_ext_arglist_fail (tso: mm_state) (t: thread_id) :
    list (pointer * memory_chunk + eventval) -> Prop :=
| mm_ext_arglist_fail_rerr: forall tso' p c rest
    (TST : mm_step tso (MMreadfail t p c) tso'),
    mm_ext_arglist_fail tso t (inl eventval (p, c) :: rest)
| mm_ext_arglist_fail_everr: forall tso' p c rest v
    (TST : mm_step tso (MMmem t (MEread p c v)) tso')
    (NVOE : forall ev, val_of_eval ev <> v),
    mm_ext_arglist_fail tso t (inl eventval (p, c) :: rest)
| mm_ext_arglist_fail_val:  forall locs v
    (MA: mm_ext_arglist_fail tso t locs),
    mm_ext_arglist_fail tso t (inr (pointer * memory_chunk) v :: locs)
| mm_ext_arglist_fail_read: forall p c v tso' locs
    (RD : mm_step tso (MMmem t (MEread p c v)) tso')
    (MA: mm_ext_arglist_fail tso' t locs),
    mm_ext_arglist_fail tso t (inl eventval (p, c) :: locs).

(** [step] is a step relation for the entire process (parallel
    composition of the TSO machine with threads.  Note that the
    silent transition is represented by None. *)

Inductive step : state -> fullevent -> state -> Prop :=
  | step_ord: (* Ordinary memory events synchronize with the TSO machine *)
    forall s s' ev tid tso tso' st st'
      (tidSTEP: Sem_step ge s (TEmem ev) s')
      (tsoSTEP: mm_step tso (MMmem tid ev) tso')
      (Gtid: st ! tid = Some s)
      (EQst': st' = st ! tid <- s'), 
    step (tso, st) Etau (tso', st')
  | step_ext: (* External event *)
    forall s s' ev tso st st' tid
      (tidSTEP: Sem_step ge s (TEext ev) s')
      (Gtid: st ! tid = Some s)
      (EQst': st' = st ! tid <- s'),
    step (tso, st) (Evisible ev) (tso, st')
  | step_unbuf: (* Memory model tau action *)
    forall tso tso' st
      (tsoSTEP: mm_step tso MMtau tso'),
    step (tso, st) Etau (tso', st)
  | step_tau: (* Thread tau action *)
    forall s s' tid tso st st'
      (tidSTEP: Sem_step ge s TEtau s')
      (Gtid: st ! tid = Some s)
      (EQst': st' = st ! tid <- s'),
    step (tso, st) Etau (tso, st')
  | step_start: (* Thread start action *)
    forall s s' newtid p v tid tso tso' st st' sinit
      (tidSTEP: Sem_step ge s (TEstart p v) s')
      (tsoSTEP: mm_step tso (MMstart tid newtid) tso')
      (Gtid: st ! tid = Some s)
      (Gnewtid: st ! newtid = None)
      (EQst': st' = (st ! tid <- s') ! newtid <- sinit)
      (INIT: Sem.(SEM_init) ge p v = Some sinit),
    step (tso, st) Etau (tso', st')
  (* Thread spawn fails - init state creation fails
     (for example, if the function pointer is bogus,
      or the number of arguments is invalid) *)
  | step_start_fail: forall s s' p v tid tso st
      (tidSTEP: Sem_step ge s (TEstart p v) s')
      (Gtid: st ! tid = Some s)
      (INIT: Sem.(SEM_init) ge p v = None),
    step (tso, st) (Evisible Efail) (tso, st ! tid <- s')
  | step_exit: (* Thread exit action *)
    forall s s' tid tso tso' st
      (tidSTEP: Sem_step ge s TEexit s')
      (tsoSTEP: mm_step tso (MMexit tid) tso')
      (Gtid: st ! tid = Some s),
    step (tso, st) Etau (tso', PTree.remove tid st)
  | step_read_fail: (* Read memory error *)
    forall s s' tid tso tso' st st' p c v
      (tidSTEP: Sem_step ge s (TEmem (MEread p c v)) s')
      (tsoSTEP: mm_step tso (MMreadfail tid p c) tso')
      (Gtid: st ! tid = Some s)
      (EQst': st' = st ! tid <- s'),
    step (tso, st) (Evisible Efail) (tso', st')
  | step_write_fail: (* Write memory error *)
    forall s s' tid tso tso' st st' p c v
      (tidSTEP: Sem_step ge s (TEmem (MEwrite p c v)) s')
      (tsoSTEP: mm_step tso (MMreadfail tid p c) tso')
      (Gtid: st ! tid = Some s)
      (EQst': st' = st ! tid <- s'),
    step (tso, st) (Evisible Efail) (tso', st')
  | step_free_fail: (* Deallocation memory error *)
    forall s s' tid tso tso' st st' p k
      (tidSTEP: Sem_step ge s (TEmem (MEfree p k)) s')
      (tsoSTEP: mm_step tso (MMfreefail tid p k) tso')
      (Gtid: st ! tid = Some s)
      (EQst': st' = st ! tid <- s'),
    step (tso, st) (Evisible Efail) (tso, st)
  | step_rmw_fail: (* Read-modify-write memory error *)
    forall s s' tid tso tso' st st' p c v instr
      (tidSTEP: Sem_step ge s (TEmem (MErmw p c v instr)) s')
      (tsoSTEP: mm_step tso (MMreadfail tid p c) tso')
      (Gtid: st ! tid = Some s)
      (EQst': st' = st ! tid <- s'), 
    step (tso, st) (Evisible Efail) (tso', st')
  | step_thread_stuck: (* Thread error *)
    forall s tid tso st
      (NOtidSTEP: forall s' l', ~ Sem_step ge s l' s')
      (Gtid: st ! tid = Some s),
    step (tso, st) (Evisible Efail) (tso, st)
  | step_alloc_out_of_memory:
    forall s s' tid tso tso' st st' p n k
      (tidSTEP: Sem_step ge s (TEmem (MEalloc p n k)) s')
      (tsoSTEP: mm_step tso (MMoutofmem tid n k) tso')
      (Gtid: st ! tid = Some s)
      (EQst': st' = st ! tid <- s'),
    step (tso, st) (Eoutofmemory) (tso', st')
  | step_thread_out_of_memory:
    forall s s' tid tso st st' 
      (tidSTEP: Sem_step ge s TEoutofmem s')
      (Gtid: st ! tid = Some s)
      (EQst': st' = st ! tid <- s'),
    step (tso, st) (Eoutofmemory) (tso, st')
  | step_extcallmem:
    forall s s' largs args tid tso tso' st st' id
      (tidSTEP: Sem_step ge s (TEexternalcallmem id largs) s')
      (tsoSTEP: mm_ext_arglist tso tid largs args tso')
      (Gtid: st ! tid = Some s)
      (EQst': st' = st ! tid <- s'),
    step (tso, st) (Evisible (Ecall id args)) (tso', st')
  | step_extcallmem_fail:
    forall s s' largs tid tso st st' id
      (tidSTEP: Sem_step ge s (TEexternalcallmem id largs) s')
      (tsoSTEP: mm_ext_arglist_fail tso tid largs)
      (Gtid: st ! tid = Some s)
      (EQst': st' = st ! tid <- s'),
    step (tso, st) (Evisible Efail) (tso, st')
  | step_startmem:
    forall s s' args tid tso tso' tso'' st st' v sinit newtid fn p
      (tidSTEP: Sem_step ge s (TEstartmem fn args) s')
      (tsoSTEP: mm_arglist tso tid (fn::args) ((Vptr p)::v) tso')
      (tsoSTEP2: mm_step tso' (MMstart tid newtid) tso'')
      (Gtid: st ! tid = Some s)
      (Gnewtid: st ! newtid = None)
      (EQst': st' = (st ! tid <- s') ! newtid <- sinit)
      (INIT: Sem.(SEM_init) ge p v = Some sinit),
    step (tso, st) Etau (tso'', st')
  | step_startmem_read_fail:
    forall s s' args tid tso st st' fn 
      (tidSTEP: Sem_step ge s (TEstartmem fn args) s')
      (tsoSTEP: mm_arglist_fail tso tid (fn::args))
      (Gtid: st ! tid = Some s)
      (EQst': st' = (st ! tid <- s')),
    step (tso, st) (Evisible Efail) (tso, st')
  | step_startmem_spawn_fail:
    forall s s' tid tso st st' lfn largs fn args tso'
      (tidSTEP: Sem_step ge s (TEstartmem lfn largs) s')
      (tsoSTEP: mm_arglist tso tid (lfn::largs) (fn::args) tso')
      (Gtid: st ! tid = Some s)
      (INIT: match fn with Vptr p => Sem.(SEM_init) ge p args = None 
                         | _ => True end)
      (EQst': st' = (st ! tid <- s')),
    step (tso, st) (Evisible Efail) (tso, st').

Definition step' := step.

(*Definition consistent (s : state) : Prop :=
  MM_inv Mm (PTree.map (fun _ _ => tt) (snd s)) (fst s).
*)

(*  (forall tid, (snd s) ! tid = None -> MM_thread_nalloc Mm (fst s) tid) /\ MM_inv Mm (fst s). *)

Hint Resolve MM_inv_init MM_inv_step.
(*Hint Resolve MM_thread_nalloc_init MM_thread_nalloc_step.*)


Lemma mapempty : 
  forall A B f, PTree.map f (PTree.empty A) = PTree.empty B.
Proof.
  by intros; apply PTree.ext; intros; rewrite PTree.gmap, !PTree.gempty. 
Qed.

Lemma maps : 
  forall A B (f : positive -> A -> B) (m: PTree.t A) k v,
  PTree.map f (m ! k <- v) = (PTree.map f m) ! k <- (f k v).
Proof.
  intros; apply PTree.ext; intro x. 
  rewrite PTree.gmap, !PTree.gsspec, PTree.gmap; destruct peq; clarify.
Qed.

Lemma ext_same:
  forall A m k (v: A), m ! k = Some v -> m ! k <- v = m.
Proof.
  intros; apply PTree.ext; intros; rewrite PTree.gsspec.
  destruct peq; clarify.
Qed.


Lemma init_consistent:
  forall {prg args ge t} (INIT: init prg args ge t),
    consistent t.
Proof. destruct 1; des; clarify; red; simpl; rewrite maps, mapempty; auto. Qed.

Lemma thread_update_preserves_consistency:
  forall m thr
    (CONS: consistent (m, thr)) tid s
    (T: thr ! tid = Some s) s',
    consistent (m, thr ! tid <- s').
Proof.
  red; intros; red in CONS; simpl in *. rewrite maps, ext_same; try done.
  by rewrite PTree.gmap, T.
Qed.

Lemma step_preserves_consistency:
  forall s e s'
    (STEP: step s e s')
    (CONS: consistent s),
    consistent s'.
Proof.
  red; intros; red in CONS; inv STEP; simpl in *; eauto; rewrite ?maps; simpl;
    try (by rewrite ext_same; [|rewrite PTree.gmap, Gtid]);
    try (by eapply MM_inv_step; eauto);
    try by eapply MM_inv_step; eauto; instantiate; simpl;
           rewrite (ext_same _ _ tid); rewrite PTree.gmap, Gtid.

    - eapply MM_inv_step; eauto; instantiate; simpl.
      rewrite PTree.gmap, Gtid; split; auto.
      apply PTree.ext; intros; rewrite PTree.gmap, !PTree.grspec, PTree.gmap.
      by destruct PTree.elt_eq; clarify. 

    - rewrite (ext_same _ _ tid); try by rewrite PTree.gmap, Gtid.
      clear tidSTEP; induction tsoSTEP; eauto. 
      by eapply IHtsoSTEP; eauto; instantiate;
         eapply MM_inv_step; eauto; simpl; rewrite PTree.gmap, Gtid.

    - rewrite (ext_same _ _ tid); try by rewrite PTree.gmap, Gtid.
      eapply MM_inv_step; eauto; try split; eauto; simpl; 
        try by rewrite PTree.gmap, Gtid.
      clear tidSTEP; induction tsoSTEP; eauto. 
      by eapply IHtsoSTEP; eauto; instantiate;
         eapply MM_inv_step; eauto; simpl; rewrite PTree.gmap, Gtid.
Qed.

Hint Resolve step_preserves_consistency.

Lemma taustar_preserves_consistency:
  forall s s',
    taustar (mklts event_labels step) s s' ->
    consistent s ->
    consistent s'.
Proof. induction 1; eauto. Qed.

Hint Resolve taustar_preserves_consistency.

Lemma taustep_preserves_consistency:
  forall s e s',
    taustep (mklts event_labels step) s e s' ->
    consistent s ->
    consistent s'.
Proof. destruct 1; des; eauto. Qed.

Lemma weakstep_preserves_consistency:
  forall s e s',
    weakstep (mklts event_labels step) s e s' ->
    consistent s ->
    consistent s'.
Proof. destruct 1; des; eauto. Qed.




  Lemma ptr_or_not:
    forall v, {p | v = Vptr p} + {match v with Vptr _ => False | _ => True end}.
  Proof. by intros []; vauto. Qed.

(*
  Lemma tso_arglist_dec:
    forall s
      (INV: MM_inv Mm s)
      (STUCK: forall s', ~ MM_step Mm s MMtau s') tid locs, 
      mm_arglist_fail s tid locs \/
      exists vals, exists s', mm_arglist s tid locs vals s'.
  Proof.
    intros; induction locs as [|[[p c]|v] locs IH]; eauto using mm_arglist.
    destruct IH as [IH|[vals [tso' IH]]]; eauto using mm_arglist_fail.

    eapply mm_can_move with (e := MMmem _ (MEread _ _ Vundef)) in STUCK; des.


    - left; eapply mm_arglist_fail_read; try edone; vauto. try edone; econstructor; try edone.

    destruct (load_ptr c tso.(tso_mem) p) as [v|] _eqn : LD; eauto with myhints.
    - left; eapply Comp.mm_arglist_fail_read; try edone; econstructor; try edone.
      by rewrite BE.
    - right; exists (v :: vals); exists tso'.
      eapply Comp.mm_arglist_read; try edone; econstructor; try edone.
      by rewrite BE.
  Qed.

  Lemma val_of_eval_dec:
    forall v,
      {ev | val_of_eval ev = v} + {forall ev, val_of_eval ev <> v}.
  Proof.
    destruct v; try (by right; intros []).
    - by left; exists (EVint i). 
    - by left; exists (EVfloat f). 
  Qed.

  Lemma tso_ext_arglist_dec:
    forall tso t locs
      (BE : tso.(tso_buffers) t = nil), 
      Comp.mm_ext_arglist_fail tso_mm tso t locs \/
      exists vals, exists tso', Comp.mm_ext_arglist tso_mm tso t locs vals tso'.
  Proof.
    intros. 
    induction locs as [|[[p c]|v] locs IH]; eauto with myhints;
      destruct IH as [IH|[vals [tso' IH]]]; eauto with myhints;
      destruct (load_ptr c tso.(tso_mem) p) as [v|] _eqn : LD; eauto with myhints.
    - left; eapply Comp.mm_ext_arglist_fail_read; try edone; econstructor; try edone.
      by rewrite BE.
    - destruct (val_of_eval_dec v) as [[ev VOE]|NVOE].
        right. exists (ev :: vals). exists tso'.
        eapply Comp.mm_ext_arglist_read; try edone. simpl.
        econstructor; try edone. by rewrite BE.
      left.
      eapply Comp.mm_ext_arglist_fail_everr; try edone.
      econstructor; try edone. by rewrite BE.
  Qed.
*)

  Section THREAD_ID_FRESH_DEC.
  (* The following section is just temporary, until 
      we change thread identifiers to integers. *)
    Fixpoint sumlistp (l : list positive) : positive :=
      match l with
        | nil => 1%positive
        | h::t => Pplus h (sumlistp t)
      end.
      
    Lemma sumlistp_greater_than_elems: 
      forall l e (H: In e l), exists x, (e + x = sumlistp l)% positive.
    Proof.
      induction l as [|h  t IH]; intros; [by inv H|].
      apply in_inv in H. destruct H as [H|H]. subst.
      by exists (sumlistp t).
      destruct (IH e H) as [x X].
      exists (Pplus h x). simpl. 
      by rewrite <- X, Pplus_assoc, (Pplus_comm e h), <- Pplus_assoc. 
    Qed.
      
    Lemma fresh_slot_in_map:
      forall (A : Type) (m : @PTree.t A),
        exists e, PTree.get e m = None.
    Proof.
      intros.
      set (w := sumlistp (map (@fst positive A) (PTree.elements m))).
      exists w. 
      destruct (PTree.get w m) as [e|] _eqn : E; try done.
      apply PTree.elements_correct, (in_map (@fst positive A)) in E. 
      destruct (sumlistp_greater_than_elems _ _ E) as [x H]. 
      by pose proof (Pplus_no_neutral w x) as H'; rewrite Pplus_comm in H'.
    Qed.

  End THREAD_ID_FRESH_DEC.

Lemma no_threads_stuck:
  forall l s s'
    (CONS: consistent s)
    (STEP: step s l s'),
    snd s = PTree.empty _ ->
    False.
Proof.
  intros; red in CONS; inv STEP; simpl in *; clarify; simpl in *; 
    rewrite ?PTree.gempty, ?mapempty in *; clarify.
  eby eapply MM_no_threads_stuck.
Qed.

Lemma stuck_imp_no_threads:
  forall s
    (CONS: consistent s)
    (STUCK: forall l' s', ~ step s l' s'),
    snd s = PTree.empty _.
Proof.
  intros; apply PTree.ext; intro t; rewrite PTree.gempty.
  destruct ((snd s) ! t) as [ts|] _eqn: X; clarify.
  destruct s as [s thr].
    destruct (SEM_progress_dec _ ge ts) as [TTSTUCK | [l' [ts' STEP]]].
      eby eelim STUCK; eapply step_thread_stuck.

  (thread_event_cases (destruct l' as [e| m| | |sp sa| | |]) Case);
    try (by eelim STUCK; vauto).
  Case "TEmem". (* case analysis on possible tso machine moves *)
    eapply MM_can_move with (e := MMmem t m) in CONS.
    destruct m; des;
    try (match goal with 
         H: taustep _ _ _ _ |- _ => destruct H as [? [XXX ?]]; inv XXX; try by eelim STUCK; vauto
         end);
    try (by edestruct (SEM_receptive Sem ge); try apply STEP; try (by eelim STUCK; vauto)).

  Case "TEexit".
    eapply MM_can_move with (e := MMexit t) in CONS; eauto.
    des; (match goal with 
         H: taustep _ _ _ _ |- _ => destruct H as [? [XXX ?]]; inv XXX; try by eelim STUCK; vauto
         end).

  Case "TEstart".
    destruct (fresh_slot_in_map _ thr) as [newtid TIDF]. 
    destruct (SEM_init _ ge sp sa) as [ns|] _eqn : INI.
        (* Everything OK - spawn *)
      eapply MM_can_move with (e := MMstart t newtid) in CONS; eauto.
      by des; (match goal with 
         H: taustep _ _ _ _ |- _ => destruct H as [? [XXX ?]]; inv XXX; try by eelim STUCK; vauto
         end).
    (* Init failed *)
    by eelim STUCK; vauto. 

  Case "TEexternalcallmem". admit.

  Case "TEstartmem". admit.
Qed.

(*
    Case "TEexternalcallmem".
      destruct (tso_ext_arglist_dec tso t l Ebft) as [FAIL | [ev [tso' MA]]].
      - eelim STUCK.
        eby eapply Comp.step_extcallmem_fail. 
      - eelim STUCK.
        eby eapply Comp.step_extcallmem.
    Case "TEstartmem".
      destruct (tso_arglist_dec tso t (f :: args) Ebft) as [FAIL | [ev [tso' MA]]].
      - eelim STUCK.
        eby eapply Comp.step_startmem_read_fail. 
      - inversion MA; subst.
          destruct (fresh_slot_in_map _ thr) as [newtid TIDF]. 
          destruct v; try (eby eelim STUCK; eapply Comp.step_startmem_spawn_fail). 
          destruct (SEM_init _ ge p vals) as [ns|] _eqn : INI.
            set (ntso := mktsostate (tupdate newtid nil tso'.(tso_buffers)) tso'.(tso_mem)).
            specialize (STUCK (ntso, (thr ! t <- ts') ! newtid <- ns ) Etau); elim STUCK.
            assert(TSO_STEP: tso_step tso' (MMstart t newtid) ntso).
            unfold ntso. eby eapply tso_step_start.
            apply (Comp.step_startmem tso_mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                     STEP MA TSO_STEP TST TIDF (refl_equal _) INI).
          eby eelim STUCK; eapply Comp.step_startmem_spawn_fail.
        destruct (fresh_slot_in_map _ thr) as [newtid TIDF]. 
        destruct v; try (eby eelim STUCK; eapply Comp.step_startmem_spawn_fail). 
        destruct (SEM_init _ ge p0 vals) as [ns|] _eqn : INI.
          set (ntso := mktsostate (tupdate newtid nil tso'.(tso_buffers)) tso'.(tso_mem)).
          specialize (STUCK (ntso, (thr ! t <- ts') ! newtid <- ns ) Etau); elim STUCK.
          assert(TSO_STEP: tso_step tso' (MMstart t newtid) ntso).
          unfold ntso. by apply (tso_step_start _ _ _ _ _ (refl_equal _)).
          apply (Comp.step_startmem tso_mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                   STEP MA TSO_STEP TST TIDF (refl_equal _) INI).
        eby eelim STUCK; eapply Comp.step_startmem_spawn_fail.
*)





End MMstep.
End MMsemantics.
End Comp.

Tactic Notation "comp_step_cases" tactic(f) tactic(c) :=
    f; [
      c "step_ord" |
      c "step_ext" |
      c "step_unbuf" |
      c "step_tau" |
      c "step_start" |
      c "step_start_fail" |
      c "step_exit" |
      c "step_read_fail" |
      c "step_write_fail" |
      c "step_free_fail" |
      c "step_rmw_fail" |
      c "step_thread_stuck" |
      c "step_alloc_out_of_memory" |
      c "step_thread_out_of_memory" |
      c "step_extcallmem" |
      c "step_extcallmem_fail" |
      c "step_startmem" |
      c "step_startmem_read_fail" |
      c "step_startmem_spawn_fail"].

