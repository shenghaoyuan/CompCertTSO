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
Require Import Memcomp.
Require Import Ast.
Require Import Globalenvs.
Require Import Maps.
Require Import Simulations.
Require Import Classical.
Require Import Libtactics.

(** * TSO machine definition *)

(** We buffer writes, allocations and frees. Note that we do
    not buffer reads; reads are satisfied directly from buffers, or from
    the main memory if the buffer of the reading thread does not contain
    a corresponding write. *)
Inductive buffer_item : Type :=
  | BufferedWrite (p: pointer) (c: memory_chunk) (v: val)
  | BufferedAlloc (p: pointer) (i: int) (k: mobject_kind)
  | BufferedFree  (p: pointer) (k: mobject_kind).

Tactic Notation "buffer_item_cases" tactic(first) tactic(c) :=
    first; [
      c "BufferedWrite" |
      c "BufferedAlloc" |
      c "BufferedFree"].

(** [apply_buffer_item] applies a given buffer item to the given memory 
    state. *)
Definition apply_buffer_item (bi : buffer_item) (m : mem) : option mem :=
  match bi with 
    | BufferedWrite p c v => store_ptr c m p v
    | BufferedAlloc p i k => alloc_ptr (p,i) k m
    | BufferedFree p k => free_ptr p k m
  end.

(** [apply_buffer] applies a given buffer to the given memory state. The buffer
    is applied from left to right (i.e., starting with the head). *)
Fixpoint apply_buffer (b : list buffer_item) (m : mem) : option mem :=
  match b with
    | nil => Some m
    | bi :: rest => optbind (fun m' => apply_buffer rest m') 
                            (apply_buffer_item bi m) 
  end.

Definition buffers := thread_id -> list buffer_item.

Definition tupdate {A} (tid : thread_id) (v : A) f t' : A :=
  if peq t' tid then v else f t'.

Lemma tupdate_s : forall {A} tid (v: A) f, tupdate tid v f tid = v.
Proof. by intros; unfold tupdate; destruct peq. Qed.

Lemma tupdate_o : forall {A} tid (v: A) f t', t' <> tid -> tupdate tid v f t' = (f t').
Proof. by intros; unfold tupdate; destruct peq. Qed.

Lemma tupdate_red:
  forall {A} tid (x y : A) b, tupdate tid x (tupdate tid y b) = tupdate tid x b.
Proof.
  by intros; apply extensionality; intro; unfold tupdate; destruct peq.
Qed. 

Lemma tupdate_red2:
  forall {A} tid (b: _ -> A), tupdate tid (b tid) b = b.
Proof.
  by intros; apply extensionality; intro; unfold tupdate; destruct peq; subst.
Qed. 

Lemma tupdate_comm:
  forall {A} tid tid' (x y: A) b, tid' <> tid -> 
   tupdate tid x (tupdate tid' y b) = tupdate tid' y (tupdate tid x b).
Proof.
  by intros; apply extensionality; intro; unfold tupdate; do 2 (destruct peq; clarify).
Qed. 

(** State of the TSO machine consists of a possibly 
    thread states (with buffers) and global memory. *)
Record tso_state := mktsostate
  { tso_buffers : buffers
  ; tso_mem : mem
  }.

(** [buffer_insert] inserts item [bi] to the end of thread [t]'s buffer. *)
Definition buffer_insert (ts : tso_state) (t : thread_id) (bi : buffer_item) :=
  mktsostate (tupdate t (ts.(tso_buffers) t ++ bi :: nil) ts.(tso_buffers))
             ts.(tso_mem).

(** State is unbuffer-safe if all possible unbufferings succeed. *)
Inductive unbuffer_safe : tso_state -> Prop :=
| unbuffer_safe_unbuffer:
  forall tso
    (ABIS: forall t bi b, 
      tso.(tso_buffers) t = bi :: b ->
      exists m', apply_buffer_item bi tso.(tso_mem) = Some m')
    (UNBS: forall t bi b m', 
      tso.(tso_buffers) t = bi :: b ->
      apply_buffer_item bi tso.(tso_mem) = Some m' ->
      unbuffer_safe (mktsostate (tupdate t b tso.(tso_buffers))
                                m')),
    unbuffer_safe tso.

(** Initial state of the TSO machine. *)
Definition tso_init (m : mem) : tso_state :=
  mktsostate (fun t => nil) m.

(** Operational semantics of the tso machine. Note that whenever we insert 
    to a buffer, we make sure that all possible unbufferings succeed. 
    This ensures that there no pending failures in buffers, so the
    semantics cannot get stuck on unbufferings. *)
Inductive tso_step : tso_state -> mm_event -> tso_state -> Prop :=
  (* MEMORY OPERATIONS *)
  | tso_step_write : (* Memory write  (goes into buffer) *)
    forall t ts ts' p c v
      (EQts': ts' = buffer_insert ts t (BufferedWrite p c v))
      (SAFE: unbuffer_safe ts'),
    tso_step ts 
             (MMmem t (MEwrite p c v))
             ts'
  | tso_step_read :   (* Memory read *)
    forall ts t m' p c v
      (AB: apply_buffer (ts.(tso_buffers) t) ts.(tso_mem) = Some m')
      (LD: load_ptr c m' p = Some v),
    tso_step ts (MMmem t (MEread p c v)) ts
  | tso_step_read_fail: (* Memory read failure *)
    forall ts t p c
      (Bemp: ts.(tso_buffers) t = nil)
      (LD: load_ptr c ts.(tso_mem) p = None),
    tso_step ts (MMreadfail t p c) ts
  | tso_step_alloc :  (* Memory allocation  (goes into buffer) *)
    forall t ts ts' p i k
      (EQts': ts' = buffer_insert ts t (BufferedAlloc p i k))
      (UNS: unbuffer_safe ts'),
    tso_step ts 
             (MMmem t (MEalloc p i k)) 
             ts'
  | tso_step_free :  (* Memory deallocation (goes into buffer) *)
    forall t ts ts' p k
      (EQts': ts' = buffer_insert ts t (BufferedFree p k))
      (UNS: unbuffer_safe ts'),
    tso_step ts 
             (MMmem t (MEfree p k))
             ts'
(*  | tso_step_free_fail : (* Memory deallocation fail *)
    forall t ts ts' p k
      (EQts': ts' = buffer_insert ts t (BufferedFree p k))
      (UNS: ~ unbuffer_safe ts'),
    tso_step ts 
             (TSOfreefail t p k)
             ts *)
  | tso_step_free_fail : (* Memory deallocation fail *)
    forall t ts p k
      (Bemp: ts.(tso_buffers) t = nil)
      (FAIL: match free_ptr p k (tso_mem ts) with
           | None => True
           | Some m' => exists tid', exists p, exists c, exists v, exists b, 
                           tso_buffers ts tid' = BufferedWrite p c v :: b
                        /\ store_ptr c m' p v = None
         end),
    tso_step ts 
             (MMfreefail t p k)
             ts
  | tso_step_outofmem :
     forall t ts n k
       (OOM: forall p, 
               ~ unbuffer_safe (buffer_insert ts t (BufferedAlloc p n k))),
    tso_step ts
             (MMoutofmem t n k)
             ts
  (* UNBUFFERING *)
  | tso_step_unbuffer : (* Apply buffer item *)
    forall t ts bufs' bi b m'
      (EQbufs: ts.(tso_buffers) t = bi :: b)
      (EQbufs': bufs' = tupdate t b ts.(tso_buffers))
      (AB: apply_buffer_item bi ts.(tso_mem) = Some m'),
    tso_step ts
             (MMtau)
             (mktsostate bufs' m')
  (* ATOMIC INSTRUCTIONS *)
  | tso_step_mfence : (* Mfence (note that the buffer must be flushed) *)
    forall ts t
      (Bemp: ts.(tso_buffers) t = nil),
    tso_step ts 
             (MMmem t MEfence) 
             ts
  | tso_step_rmw : (* Read-modify-write (note that the buffer must be flushed) *)
    forall ts ts' t p c v instr m'
      (Bemp: ts.(tso_buffers) t = nil)
      (LD: load_ptr c ts.(tso_mem) p = Some v)
      (STO: store_ptr c ts.(tso_mem) p (rmw_instr_semantics instr v) = Some m')
      (EQts': mktsostate ts.(tso_buffers) m' = ts'),
    tso_step ts 
             (MMmem t (MErmw p c v instr)) 
             ts'
  (* THREAD MANAGEMENT *)
  | tso_step_start : (* Thread start *)
    forall ts ts' t bufs' newtid
      (EQbufs': bufs' = tupdate newtid nil ts.(tso_buffers)) (* this is not really needed... *)
      (EQts': mktsostate bufs' ts.(tso_mem) = ts'),
    tso_step ts 
             (MMstart t newtid)
             ts'
  | tso_step_finish : (* Thread finish *)
    forall ts t
      (Bemp: ts.(tso_buffers)  t = nil),
    tso_step ts 
             (MMexit t)
             ts
.

Tactic Notation "tso_step_cases" tactic(first) tactic(c) :=
    first; [
      c "tso_step_write" |
      c "tso_step_read" |
      c "tso_step_read_fail" |
      c "tso_step_alloc" |
      c "tso_step_free" |
      c "tso_step_free_fail" |
      c "tso_step_outofmem" |
      c "tso_step_unbuffer" |
      c "tso_step_mfence" |
      c "tso_step_rmw" |
      c "tso_step_start" |
      c "tso_step_finish"].

(** * Facts about the tso machine *)

(** ** Lemmata about [apply_buffer] *)

Lemma apply_buffer_app:
  forall b1 b2 m,
  apply_buffer (b1 ++ b2) m = 
  optbind (fun m => apply_buffer b2 m) 
          (apply_buffer b1 m).
Proof.
  induction b1 as [|h t IH]; simpl; intros; try done.
  by destruct (apply_buffer_item h m); simpl; rewrite ?IH.
Qed.

Lemma apply_buffer_item_none_arange:
  forall m m' bi
    (EQ: arange_eq (fun _ => true) m m'),
    (apply_buffer_item bi m = None <->
    apply_buffer_item bi m' = None).
Proof.
  intros; (buffer_item_cases (destruct bi as [p' c' v'|[b ofs] n k|p' k]) Case); simpl.
  Case "BufferedWrite".
    generalize (store_chunk_allocated_spec c' m p' v').
    generalize (store_chunk_allocated_spec c' m' p' v').
    destruct (store_ptr c' m p' v');
    destruct (store_ptr c' m' p' v'); try done; intros A B; split; try done.
      eby elim A; eapply chunk_allocated_and_aligned_arange.
    eby elim B; eapply chunk_allocated_and_aligned_arange; try eapply arange_eq_sym.
  Case "BufferedAlloc".
    generalize (alloc_cond_spec (Ptr b ofs,n) k m);
    generalize (alloc_cond_spec (Ptr b ofs,n) k m');
    destruct alloc_ptr; destruct alloc_ptr; try done; intros A B; split; try done.
      destruct A as (RA & ? & RESTR & ROVER);
      destruct B as [|[NRESTR|(r & k' & RO & RA')]]; try tauto.
        by elim NRESTR; unfold restricted_pointer in *; rewrite (proj2 EQ).
      eby byContradiction; eapply (ROVER _ _ RO); apply -> (proj1 EQ).
    destruct B as (RA & ? & ? & ROVER).
    destruct A as [|[NRESTR|(r & k' & RO & RA')]]; try tauto.
      by elim NRESTR; unfold restricted_pointer; rewrite <- (proj2 EQ).
    eby byContradiction; eapply (ROVER _ _ RO); apply <- (proj1 EQ).
  Case "BufferedFree".
    generalize (free_cond_spec p' k m);
    generalize (free_cond_spec p' k m').
    destruct free_ptr; destruct free_ptr; try done; intros A B; split; try done.
      eby destruct A as (n & ?); elim (B n); apply <- (proj1 EQ).
    eby destruct B as (n & ?); elim (A n); apply -> (proj1 EQ).
Qed.

Lemma apply_buffer_item_some_fw_arange:
  forall {bi m m' mb}
    (EQ: arange_eq (fun _ => true) m m')
    (AB: apply_buffer_item bi m = Some mb),
    exists mb', apply_buffer_item bi m' = Some mb' /\ arange_eq (fun _ => true) mb mb'.
Proof.
  intros; destruct bi; simpl.
    eby eapply store_ptr_some_arange.
   eby eapply alloc_ptr_some_arange.
  eby eapply free_ptr_some_arange.
Qed.

Lemma apply_buffer_some_fw_arange:
  forall {b m m' mb}
    (EQ: arange_eq (fun _ => true) m m')
    (AB: apply_buffer b m = Some mb),
    exists mb', apply_buffer b m' = Some mb' /\ arange_eq (fun _ => true) mb mb'.
Proof.
  induction b as [|bi b IH]; simpl; intros; clarify.
    by eauto.
  destruct (apply_buffer_item bi m) as [] _eqn: ABI; try done.
  exploit @apply_buffer_item_some_fw_arange; try edone; intros (? & -> & ?).
  eby eapply IH.
Qed.

Lemma load_eq_preserved_by_apply_buffer_arange:
  forall {b c m mx p m' mx'}
    (Leq: load_ptr c m p = load_ptr c mx p)
    (AB: apply_buffer b m = Some m')
    (ABx: apply_buffer b mx = Some mx')
    (Req: arange_eq (fun _ => true) m mx),
  load_ptr c m' p = load_ptr c mx' p.
Proof.
  induction b as [|[p' c' v'|p' n' k|p' k] b IH]; simpl; intros; clarify;
   destruct (optbind_someD AB) as (m'' & A & B);
   destruct (optbind_someD ABx) as (mx'' & Ax & Bx); clear AB ABx;
   apply IH with (m := m'') (mx := mx''); try eassumption.
   eby eapply @load_eq_preserved_by_store.
   eby eapply store_ptr_some_arange1.
   eby eapply @load_eq_preserved_by_alloc.
   eby eapply alloc_ptr_some_arange1.
   eby eapply @load_eq_preserved_by_free_arange.
   eby eapply free_ptr_some_arange1.
Qed.

Lemma apply_buffer_item_arange1:
  forall {bi m mx m' mx' f}
    (AB: apply_buffer_item bi m = Some m')
    (ABx: apply_buffer_item bi mx = Some mx')
    (Req: arange_eq f m mx),
  arange_eq f m' mx'.
Proof.
  destruct bi as [p' c' v'|p' n' k|p' k]; simpl; intros.
  eby eapply store_ptr_some_arange1.
  eby eapply alloc_ptr_some_arange1.
  eby eapply free_ptr_some_arange1.
Qed.

Lemma apply_buffer_arange1:
  forall {b m mx m' mx' f}
    (AB: apply_buffer b m = Some m')
    (ABx: apply_buffer b mx = Some mx')
    (Req: arange_eq f m mx),
  arange_eq f m' mx'.
Proof.
  induction b as [|bi b IH]; simpl; intros; clarify. 
  destruct (optbind_someD AB) as (m'' & A & B);
  destruct (optbind_someD ABx) as (mx'' & Ax & Bx); clear AB ABx.
  apply IH with (m := m'') (mx := mx''); try eassumption.
  eby eapply apply_buffer_item_arange1.
Qed.

Lemma mem_agrees_on_preserved_by_apply_buffer_item:
  forall {m mx l bi m' mx'}
    (EQ: mem_agrees_on m mx l)
    (REQ: arange_eq (fun _ => true) m mx)
    (F: apply_buffer_item bi m = Some m')
    (Fx: apply_buffer_item bi mx = Some mx'),
  mem_agrees_on m' mx' l.
Proof.
  intros; destruct bi as [| |]; simpl in *;
  [ eby eapply mem_agrees_on_preserved_by_store
  | eby eapply mem_agrees_on_preserved_by_alloc
  | eby eapply mem_agrees_on_preserved_by_free_arange].
Qed.

Lemma mem_agrees_on_preserved_by_apply_buffer:
  forall {b m mx l m' mx'}
    (EQ: mem_agrees_on m mx l)
    (REQ: arange_eq (fun _ => true) m mx)
    (F: apply_buffer b m = Some m')
    (Fx: apply_buffer b mx = Some mx'),
  mem_agrees_on m' mx' l.
Proof.
  induction b as [|bi b IH]; simpl; intros; clarify.
  destruct (apply_buffer_item bi m) as [] _eqn: ABI; simpl in *; try done.
  exploit @apply_buffer_item_some_fw_arange; try edone; [];
    intros (? & ABIx & ?); rewrite ABIx in *.
  pose proof (mem_agrees_on_preserved_by_apply_buffer_item EQ REQ ABI ABIx).
  eby eapply IH.
Qed.

Lemma alloc_comm_apply_item:
  forall bi r k m m1 m2 m'
    (A : alloc_ptr r k m = Some m1)
    (B1: apply_buffer_item bi m1 = Some m')
    (B2: apply_buffer_item bi m = Some m2),
  alloc_ptr r k m2 = Some m'.
Proof.
  intros []; intros until 0;
  [eapply alloc_comm_store|eapply alloc_comm_alloc|eapply alloc_comm_free].
Qed.

Lemma free_comm_apply_item:
  forall bi p k m m1 m2 m'
    (A : free_ptr p k m = Some m1)
    (B1: apply_buffer_item bi m1 = Some m')
    (B2: apply_buffer_item bi m = Some m2),
  free_ptr p k m2 = Some m'.
Proof.
  intros []; intros until 0;
  [eapply free_comm_store|eapply free_comm_alloc|eapply free_comm_free].
Qed.

Lemma mem_consistent_with_restr_apply_item:
  forall {m bi m'},
    apply_buffer_item bi m = Some m' ->
    mrestr m' = mrestr m.
Proof.
  intros m bi m' ABI.
  unfold apply_buffer_item in ABI; destruct bi;
  [ eapply restr_of_store | 
    eapply restr_of_alloc | 
    eapply restr_of_free]; apply ABI.
Qed.

Lemma mem_consistent_with_restr_apply_buffer:
  forall b m m',
    apply_buffer b m = Some m' ->
    mrestr m' = mrestr m.
Proof.
  induction b as [|bi br IH]; intros m m' AB.

  by inv AB.

  simpl in AB; destruct (apply_buffer_item bi m) as [mi|] _eqn : ABI;
    try edone; simpl in AB.
  rewrite (IH mi).
    eby eapply mem_consistent_with_restr_apply_item.
  done.
Qed.

Lemma sim_apply_item_preserves_alloc_impl:
  forall m1 m2 m1' m2' bi,
    apply_buffer_item bi m1 = Some m1' ->
    apply_buffer_item bi m2 = Some m2' ->
    (forall r k, range_allocated r k m1 -> 
                 range_allocated r k m2) ->  
    forall r k, range_allocated r k m1' -> 
                range_allocated r k m2'.
Proof.
  intros m1 m2 m1' m2' bi ABI1 ABI2 AI r k RA1'.
  unfold apply_buffer_item in ABI1, ABI2.
  destruct bi as [pi ci vi | pi ni ki | pi ki].
      (* Write *)
      apply (store_preserves_allocated_ranges ABI1) in RA1'.
      apply (store_preserves_allocated_ranges ABI2 _ _).
      by apply AI.
    (* Alloc *)
    destruct (alloc_preserves_allocated_back ABI1 _ _ RA1')
      as [[-> ->] | DISJ].
      apply alloc_someD in ABI2.  by destruct ABI2.
    apply AI in DISJ.
    eby eapply alloc_preserves_allocated.
  (* Free *)
  pose proof (free_preserves_allocated_back ABI1 _ _ RA1') as RA1.
  apply AI in RA1.
  apply (free_preserves_allocated ABI2) in RA1.
  destruct RA1 as [RA2 | [<- <-]]. done.
  byContradiction.
  destruct r. simpl in ABI1.
  eapply free_not_allocated. apply ABI1.  edone.
Qed.

(** ** Lemmata about [unbuffer_safe] *)

Lemma unbuffer_unbuffer_safe:
  forall {tso t bi b},
    unbuffer_safe tso ->
    tso.(tso_buffers) t = bi :: b ->
    exists m', apply_buffer_item bi tso.(tso_mem) = Some m' /\
               unbuffer_safe (mktsostate (tupdate t b tso.(tso_buffers))
                                         m').
Proof.
  destruct 1; intro EQ.
  destruct (ABIS _ _ _ EQ) as (m' & ABI); eauto.
Qed.

Lemma apply_item_unbuffer_safe:
  forall bufs m t bi b m'
    (US: unbuffer_safe (mktsostate bufs m))
    (DC: bufs t = bi :: b)
    (ABI: apply_buffer_item bi m = Some m'),
    unbuffer_safe (mktsostate (tupdate t b bufs) m').
Proof.
  intros; destruct (unbuffer_unbuffer_safe US DC) as [m'' [ABI' US']].
  by simpl in ABI'; rewrite ABI in ABI'; inv ABI'.
Qed.

Lemma apply_prefix_unbuffer_safe:
  forall bufs m t b1 b2 m'
    (US: unbuffer_safe (mktsostate bufs m))
    (Beq: bufs t = b1 ++ b2)
    (ABI: apply_buffer b1 m = Some m'),
    unbuffer_safe (mktsostate (tupdate t b2 bufs) m').
Proof.
  intros until 0; revert bufs m.
  induction b1 as [|bi b1 IH]; intros; simpl in *; clarify.
    by rewrite tupdate_red2.
  destruct (unbuffer_unbuffer_safe US Beq) as (? & ABI' & US'); simpl in *.
  rewrite ABI' in ABI; simpl in *.
  by exploit IH; try eassumption; rewrite ?tupdate_s, ?tupdate_red.
Qed.

Lemma no_unbuffer_errors:
  forall stso t,
    unbuffer_safe stso ->
    apply_buffer (stso.(tso_buffers) t) stso.(tso_mem) <> None.
Proof.
  intros [b m] t; simpl.
  remember (b t) as bt. revert b m Heqbt.
  induction bt as [|bh bt IH]; [done|].
  (* step case *)
  intros b m BT US. 
  destruct (unbuffer_unbuffer_safe US (sym_eq BT))
    as [mt' [ABI' US']]; simpl in *.
  destruct (apply_buffer_item bh m) as [mt|] _eqn:EQ; clarify.
  by eapply IH, US'; rewrite tupdate_s.
Qed.

Definition tso_fin_sup (tso : tso_state) :=
  { l | NoDup l /\ forall t, ~ In t l -> tso.(tso_buffers) t = nil }.

Lemma fin_sup_buffer_insert:
  forall t bi tso,
    tso_fin_sup tso ->
    tso_fin_sup (buffer_insert tso t bi).
Proof.
  intros t bi tso [l [ND FS]].
  destruct (In_dec peq t l) as [IN | NIN].
    exists l; split; try done.
    intros t' NIN'; unfold buffer_insert, tupdate; simpl.
    by destruct (peq t' t) as [-> | N]; [|apply FS].
  exists (t :: l).
  split. by constructor.
  intros t' NIN'; unfold buffer_insert, tupdate; simpl in *.
  destruct (peq t' t) as [-> | N]. tauto.
  destruct (In_dec peq t' l) as [IN2 | NIN2]. tauto.
  by apply FS.
Qed.

Lemma tso_fin_sup_change:
  forall tso tso' t,
    tso_fin_sup tso ->
    (forall t', t' <> t -> tso.(tso_buffers) t' = tso'.(tso_buffers) t') ->
    tso_fin_sup tso'.
Proof.
  intros tso tso' t [l [ND FS]] B.
  destruct (In_dec peq t l) as [IN | NIN].
    exists l. split. done.
    intros t' NIN.
    destruct (peq t' t) as [-> | N]. done.
    rewrite <- B. by apply FS. done.
  exists (t :: l).
  split. by constructor.
  intros t' NIN'. 
  destruct (peq t' t) as [-> | N].
    elim NIN'. apply in_eq.
  rewrite <- B. apply FS. intro. elim NIN'. by apply in_cons.
  done.
Qed.

Lemma tso_fin_sup_tupdate:
  forall tso t b m,
    tso_fin_sup tso ->
    tso_fin_sup (mktsostate (tupdate t b tso.(tso_buffers)) m).
Proof.
  intros tso t b m FS.
  eapply (tso_fin_sup_change _ _ t). edone.
  intros t' N.
  unfold tupdate; simpl.
  by destruct (peq t' t).
Qed.

Lemma unbuffer_safe_on_buffer_prefixes:
  forall b m,
    unbuffer_safe (mktsostate b m) ->
    forall b',
      (forall t, exists bs, b t = b' t ++ bs) ->
      unbuffer_safe (mktsostate b' m).
Proof.
  intros b m US.
  remember (mktsostate b m) as tso; revert b m Heqtso.
  induction US as [tso ABIS UBS IH].
  intros b m E b' PFX. rewrite E in *; simpl in *.
  eapply unbuffer_safe_unbuffer; simpl.
    intros t' bi bs ED.
    destruct (PFX t') as [brest BR]. rewrite ED, <- app_comm_cons in BR.
    eby eapply ABIS.
  intros t' bi bs m' Ebt ABI.
  destruct (PFX t') as [brest BR]. rewrite Ebt, <- app_comm_cons in BR.
  eapply IH; try edone.
  intro t. unfold tupdate. 
  destruct (peq t t') as [Et | N]. eby eexists.
  apply PFX.
Qed.

Lemma unbuffer_safe_tupdate_nil:
  forall b m t
    (US: unbuffer_safe (mktsostate b m)),
    unbuffer_safe (mktsostate (tupdate t nil b) m).
Proof.
  intros; eapply unbuffer_safe_on_buffer_prefixes; try edone.
  intro t'. unfold tupdate. destruct (peq t' t).
  exists (b t'). done. eexists nil. apply app_nil_end.
Qed.

Lemma unbuffer_safe_arange:
  forall b m m'
    (EQ: arange_eq (fun _ => true) m m')
    (UNB: unbuffer_safe (mktsostate b m)),
  unbuffer_safe (mktsostate b m').
Proof.
  intros; remember (mktsostate b m) as tso; revert b m m' Heqtso EQ.
  induction UNB as [tso ABIS _ UNBS]; intros; clarify; simpl in *.
  constructor; simpl.
  - eby intros ? ? ? M; destruct (ABIS _ _ _ M) as [? X];
        destruct (apply_buffer_item_some_fw_arange EQ X) as (? & Y & _);
        eexists.
  intros ? ? ? ? M ABI. 
  destruct (ABIS _ _ _ M) as [? X].
  eapply (UNBS _ _ _ _ M X); try edone. 
  by destruct (apply_buffer_item_some_fw_arange EQ X) as (? & Y & REQ); clarify'.
Qed.

Lemma unbuffer_safe_buf_ext:
  forall tso tso',
    unbuffer_safe tso ->
    (forall t, tso_buffers tso t = tso_buffers tso' t) ->
    tso_mem tso = tso_mem tso' ->
    unbuffer_safe tso'.
Proof.
  intros [bs m] [bs' m'] US Beq Meq.
  simpl in *; subst.
  eapply unbuffer_safe_on_buffer_prefixes. eassumption.
  intro t'. exists nil. by rewrite <- app_nil_end.
Qed.

Lemma apply_buffer_unbuffer_safe:
  forall t m' b2 b1 bufs m,
    unbuffer_safe (mktsostate bufs m) ->
    bufs t = b1 ++ b2 ->
    apply_buffer b1 m = Some m' ->
    unbuffer_safe (mktsostate (tupdate t b2 bufs) m').
Proof.
  intros t m' b2 b1.
  induction b1 as [|bh b1 IH]; simpl; intros bufs m US BD AB.

  inv AB. 
  eapply unbuffer_safe_buf_ext; try edone.
  intros t'. simpl. unfold tupdate. 
  by destruct (peq t' t) as [-> | N].

  destruct (apply_buffer_item bh m) as [mi|] _eqn : ABI; 
    try done; simpl in AB.
  by eapply unbuffer_safe_buf_ext; 
    [eapply IH; [eby eapply (apply_item_unbuffer_safe _ _ t)| |]| |];
    intros; try done; unfold tupdate; simpl; destruct peq.
Qed.

(** Reachability by unbufferings. *)
Inductive apply_buffer_reachable : thread_id -> 
                                   tso_state -> 
                                   list buffer_item ->
                                   tso_state -> Prop :=
| apply_buffer_reachable_refl:
  forall t tso,
    apply_buffer_reachable t tso nil tso
| apply_buffer_reachable_step:
  forall tso t bi b m' tso' tso'' acc
    (BTD: tso.(tso_buffers) t = bi :: b)
    (ABI: apply_buffer_item bi tso.(tso_mem) = Some m')
    (Etso': tso' = mktsostate
                      (tupdate t b tso.(tso_buffers))
                      m')
    (ABRA: apply_buffer_reachable t tso' acc tso''),
    apply_buffer_reachable t tso (bi :: acc) tso''.

(** Safety of buffer with respect of memory (i.e., applying
    the buffer does not fail). *)
Definition buffer_safe_for_mem (b : list buffer_item)
                               (m : mem) : Prop :=
  exists m', apply_buffer b m = Some m'.

Lemma buffer_safe_for_mem_cons:
  forall bi b m m',
    buffer_safe_for_mem (bi :: b) m ->
    apply_buffer_item bi m = Some m' ->
    buffer_safe_for_mem b m'.
Proof.
  intros bi b m m' [m'' BSM] ABI.
  simpl in BSM. rewrite ABI in BSM. simpl in BSM.
  by exists m''.
Qed.

Lemma buffer_safe_for_mem_cons_head:
  forall bi b m,
    buffer_safe_for_mem (bi :: b) m ->
    exists m', apply_buffer_item bi m = Some m'.
Proof.
  intros bi b m [m'' BSM].
  simpl in BSM. 
  destruct apply_buffer_item.
    simpl in BSM. eby eexists.
  done.
Qed.

Lemma buffer_safe_for_mem_app1:
  forall b1 b2 m,
    buffer_safe_for_mem (b1 ++ b2) m ->
    buffer_safe_for_mem b1 m.
Proof.
  intros b1 b2 m [m' BSM].
  rewrite apply_buffer_app in BSM.
  destruct (apply_buffer b1 m) as [m''|] _eqn : E;
    simpl in BSM; try done.
  eby exists m''. 
Qed.

Lemma buffer_safe_for_mem_app2:
  forall b1 b2 m m',
    buffer_safe_for_mem (b1 ++ b2) m ->
    apply_buffer b1 m = Some m' ->
    buffer_safe_for_mem b2 m'.
Proof.
  intros b1 b2 m m' [m'' BSM] ABI.
  rewrite apply_buffer_app in BSM. rewrite ABI in BSM.
  simpl in BSM.
  eby exists m''. 
Qed.

Lemma unbuffer_safe_to_buffer_safe_for_mem:
  forall stso t bis rb,
    unbuffer_safe stso ->
    stso.(tso_buffers) t = bis ++ rb ->
    buffer_safe_for_mem bis stso.(tso_mem).
Proof.
  intros stso t bis rb UBS.
  revert bis rb. simpl in UBS.
  induction UBS as [tso' CABI UBS' IH].
  
  intros bis rb Eb. 
  destruct bis as [|bi rbis].
    eexists. simpl. reflexivity.
  rewrite <- app_comm_cons in Eb.
  destruct (CABI _ _ _ Eb) as [im' ABIi].
  specialize (IH _ _ _ _ Eb ABIi rbis rb). simpl in IH. 
  rewrite tupdate_s in IH. destruct (IH (refl_equal _)) as [m' AB].
  exists m'. by simpl; rewrite ABIi.
Qed.

(** Well-founded order on buffers that goes down if unbuffered *)
Definition buffers_measure (l : list thread_id)
                           (b : buffers) : nat :=
  fold_right (fun t sz => (sz + length (b t))%nat) O l.

Lemma buffer_measure_zero:
  forall l b t
    (BM: O = buffers_measure l b)
    (IN: In t l),
    b t = nil.
Proof.  
  induction l as [|h rest IH]; simpl; try done; intros.
  apply sym_eq in BM.
  destruct (plus_is_O _ _ BM) as [BM0 LBH0].
  destruct IN as [-> | INR].
    by induction (b t).
  by apply IH.
Qed.

Lemma preserve_dom_unbuffer:
  forall t l b bi tso,
    tso_buffers tso t = bi :: b ->
    (forall t', ~ In t' l -> tso_buffers tso t' = nil) ->
    (forall t', ~ In t' l -> (tupdate t b (tso_buffers tso)) t' = nil).
Proof.
  intros t l b bi tso BNE DOM t' NIN.
  specialize (DOM t' NIN).
  unfold tupdate. 
  by destruct (peq t' t) as [-> | NEQ]; try rewrite DOM in *.
Qed.

Lemma buffer_measure_tupdate:
  forall l t b bufs,
    ~ In t l -> buffers_measure l (tupdate t b bufs) = 
                buffers_measure l bufs.
Proof.
  induction l as [|h rest IH]; try done.
  intros t b bufs NIN. simpl.
  destruct (In_dec peq t rest) as [INR | NINR].
    by elim NIN; apply in_cons.
  unfold tupdate at 2. destruct (peq h t) as [<- | Nht].
    by elim NIN; constructor. 
  by rewrite ! IH.
Qed.

Lemma nodup_decomp:
  forall {A} {h : A} {t : list A} (ASM: NoDup (h :: t)), 
    ~ In h t /\ NoDup t.
Proof.
  by intros; inv ASM.
Qed.

Lemma in_not_head:
  forall {A} {e : A} {h} {t}, In e (h :: t) -> h <> e -> In e t.
Proof.
  by intros A e h t []. 
Qed.

Lemma measure_down_unbuffer:
  forall l bb t b bi
    (NDUP: NoDup l)
    (EQbuff: bb t = bi :: b)
    (IN: In t l),
    {bsize |
      bsize = buffers_measure l (tupdate t b bb) /\
      S bsize = buffers_measure l bb}.
Proof.
  induction l as [|h rest IH]; intros; simpl; [done|].
  pose proof (nodup_decomp NDUP) as [NIN NDrest].
  unfold tupdate at 2. 
  destruct (peq h t) as [<- | N].
    rewrite buffer_measure_tupdate, EQbuff; [|done]; simpl. 
    by eexists.
  apply in_not_head in IN; [|done].
  destruct (IH _ _ _ _ NDrest EQbuff IN) as [bsize [BS SBS]].
  by rewrite <- BS, <- SBS; eexists. 
Qed.

(** Decidability of unbuffer_safe *)

Lemma unbuffer_safe_dec :
  forall tso, tso_fin_sup tso ->
    {unbuffer_safe tso} + {~ unbuffer_safe tso}.
Proof.
  destruct 1 as (l & NDUP & DOM).
  remember (buffers_measure l tso.(tso_buffers)) as bsize.
  revert tso NDUP DOM Heqbsize.
  induction bsize as [|bsize IH].
  
  (* Base case *)
  intros tso NDUP DOM BM. 
  left; constructor; intro t;
    destruct (In_dec tid_eq_dec t l) as [IN | NIN];
      (try by rewrite (buffer_measure_zero _ _ _ BM IN));
        by rewrite DOM.

  (* Induction step *)
  intros tso NDUP DOM BM.
  (* First see whether there is a thread for which unbuffer fails *)
  set (ABS t := 
    match tso.(tso_buffers) t with
      | bi :: rb =>
        match apply_buffer_item bi tso.(tso_mem) with
          | Some m' => 
              unbuffer_safe (mktsostate (tupdate t rb tso.(tso_buffers))
                                        m')
          | _ => False
        end
      | _ => True
    end).
  assert (ABSDEC: forall t, {ABS t} + {~ ABS t}).
    intro t.
    destruct (tso.(tso_buffers) t) as [|bi rb] _eqn : Etb.
      left. unfold ABS. by rewrite Etb.
    destruct (apply_buffer_item bi tso.(tso_mem)) as [m'|] _eqn: Eabi.
      specialize (IH (mktsostate 
                     (tupdate t rb (tso_buffers tso)) m') NDUP).
      specialize (IH (preserve_dom_unbuffer _ _ _ _ _ Etb DOM)).
      destruct (In_dec peq t l) as [INR | NINR].
        2: rewrite DOM in Etb; done.
      destruct (measure_down_unbuffer _ _ _ _ _ NDUP Etb INR) 
        as [s [BS SBS]].
      rewrite <- BM in SBS. injection SBS as Ebsize. rewrite Ebsize in *.
      destruct (IH BS) as [UBS | UBUS]; [left|right]; by unfold ABS; 
        rewrite Etb, Eabi.
    right. unfold ABS. by rewrite Etb, Eabi.
  destruct (strong_in_dec_neg ABS ABSDEC l) as [[ft [INl FABI]] | SUCCABI].
    (* Some apply buffer fails *)
    right. intro UBS. destruct UBS as [ts AS UBS']. 
    unfold ABS in FABI. destruct (ts.(tso_buffers) ft) as [|bi b] _eqn : Etb; try done.
    destruct (apply_buffer_item bi ts.(tso_mem)) as [|m'] _eqn: Eabi; try done.
      specialize (UBS' _ _ _ _ Etb Eabi). done.
    destruct (AS _ _ _ Etb). by rewrite Eabi in *.
  (* All apply buffers succeed *)
  left; constructor.
    intros t bi b Etb. 
    destruct (In_dec peq t l) as [INR | NINR]. 2: by rewrite DOM in Etb.
    specialize (SUCCABI t INR). unfold ABS in SUCCABI. rewrite Etb in SUCCABI.
    destruct (apply_buffer_item bi tso.(tso_mem)); [eexists|]; done.
  intros t bi b m' Etb Eabi.
  destruct (In_dec peq t l) as [INR | NINR]. 2: by rewrite DOM in Etb.
  specialize (SUCCABI t INR). unfold ABS in SUCCABI. 
  by rewrite Etb, Eabi in SUCCABI.
Qed.

(** A more direct definition of the negation of unbuffer-safety. *)

Inductive unbuffer_unsafe : tso_state -> Prop :=
| unbuffer_unsafe_error:
  forall tso tid bi b
    (BEQ : tso_buffers tso tid = bi :: b)
    (ABI : apply_buffer_item bi (tso_mem tso) = None),
    unbuffer_unsafe tso
| unbuffer_unsafe_cons:
  forall tso tid bi b m
    (BEQ : tso_buffers tso tid = bi :: b)
    (ABI : apply_buffer_item bi (tso_mem tso) = Some m)
    (UNS : unbuffer_unsafe (mktsostate (tupdate tid b (tso_buffers tso)) m)),
    unbuffer_unsafe tso.

Lemma unbuffer_unsafe_not_safe :
  forall tso, unbuffer_unsafe tso -> unbuffer_safe tso -> False.
Proof. 
  induction 1; inversion 1; clarify; eauto.
  by edestruct ABIS; try edone; clarify'.
Qed.

Lemma not_unbuffer_safe :
  forall {tso}
    (FS: tso_fin_sup tso)
    (UBS: ~ unbuffer_safe tso),
    unbuffer_unsafe tso.
Proof.
  intros until 1.
  destruct FS as (l & NDUP & DOM).
  remember (buffers_measure l tso.(tso_buffers)) as bsize.
  revert tso Heqbsize DOM.
  induction bsize as [|bsize IH].
  
  (* Base case *)
  intros tso BM DOM UBS. 
  destruct UBS; constructor; intro t;
    destruct (In_dec tid_eq_dec t l) as [IN | NIN];
      (try by rewrite (buffer_measure_zero _ _ _ BM IN));
      by rewrite DOM.

  (* Induction step *)
  intros tso BM DOM UBS.
  (* First see whether there is a thread for which unbuffer fails *)
  set (ABS P X t := 
    match tso.(tso_buffers) t with
      | bi :: rb =>
        match apply_buffer_item bi tso.(tso_mem) with
          | Some m' => 
              P (mktsostate (tupdate t rb tso.(tso_buffers))
                                        m')
          | _ => ~ X
        end
      | _ => X
    end).
  assert (ABSDEC: forall t, {ABS unbuffer_unsafe False t} + {ABS unbuffer_safe True t}).
    intro t.
    destruct (tso.(tso_buffers) t) as [|bi rb] _eqn : Etb.
      by unfold ABS; rewrite Etb; eauto.
    destruct (apply_buffer_item bi tso.(tso_mem)) as [m'|] _eqn: Eabi.
      specialize (IH (mktsostate 
                     (tupdate t rb (tso_buffers tso)) m')).
      destruct (In_dec peq t l) as [INR | NINR]; [|by rewrite DOM in Etb].
      destruct (measure_down_unbuffer _ _ _ _ _ NDUP Etb INR) 
        as [s [BS SBS]].
      rewrite <- BM in SBS; clarify; simpl in *.
      specialize (IH (refl_equal _) (preserve_dom_unbuffer _ _ _ _ _ Etb DOM)).
      unfold ABS; rewrite Etb, Eabi.
      edestruct (unbuffer_safe_dec (mktsostate (tupdate t rb (tso_buffers tso)) m')); eauto.
      by exists l; split; try done; simpl; intros; rewrite tupdate_o; eauto; intro; clarify.
    by unfold ABS; rewrite Etb, Eabi; eauto.
  destruct (strong_in_dec _ _ ABSDEC l) as [[ft [INl FABI]] | SUCCABI].
    (* Some apply buffer fails *)
    unfold ABS in FABI. destruct (tso.(tso_buffers) ft) as [|bi b] _eqn : Etb; try done.
    by destruct (apply_buffer_item bi tso.(tso_mem)) as [|m'] _eqn: Eabi; vauto.
  (* All apply buffers succeed *)
  destruct UBS; constructor.
    intros t bi b Etb. 
    destruct (In_dec peq t l) as [INR | NINR]. 2: by rewrite DOM in Etb.
    specialize (SUCCABI t INR). unfold ABS in SUCCABI. rewrite Etb in SUCCABI.
    by destruct (apply_buffer_item bi tso.(tso_mem)); [eexists|]. 
  intros t bi b m' Etb Eabi.
  destruct (In_dec peq t l) as [INR | NINR]. 2: by rewrite DOM in Etb.
  specialize (SUCCABI t INR). unfold ABS in SUCCABI. 
  by rewrite Etb, Eabi in SUCCABI.
Qed.

Lemma not_unbuffer_unsafe:
  forall {tso}
    (FS: tso_fin_sup tso)
    (UBS: ~ unbuffer_unsafe tso),
    unbuffer_safe tso.
Proof.
  intros; edestruct (unbuffer_safe_dec); eauto. 
  eby elim UBS; eapply not_unbuffer_safe.
Qed.

Lemma unbuffer_unsafe_expose:
  forall {tso}
    (UNS: unbuffer_unsafe tso),
   exists tso', exists tid, exists bi, exists b, 
     taustar (mklts mm_event_labels tso_step) tso tso'
     /\ tso_buffers tso' tid = bi :: b
     /\ apply_buffer_item bi (tso_mem tso') = None.
Proof.
  induction 1; intros; des; clarify; simpl in *; eauto 8 using taustar_refl. 
  repeat eexists; try eapply taustar_trans; try eassumption.
  eapply steptau_taustar; vauto.
Qed.

Lemma unbuffer_safe_expose_alloc1:
  forall {r k tb m m'}
    (UNS : unbuffer_unsafe (mktsostate tb m'))
    (SAFE : unbuffer_safe (mktsostate tb m))
    (A : alloc_ptr r k m = Some m'),
   exists tso',
     taustar (mklts mm_event_labels tso_step) (mktsostate tb m) tso'
     /\ alloc_ptr r k (tso_mem tso') = None.
Proof.
  intros until 1.
  remember (mktsostate tb m') as tso; revert tb m m' Heqtso. 
  induction UNS; intros; clarify; simpl in *.
  Case "base case".
  inv SAFE; destruct (ABIS _ _ _ BEQ) as [b2 B]; simpl in *.
  destruct bi as [p c v|p n k'|p k']; simpl in *.
  - destruct (store_chunk_allocated_someD B) as [(? & ? & ? & ?) ?].
    destruct (store_chunk_allocated_noneD ABI); split; try done.
    eby repeat eexists; try eapply alloc_preserves_allocated.
  - eexists; split; [by eapply steptau_taustar; vauto|]; simpl.
    eby eapply alloc_comm_alloc_none.
  - pose proof (free_cond_spec p k' m') as X'; 
    pose proof (free_cond_spec p k' m); do 2 (destruct free_ptr; try done).
    eby des; edestruct X'; eapply alloc_preserves_allocated.
  Case "ind. step".
  inv SAFE; simpl in *.
  destruct (ABIS _ _ _ BEQ) as [? X].
  exploit IHUNS; try edone.
  - by eapply (UNBS _ _ _ _ BEQ X). 
  - eby eapply alloc_comm_apply_item.
  intros (? & ? & ?); repeat eexists; try eassumption.
  eapply taustar_trans; try eassumption.
  eapply steptau_taustar; vauto.
Qed.

Lemma unbuffer_safe_expose_free1:
  forall {p k tb m m'}
    (UNS : unbuffer_unsafe (mktsostate tb m'))
    (SAFE : unbuffer_safe (mktsostate tb m))
    (A : free_ptr p k m = Some m'),
   exists tso',
     taustar (mklts mm_event_labels tso_step) (mktsostate tb m) tso'
     /\ (match free_ptr p k (tso_mem tso') with
           | None => True
           | Some m' => exists tid', exists p, exists c, exists v, exists b, 
                           tso_buffers tso' tid' = BufferedWrite p c v :: b
                        /\ store_ptr c m' p v = None
         end).
Proof.
  intros until 1.
  remember (mktsostate tb m') as tso; revert tb m m' Heqtso. 
  induction UNS; intros; clarify; simpl in *.
  Case "base case".
  inv SAFE; destruct (ABIS _ _ _ BEQ) as [b2 B]; simpl in *.
  destruct bi as [p' c v|p' n k'|p' k']; simpl in *.
  - destruct (store_chunk_allocated_someD B) as [(? & ? & ? & ?) ?].
    edestruct @free_preserves_allocated; try edone; des; clarify.
    + by destruct (store_chunk_allocated_noneD ABI); split; vauto.
    eby eexists; split; vauto; simpl; rewrite A; repeat eexists.
  - destruct (alloc_someD B); des; destruct (alloc_noneD ABI); des; clarify.
    + by destruct p'; simpl in *; rewrite (restr_of_free A) in *.
    eby edestruct H2; try eapply free_preserves_allocated_back.
  - eexists; split; [by eapply steptau_taustar; vauto|]; simpl.
    destruct (free_ptr p k b2) as [] _eqn: X; clarify.
    by rewrite (free_comm_free _ _ _ _ _ B X A) in ABI. 
  Case "ind. step".
  inv SAFE; simpl in *.
  destruct (ABIS _ _ _ BEQ) as [? X].
  exploit IHUNS; try edone.
  - by eapply (UNBS _ _ _ _ BEQ X).
  - eby eapply free_comm_apply_item. 
  intros (? & ? & ?); repeat eexists; try eassumption.
  eapply taustar_trans; try eassumption.
  eapply steptau_taustar; vauto.
Qed.

Lemma unbuffer_nil_unchanged:
  forall {tid tso tso'}
    (TAU : taustar (mklts mm_event_labels tso_step) tso tso')
    (B : tso_buffers tso tid = nil),
    tso_buffers tso' tid = nil.
Proof.
  induction 1; intros; clarify; inv H; simpl in *.
  destruct (peq tid t); [by subst; rewrite B in *|].
  by rewrite tupdate_o in IHTAU; eauto.
Qed.

Lemma unbuffer_safe_expose_alloc:
  forall {tid p n k tso}
    (SAFE: unbuffer_safe tso)
    (UNS: unbuffer_unsafe (buffer_insert tso tid (BufferedAlloc p n k))),
   exists tso', 
     taustar (mklts mm_event_labels tso_step) tso tso'
     /\ tso_buffers tso' tid = nil
     /\ alloc_ptr (p,n) k (tso_mem tso') = None.
Proof.
  intros; remember (buffer_insert tso tid (BufferedAlloc p n k)) as x.
  destruct tso as [b m]; unfold buffer_insert in *; simpl in *.
  revert b m SAFE Heqx. 
  induction UNS; intros; clarify; simpl in *.

  Case "base".
  inv SAFE; specialize (ABIS tid0); simpl in *.
  destruct (peq tid tid0); subst; rewrite ?tupdate_s, ?tupdate_o in BEQ; try congruence.
  - destruct (b0 tid0) as [] _eqn: B; simpl in *; clarify.
      by eexists; split; [|split]; vauto; simpl; rewrite ABI.
    by destruct (ABIS _ _ (refl_equal _)); clarify'.
  by destruct (ABIS _ _ BEQ); clarify'.
  
  Case "step".
  destruct (peq tid tid0); subst; rewrite ?tupdate_s, ?tupdate_o in BEQ; try congruence.
  - destruct (b0 tid0) as [] _eqn: B; simpl in *; clarify.
    + rewrite tupdate_red, <- B, tupdate_red2 in UNS; simpl in *.
      edestruct @unbuffer_safe_expose_alloc1; des; try edone.
      eby eexists; split; [|split]; try eapply unbuffer_nil_unchanged.
    inv SAFE; pose proof (UNBS tid0 _ _ _ B ABI); try edone. 
    exploit IHUNS; try edone; [by rewrite !tupdate_red, tupdate_s|intro; des].
    eexists; split; [|split]; try eassumption.
    eapply taustar_trans; try eassumption. 
    by eapply steptau_taustar; simpl; vauto.
  inv SAFE; pose proof (UNBS tid0 _ _ _ BEQ ABI); try edone. 
  exploit IHUNS; try edone; [by rewrite tupdate_comm, tupdate_o|intro; des].
  eexists; split; [|split]; try eassumption.
  eapply taustar_trans; try eassumption. 
  by eapply steptau_taustar; simpl; vauto.
Qed.

Lemma unbuffer_safe_expose_free:
  forall {tid p k tso}
    (SAFE: unbuffer_safe tso)
    (UNS: unbuffer_unsafe (buffer_insert tso tid (BufferedFree p k))),
   exists tso', 
     taustar (mklts mm_event_labels tso_step) tso tso'
     /\ tso_buffers tso' tid = nil
     /\ (match free_ptr p k (tso_mem tso') with
           | None => True
           | Some m' => exists tid', exists p, exists c, exists v, exists b, 
                           tso_buffers tso' tid' = BufferedWrite p c v :: b
                        /\ store_ptr c m' p v = None
         end).
Proof.
  intros; remember (buffer_insert tso tid (BufferedFree p k)) as x.
  destruct tso as [b m]; unfold buffer_insert in *; simpl in *.
  revert b m SAFE Heqx. 
  induction UNS; intros; clarify; simpl in *.

  Case "base".
  inv SAFE; specialize (ABIS tid0); simpl in *.
  destruct (peq tid tid0); subst; rewrite ?tupdate_s, ?tupdate_o in BEQ; try congruence.
  - destruct (b0 tid0) as [] _eqn: B; simpl in *; clarify; simpl in *. 
      by eexists; split; [|split]; vauto; simpl; rewrite ABI.
    by destruct (ABIS _ _ (refl_equal _)); clarify'.
  by destruct (ABIS _ _ BEQ); clarify'.
  
  Case "step".
  destruct (peq tid tid0); subst; rewrite ?tupdate_s, ?tupdate_o in BEQ; try congruence.
  - destruct (b0 tid0) as [] _eqn: B; simpl in *; clarify.
    + rewrite tupdate_red, <- B, tupdate_red2 in UNS; simpl in *.
      edestruct @unbuffer_safe_expose_free1; des; try edone.
      eby eexists; split; [|split]; try eapply unbuffer_nil_unchanged.
    inv SAFE; pose proof (UNBS tid0 _ _ _ B ABI); try edone. 
    exploit IHUNS; try edone; [by rewrite !tupdate_red, tupdate_s|intro; des].
    eexists; split; [|split]; try eassumption.
    eapply taustar_trans; try eassumption. 
    by eapply steptau_taustar; simpl; vauto.
  inv SAFE; pose proof (UNBS tid0 _ _ _ BEQ ABI); try edone. 
  exploit IHUNS; try edone; [by rewrite tupdate_comm, tupdate_o|intro; des].
  eexists; split; [|split]; try eassumption.
  eapply taustar_trans; try eassumption. 
  by eapply steptau_taustar; simpl; vauto.
Qed.

Lemma unbuffer_safe_expose_write:
  forall {tid p c v tso}
    (SAFE: unbuffer_safe tso)
    (UNS: unbuffer_unsafe (buffer_insert tso tid (BufferedWrite p c v))),
   exists tso', 
     taustar (mklts mm_event_labels tso_step) tso tso'
     /\ tso_buffers tso' tid = nil
     /\ store_ptr c (tso_mem tso') p v = None.
Proof.
  intros; remember (buffer_insert tso tid (BufferedWrite p c v)) as x.
  destruct tso as [b m]; unfold buffer_insert in *; simpl in *.
  revert b m SAFE Heqx. 
  induction UNS; intros; clarify; simpl in *.

  Case "base".
  inv SAFE; specialize (ABIS tid0); simpl in *.
  destruct (peq tid tid0); subst; rewrite ?tupdate_s, ?tupdate_o in BEQ; try congruence.
  - destruct (b0 tid0) as [] _eqn: B; simpl in *; clarify; simpl in *. 
      by eexists; split; [|split]; vauto; simpl; rewrite ABI.
    by destruct (ABIS _ _ (refl_equal _)); clarify'.
  by destruct (ABIS _ _ BEQ); clarify'.
  
  Case "step".
  destruct (peq tid tid0); subst; rewrite ?tupdate_s, ?tupdate_o in BEQ; try congruence.
  - destruct (b0 tid0) as [] _eqn: B; simpl in *; clarify.
    + rewrite tupdate_red, <- B, tupdate_red2 in UNS; simpl in *.
      destruct (unbuffer_unsafe_not_safe _ UNS).
      eapply unbuffer_safe_arange; try eassumption. 
      eby eapply arange_eq_sym, arange_eq_store.
    inv SAFE; pose proof (UNBS tid0 _ _ _ B ABI); try edone. 
    exploit IHUNS; try edone; [by rewrite !tupdate_red, tupdate_s|intro; des].
    eexists; split; [|split]; try eassumption.
    eapply taustar_trans; try eassumption. 
    by eapply steptau_taustar; simpl; vauto.
  inv SAFE; pose proof (UNBS tid0 _ _ _ BEQ ABI); try edone. 
  exploit IHUNS; try edone; [by rewrite tupdate_comm, tupdate_o|intro; des].
  eexists; split; [|split]; try eassumption.
  eapply taustar_trans; try eassumption. 
  by eapply steptau_taustar; simpl; vauto.
Qed.

Lemma tso_step_write_fail:
  forall {tid p c v tso}
    (SAFE: unbuffer_safe tso)
    (UNS: unbuffer_unsafe (buffer_insert tso tid (BufferedWrite p c v))),
   exists tso', taustep (mklts mm_event_labels tso_step) tso (MMreadfail tid p c) tso'.
Proof.
  intros; destruct (unbuffer_safe_expose_write SAFE UNS) as (tso' & TAU & Bemp & STO).
  eexists; eexists; split; try edone. 
  econstructor; try edone. 
  pose proof (store_chunk_allocated_noneD STO).
  pose proof (load_chunk_allocated_spec c (tso_mem tso') p).
  by destruct load_ptr.
Qed.

Lemma tso_step_free_fail2:
  forall {tid p k tso}
    (SAFE: unbuffer_safe tso)
    (UNS: unbuffer_unsafe (buffer_insert tso tid (BufferedFree p k))),
   exists tso', taustep (mklts mm_event_labels tso_step) tso (MMfreefail tid p k) tso'.
Proof.
  intros; destruct (unbuffer_safe_expose_free SAFE UNS) as (tso' & TAU & Bemp & STO).
  eexists; eexists; split; try edone; vauto.
Qed.

Lemma tso_step_preserves_unbuffer_safety:
  forall tso tso' e,
    tso_step tso e tso' ->
    unbuffer_safe tso ->
    unbuffer_safe tso'.
Proof.
  intros tso tso' e TSTEP.
  (tso_step_cases (case TSTEP) Case); try done; 
    try by intros [].
  Case "tso_step_unbuffer".
    intros t' [] bufs' bi b m' BD -> ABI US.
    eby eapply apply_item_unbuffer_safe.
  Case "tso_step_rmw".
    intros []; intros; subst; simpl in *.
    eapply unbuffer_safe_arange; try eassumption.
    eby eapply arange_eq_sym, arange_eq_store.
  Case "tso_step_start".
    intros []; intros; subst.
    by apply unbuffer_safe_tupdate_nil.
Qed.


Lemma tso_machine_can_unbuffer:
  forall {tso}
    (UNB: unbuffer_safe tso) {t bi b}
    (EQ: tso.(tso_buffers) t = bi :: b),
    exists tso', tso_step tso MMtau tso'.
Proof.
  intros; destruct UNB as [tso ABI' UBS'].
  specialize (ABI' t).
  destruct (ABI' _ _ EQ) as [m' ABI].
  eby eexists; eapply tso_step_unbuffer. 
Qed.

Definition alloc_fresh (tso : tso_state) 
                       (t : thread_id)
                       (r : arange)
                       (k : mobject_kind) : Prop :=
  let (p, n) := r in
    unbuffer_safe (buffer_insert tso t (BufferedAlloc p n k)).


Lemma tso_machine_can_move:
  forall e t tso,
    tso_fin_sup tso ->
    unbuffer_safe tso ->
    tso_buffers tso t = nil ->
    exists tso', 
      taustep (mklts mm_event_labels tso_step) tso (MMmem t e) tso' \/
(*      tso_step tso MMtau tso' \/ *)
    (exists p, exists c, exists v,
      taustep (mklts mm_event_labels tso_step) tso (MMreadfail t p c) tso' /\
      e = MEwrite p c v) \/
    (exists p, exists k,
      taustep (mklts mm_event_labels tso_step) tso (MMfreefail t p k) tso' /\
      e = MEfree p k) \/
    (exists p, exists c, exists v, exists v',
      taustep (mklts mm_event_labels tso_step) tso (MMmem t (MEread p c v')) tso' /\
      te_samekind (TEmem (MEread p c v')) (TEmem (MEread p c v)) /\
      e = MEread p c v) \/
    (exists p, exists c, exists v,
      taustep (mklts mm_event_labels tso_step) tso (MMreadfail t p c) tso' /\
      e = MEread p c v) \/
    (exists p, exists i, exists k, 
      ~ alloc_fresh tso t (p, i) k /\
      e = MEalloc p i k) \/
    (exists p, exists c, exists v, exists v', exists f,
      taustep (mklts mm_event_labels tso_step) tso (MMmem t (MErmw p c v' f)) tso' /\
      te_samekind (TEmem (MErmw p c v' f)) (TEmem (MErmw p c v f)) /\
      e = MErmw p c v f) \/
    (exists p, exists c, exists v, exists f, 
      taustep (mklts mm_event_labels tso_step) tso (MMreadfail t p c) tso' /\
      e = MErmw p c v f).
Proof.
  intros e t tso FINSUP SAFE (*Ebft*).
  destruct (tso.(tso_buffers) t) as [] _eqn: Ebft.
  2: by edestruct @tso_machine_can_unbuffer; eauto.
  destruct tso as [bf m]. simpl in Ebft.
  mem_event_cases (destruct e as [|p c v|p c v|p c v f|p s k|p k]) Case.
  Case "MEfence". 
  by eexists; left; eapply step_taustep,tso_step_mfence.
  Case "MEwrite".
  assert (FS := fin_sup_buffer_insert t (BufferedWrite p c v) _ FINSUP).
  destruct (unbuffer_safe_dec _ FS) as [WS | WUS].
    eby eexists; left; eapply step_taustep,tso_step_write.
  by destruct (tso_step_write_fail SAFE (not_unbuffer_safe FS WUS)); eauto 10.
  Case "MEread".
  exists (mktsostate bf m).
  destruct (load_ptr c m p) as [v'|] _eqn : LDRES.
  right; right; right; left. 
  exists p; exists c; exists v; exists v'.
  split; try reflexivity.
  assert (AEB: apply_buffer (tso_buffers (mktsostate bf m) 
                                         t) m = Some m).
    by simpl; rewrite Ebft; auto.
  apply step_taustep, (tso_step_read _ t _ p c v' AEB LDRES).
  - eby repeat split; intros; destruct p; eapply load_wt.
  do 4 right; left. 
  exists p; exists c; exists v; split; try reflexivity. 
  eapply step_taustep,tso_step_read_fail; try eassumption.
  Case "MErmw".
  destruct (load_ptr c m p) as [v'|] _eqn : LDRES.
    destruct (store_ptr c m p (rmw_instr_semantics f v')) as [m'|] _eqn : STRES.
    2: by generalize (load_chunk_allocated_someD LDRES),
                  (store_chunk_allocated_noneD STRES).
    eexists; do 6 right; left; do 6 eexists; try done; try eapply step_taustep,tso_step_rmw; eauto.
    by repeat split; destruct p; eauto using @load_wt.
  eby eexists; do 7 right; do 6 eexists; vauto.
  Case "MEalloc".
  set (ntso := mktsostate (tupdate t (bf t ++ BufferedAlloc p s k :: nil) bf) m).
  exists ntso.
  assert (FS := fin_sup_buffer_insert t (BufferedAlloc p s k) _ FINSUP).
  destruct (unbuffer_safe_dec _ FS) as [AS | AUS].
    left. eby eapply step_taustep,tso_step_alloc; edone.
  by do 5 right; left; repeat eexists.
  Case "MEfree".
  assert (FS := fin_sup_buffer_insert t (BufferedFree p k) _ FINSUP).
  destruct (unbuffer_safe_dec _ FS) as [WS | WUS].
    eby eexists; left; eapply step_taustep,tso_step_free. 
  by destruct (tso_step_free_fail2 SAFE (not_unbuffer_safe FS WUS)); eauto 10.
Qed.

Lemma unbuffer_to_mm_tsopc:
  forall stso t,
    unbuffer_safe stso -> 
    exists m', apply_buffer (stso.(tso_buffers) t) stso.(tso_mem) = Some m' /\
    taustar (mklts mm_event_labels tso_step) stso 
       (mktsostate (tupdate t nil stso.(tso_buffers)) m').
Proof.
  induction 1; simpl in *.
  destruct (tso_buffers tso t) as [] _eqn: EQ.
  - eexists; split; try done.
    by rewrite <- EQ, tupdate_red2; destruct tso; vauto.
  specialize (ABIS _ _ _ EQ); des; simpl; rewrite ABIS; simpl.
  exploit H; eauto; []; rewrite tupdate_s, tupdate_red; intros; simpl; des.
  by eexists; split; vauto.
Qed.

(** Package as a memory model. *)
Program Definition tso_mm := 
  {| MM_init := tso_init ; 
     MM_step := tso_step ;
     MM_inv a s := (forall tid (EQ: a ! tid = None), tso_buffers s tid = nil) /\ unbuffer_safe s
   |}.
Solve Obligations using done.
(* Solve Obligations using eauto using tso_step_preserves_unbuffer_safety. *)
Next Obligation.
  split; eauto using tso_step_preserves_unbuffer_safety.
  intros; inv STEP; des; try done; 
    unfold buffer_insert; simpl; clarify; eauto;
      try (by rewrite tupdate_o; try intro; clarify'; eauto).

  - by unfold tupdate; destruct peq; eapply H in EQ; clarify'.
  - by unfold tupdate; destruct peq; clarify'; eapply H; rewrite PTree.gso in *.
  - by rewrite PTree.grspec in *; destruct PTree.elt_eq; clarify'; eauto.
Qed.
Next Obligation.
  inv STEP; clarify; rewrite H in *; clarify; apply PTree.gempty.
Qed.
Next Obligation.
  destruct e as [tid m| | | | | | ]; clarify.
  + destruct (unbuffer_to_mm_tsopc _ tid H0) as (m' & AB & TAU).
    destruct s as [b mem]; eapply (apply_buffer_unbuffer_safe tid _ nil) in H0; eauto using app_nil_end.
    exploit (tso_machine_can_move m tid); eauto.
    - clear - a H; revert a H; intros.
      exists (List.map (@fst _ _) (PTree.elements a)).
      split; eauto using PTree.elements_keys_norepet.
      intros t NIN. simpl. 
      unfold tupdate; destruct peq; clarify; apply H. 
      destruct (a ! t) as [|ts] _eqn: E; try done.
      apply PTree.elements_correct in E.
      by elim NIN; apply in_map_iff; exists (t, u). 
    - by apply tupdate_s.
    intros; des; clarify; eauto 8 using taustar_taustep.
    - by destruct m; eauto 10 using taustar_taustep.
    - (* NB: Classical reasoning used *)
      destruct (classic (exists p', exists s', tso_step (mktsostate (tupdate tid nil b) m') (MMmem tid (MEalloc p' i k)) s')).
      des; eauto 8 using taustar_taustep, step_taustep.
      eexists; right; eexists; split; [edone|].
      by econstructor; try red; eauto using tso_step.
 + by eexists; eapply step_taustep; econstructor; eauto. 
 + eapply (unbuffer_to_mm_tsopc _ tid) in H0; des.
   by eexists; eexists; split; [edone|econstructor; eapply tupdate_s].
Qed.
Next Obligation. by inv STEP. Qed.


Lemma tso_pure_load_condition:
  MM_pure_load_condition tso_mm.
Proof.
  red; intros.
  destruct (unbuffer_to_mm_tsopc s tid (proj2 INV)) as (m' & AB & TAU).
  destruct (load_ptr c m' p) as [v'|] _eqn : LDRES.
  - by simpl; destruct p; eauto 8 using tso_step, @load_wt.
  by right; do 3 eexists; eauto; econstructor; try eapply tupdate_s.
Qed.


(** ** Properties of the composition with a thread semantics *)

Module TSO.

Section TSOsemantics.

Variable Sem : SEM.
Variable ge : SEM_GE Sem.

Notation state := (Comp.state tso_mm Sem).
Notation step := (Comp.step tso_mm Sem ge).

Lemma partial_unbuffer_to_tsopc:
  forall stso t m' sthr B1 B2,
    stso.(tso_buffers) t = B1 ++ B2 ->
    apply_buffer B1 stso.(tso_mem) = Some m' ->
    taustar (mklts event_labels step) (stso, sthr) 
       (mktsostate (tupdate t B2 stso.(tso_buffers)) m', sthr).
Proof.
  intros [b m] t m' sthr B1 B2; simpl in *.
  revert b m; induction B1 as [|bh bt IH]; simpl; intros b m EQ AB; clarify.
    by rewrite tupdate_red2; constructor.
  destruct (optbind_someD AB) as (mt & EQ' & AB').
  specialize (IH (tupdate t (bt ++ B2) b) mt); rewrite tupdate_s, tupdate_red in IH.
  eapply taustar_step; simpl; [|apply IH]; try edone.  
  eby eapply Comp.step_unbuf; eapply tso_step_unbuffer.
Qed.

Lemma unbuffer_to_tsopc:
  forall stso t m' sthr,
    apply_buffer (stso.(tso_buffers) t) stso.(tso_mem) = Some m' ->
    taustar (mklts event_labels step) (stso, sthr) 
       (mktsostate (tupdate t nil stso.(tso_buffers)) m', sthr).
Proof.
  intros; eapply partial_unbuffer_to_tsopc; try eassumption.
  by apply app_nil_end.
Qed.

Lemma unbuffer_to_tsopc2:
  forall {tso tso'} thr
    (TAU: taustar (mklts mm_event_labels tso_step) tso tso'),
    taustar (mklts event_labels step) (tso,thr) (tso',thr).
Proof.
  induction 1; vauto.
Qed.

Lemma partial_unbuffer_ne_to_tsopc:
  forall stso t m' sthr B1 B2
    (EQ: stso.(tso_buffers) t = B1 ++ B2)
    (NEQ: B1 <> nil)
    (AB: apply_buffer B1 stso.(tso_mem) = Some m'),
    taustep (mklts event_labels step) (stso, sthr) Etau
       (mktsostate (tupdate t B2 stso.(tso_buffers)) m', sthr).
Proof.
  intros [b m]; intros. 
  destruct B1; try done; simpl in *.
  destruct (optbind_someD AB) as (mt & EQ' & AB').
  eapply steptau_taustar_taustep.
    eby eapply Comp.step_unbuf; eapply tso_step_unbuffer. 
  eby exploit (partial_unbuffer_to_tsopc (mktsostate (tupdate t (B1 ++ B2) b) mt) t); 
    simpl; try edone; try apply tupdate_s; rewrite tupdate_red. 
Qed.

Definition buffers_consistent (s : state) : Prop :=
  forall t, (snd s) ! t = None -> (fst s).(tso_buffers) t = nil.

Lemma tso_tau_preserves_buffer_consistency:
  forall s s' th
    (ST: tso_step s MMtau s')
    (C: buffers_consistent (s, th)),
    buffers_consistent (s', th).
Proof.
  inversion 1; clarify; intros C t' N; specialize (C t' N). 
  simpl in *; unfold tupdate; destruct peq; clarify'.
Qed.

Lemma tso_step_preserves_buffer_consistency:
  forall s t e s' th ts,
    tso_step s e s' ->
    match e with
    | MMmem t' _ => t' = t
    | MMstart _ _ => False
    | MMtau =>  False
    | _ => True
    end ->
    th ! t = Some ts ->
    buffers_consistent (s, th) ->
    buffers_consistent (s', th).
Proof.
  intros until 2; destruct e; clarify; inv H;
  try (unfold buffers_consistent; simpl;
    intros TST C t' H; unfold tupdate; destruct (peq t' t) as [-> | N];
      [rewrite H in * | apply C]; done); try done.
Qed.

Lemma thread_update_preserves_buffer_consistency:
  forall s t th ts',
    buffers_consistent (s, th) ->
    buffers_consistent (s, th ! t <- ts').
Proof.
  intros s t th ts' C t'. simpl.
  destruct (peq t' t) as [-> | N].
  rewrite PTree.gss. done.
  rewrite PTree.gso; [intro; apply C |]; done.
Qed.

Lemma thread_start_preserves_buffer_consistency:
  forall tso newtid st
    (C : buffers_consistent (tso, st)),
   buffers_consistent
     (mktsostate (tupdate newtid nil (tso_buffers tso))
        (tso_mem tso), st).
Proof.
  intros.
  intro t'. simpl. unfold tupdate.
  destruct (peq t' newtid) as [-> | N]; try done. intro X. by apply C.
Qed.

Lemma tso_arglist_tso_eq:
  forall {tso tid largs args tso'}
  (MA : Comp.mm_arglist tso_mm tso tid largs args tso'),
  tso' = tso.
Proof. by intros; induction MA; try inv RD. Qed.

Lemma tso_ext_arglist_tso_eq:
  forall {tso tid largs args tso'}
  (MA : Comp.mm_ext_arglist tso_mm tso tid largs args tso'),
  tso' = tso.
Proof. by intros; induction MA; try inv RD. Qed.


Lemma buffer_cons_impl_fin_sup:
  forall tso s,
     buffers_consistent (tso, s) -> tso_fin_sup tso.
Proof.
  intros tso thr TSOC.
  exists (List.map (@fst thread_id _) (PTree.elements thr)).
  split. apply PTree.elements_keys_norepet.
  intros t NIN. apply TSOC.
  destruct (thr ! t) as [|ts] _eqn: E; try done.
  apply PTree.elements_correct in E.
  elim NIN.
  apply (proj2 (in_map_iff _ _ _)). 
  by exists (t, s). 
Qed.


Lemma tso_cons_impl_fin_sup:
  forall s,
     Comp.consistent tso_mm Sem s -> tso_fin_sup (fst s).
Proof.
  intros [tso thr] [BC _].
  eapply buffer_cons_impl_fin_sup; red; simpl; intros ? H.
  by apply BC; rewrite PTree.gmap; rewrite H.
Qed.

Lemma taustep_write_fail: 
  forall {s s' tid tso st p c v}
    (tidSTEP: SEM_step Sem ge s (TEmem (MEwrite p c v)) s')
    (UNS: ~ unbuffer_safe (buffer_insert tso tid (BufferedWrite p c v)))
    (Gtid: st ! tid = Some s)
    (CONS: Comp.consistent tso_mm Sem (tso, st)),
  exists m, taustep (mklts event_labels step) (tso, st) (Evisible Efail) m.
Proof.
  intros; eapply not_unbuffer_safe in UNS;
    [|by eapply fin_sup_buffer_insert, (tso_cons_impl_fin_sup _ CONS)].
  destruct (tso_step_write_fail (proj2 CONS) UNS) as (? & ? & ? & ?).
  eexists (_, _); eexists; split; [eby eapply unbuffer_to_tsopc2|]; vauto.
Qed.

Lemma taustep_free_fail: 
  forall {s s' tid tso st p k}
    (tidSTEP: SEM_step Sem ge s (TEmem (MEfree p k)) s')
    (UNS: ~ unbuffer_safe (buffer_insert tso tid (BufferedFree p k)))
    (Gtid: st ! tid = Some s)
    (CONS: Comp.consistent tso_mm _ (tso, st)),
  exists m, taustep (mklts event_labels step) (tso, st) (Evisible Efail) m.
Proof.
  intros; eapply not_unbuffer_safe in UNS;
    [|by eapply fin_sup_buffer_insert, (tso_cons_impl_fin_sup _ CONS)].
  destruct (tso_step_free_fail2 (proj2 CONS) UNS) as (? & ? & ? & ?).
  eexists (_, _); eexists; split; [eby eapply unbuffer_to_tsopc2|]; vauto.
Qed.

Lemma apply_buffer_reachable_preserves_tso_consistency:
  forall t tso b tso' thrs,
    apply_buffer_reachable t tso b tso' ->
    Comp.consistent tso_mm Sem (tso, thrs) ->
    Comp.consistent tso_mm Sem (tso', thrs).
Proof.
  intros t tso b tso' thrs ABR.
  induction ABR. done.
  subst. 
  intros [BC US]. apply IHABR.
  split. intros t' N'; simpl in *. specialize (BC t' N'). 
    unfold tupdate; destruct (peq t' t) as [-> | Nt]; by try rewrite BC in *.
  simpl. destruct tso; simpl in *; eby eapply apply_item_unbuffer_safe.
Qed.

Lemma apply_buffer_reachable_taustar:
  forall t tso b tso' thrs,
    apply_buffer_reachable t tso b tso' ->
    taustar (mklts event_labels step) (tso, thrs) (tso', thrs).
Proof.
  induction 1; subst; [by apply taustar_refl|].
  eapply taustar_step; try edone; simpl. 
  eby eapply Comp.step_unbuf, tso_step_unbuffer.
Qed.

Lemma apply_buffer_reachable_taustep:
  forall t tso b tso' thrs,
    b <> nil ->
    apply_buffer_reachable t tso b tso' ->
    taustep (mklts event_labels step) (tso, thrs) Etau (tso', thrs).
Proof.
  intros t tso b tso' thrs NE ABR.

  destruct b as [|bi b]; try done. 
  inv ABR.
  eapply (@steptau_taustar_taustep _ (mklts event_labels step) _ (_, _)).
    simpl. eapply Comp.step_unbuf. 
    eby eapply tso_step_unbuffer.
  eby eapply apply_buffer_reachable_taustar.
Qed.

Lemma unbuffer_to_tso_state:
  forall b br t tso m',
    (tso.(tso_buffers) t) = b ++ br ->
    apply_buffer b tso.(tso_mem) = Some m' ->
    exists tso',
      apply_buffer_reachable t tso b tso' /\
      tso'.(tso_buffers) t = br /\
      (forall t', t' <> t -> tso'.(tso_buffers) t' = tso.(tso_buffers) t') /\
      tso'.(tso_mem) = m'.
Proof.
  induction b as [|bi bir IH]; simpl; intros br t tso m' BD AB. 
  exists tso. inv AB.
  by split; [apply apply_buffer_reachable_refl | repeat (split; try done)].

  destruct (apply_buffer_item bi tso.(tso_mem)) as [mi|] _eqn : ABI;
    try done.
  simpl in AB.

  set (ntso := mktsostate (tupdate t (bir ++ br) tso.(tso_buffers))
                          mi).
  assert (ntsobuf : tso_buffers ntso t = bir ++ br).
    by simpl; unfold tupdate; destruct (peq t t).
  assert (ABIi: apply_buffer bir (tso_mem ntso) = Some m') by done.
  destruct (IH _ _ _ _ ntsobuf ABIi) 
    as (tso' & ABR & TB & TBO & MEM).
  exists tso'; repeat split; try done.
  - eby refine (apply_buffer_reachable_step _ _ _ _ _ _ _ _ _ _ _ ABR).
  intros t' N. specialize (TBO _ N). simpl in TBO; unfold tupdate in TBO.
  by destruct (peq t' t) as [-> | NE].
Qed.

End TSOsemantics.

End TSO.

(** Additional results about the TSOmachine. *)

Section TSOresults.

  Variables (Sem : SEM).
  Let tsolts ge := (mklts event_labels (Comp.step tso_mm Sem ge)).
  Let lts ge := (mklts thread_labels (SEM_step Sem ge)).

  Hint Constructors tso_step : myhints.
  Hint Constructors Comp.mm_arglist : myhints.
  Hint Constructors Comp.mm_arglist_fail : myhints.
  Hint Constructors Comp.mm_ext_arglist : myhints.
  Hint Constructors Comp.mm_ext_arglist_fail : myhints.
  Hint Constructors Val.lessdef_list.
  Hint Unfold tso_mm.
  Hint Extern 1 (MM_step tso_mm _ _ _) => simpl.

  Lemma tso_arglist_dec:
    forall tso t locs
      (BE : tso.(tso_buffers) t = nil), 
      Comp.mm_arglist_fail tso_mm tso t locs \/
      exists vals, exists tso', Comp.mm_arglist tso_mm tso t locs vals tso'.
  Proof.
    intros; induction locs as [|[[p c]|v] locs IH]; eauto with myhints;
    destruct IH as [IH|[vals [tso' IH]]]; eauto with myhints;
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

  Lemma ptree_empty_dec:
    forall (A : Type) (m : @PTree.t A),
      {exists i, exists s, PTree.get i m = Some s} + {forall i, PTree.get i m = None}.
  Proof.
    intros; destruct (PTree.elements m) as [|[i s] t] _eqn : Els.
      right; intro i; destruct (m!i) as [e|] _eqn:E; try done.
      by apply PTree.elements_correct in E; rewrite Els in E.
    left; exists i; exists s; apply PTree.elements_complete.
    by rewrite Els; left.
  Qed.

  Lemma stuck_tso_impl_empty_buffers:
    forall {ge s}
      (TSOC: Comp.consistent tso_mm Sem s)
      (TSTUCK: forall s' l', ~ Comp.step _ _ ge s l' s'),
      forall t, (fst s).(tso_buffers) t = nil.
  Proof.
    intros.
    destruct ((fst s).(tso_buffers) t) as [|bh bt] _eqn:Ebft; try done.
    destruct s as [tso thr].
    destruct (tso_machine_can_unbuffer (proj2 TSOC) Ebft) as [tso' TAU].
    elim(TSTUCK (tso', thr) Etau).
    eapply Comp.step_unbuf, TAU.
  Qed.


End TSOresults.
