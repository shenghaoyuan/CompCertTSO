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
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Representation of observable events and execution traces. *)

Require Import Coqlib.
Require Import Ast.
Require Import Integers.
Require Import Floats.
Require Import Pointers.
Require Import Values.
Require Import Libtactics.

(** The observable behaviour of programs is stated in terms of
  input/output events, which can also be thought of as system calls 
  to the operating system.  An event is generated each time an
  external function (see module Ast) is invoked.  The event records
  the name of the external function, the arguments to the function
  invocation provided by the program, and the return value provided by
  the outside world (e.g. the operating system).  Arguments and values
  are either integers or floating-point numbers.  We currently do not
  allow pointers to be exchanged between the program and the outside
  world. *)

Inductive eventval :=
  | EVint   (i: int)
  | EVfloat (f: float).

Inductive event :=
  | Ecall   (fn: ident) (args: list eventval)
  | Ereturn (ty: typ) (res: eventval)
  | Eexit   (i: int)
  | Efail.

Inductive fullevent :=
  | Evisible (ev: event)
  | Etau
  | Eoutofmemory.

Lemma event_dec:
  forall (x y : event), {x = y} + {x <> y}.
Proof. repeat (decide equality; auto using Float.eq_dec, Int.eq_dec). Qed.

Lemma fullevent_dec:
  forall (x y : fullevent), {x = y} + {x <> y}.
Proof. decide equality; auto using event_dec. Qed.

Definition val_of_eval (e : eventval) :=
  match e with
  | EVint i => Vint i
  | EVfloat f => Vfloat f
  end.

Definition eval_of_val (e: val) : option eventval :=
  match e with
    | Vint i => Some (EVint i)
    | Vfloat f => Some (EVfloat f)
    | _ => None
  end.

Definition event_samekind (e1 e2 : fullevent) :=
  match e1, e2 with
  | Evisible (Ereturn t1 rv1), Evisible (Ereturn t2 rv2) => 
      t1 = t2 /\ 
      (Val.has_type (val_of_eval rv2) t2 -> 
       Val.has_type (val_of_eval rv1) t1)
  | _, _ => e1 = e2
  end.

(** * Read-modify-write instructions *)

Inductive rmw_instr :=
   | rmw_ADD (v: val)
   | rmw_CAS (vold vnew: val)
   | rmw_SET (v: val).

Lemma rmw_instr_dec (x y: rmw_instr): {x = y} + {x <> y}.
Proof. decide equality; auto using Val.eq_dec. Qed.

Definition rmw_instr_semantics (i : rmw_instr) (v : val) : val :=
  match i with
    | rmw_ADD v' => Val.add v v'
    | rmw_CAS vold vnew =>
        if Val.eq_dec vold Vundef || Val.eq_dec v Vundef 
          then Vundef
          else if Val.eq_dec vold v 
            then vnew
            else v
    | rmw_SET v' => v'
  end.

Lemma rmw_lessdef: 
  forall {v v'} i
    (LT: Val.lessdef v v'),
    Val.lessdef (rmw_instr_semantics i v) (rmw_instr_semantics i v').
Proof.
  inversion 1; clarify.
  destruct i; try done.
  simpl. by destruct vold; repeat destruct Val.eq_dec.
Qed.

(** Between compilation passes, we also keep track of memory events.
  The memory events include read, write, read-modify-write, allocation, deallocation, 
   *)
  
Inductive mem_event :=
  | MEfence
  | MEwrite (p: pointer) (chunk: memory_chunk) (v: val)
  | MEread  (p: pointer) (chunk: memory_chunk) (v: val)
  | MErmw   (p: pointer) (chunk: memory_chunk) (v: val) (instr: rmw_instr)
  | MEalloc (p: pointer) (size: int) (k: mobject_kind)
  | MEfree  (p: pointer) (k: mobject_kind).

Definition thread_id := positive.
Lemma tid_eq_dec (x y : thread_id): {x = y} + {x <> y}.
Proof. decide equality. Qed.

(** Thread transitions are labelled by thread events. These can be 
    either external events, memory events, silent action, thread
    exit or thread start events. The [MEstart t f v] event  stands 
    for an invocation of [pthread_create] of function [f] with the 
    value [v] passed to the thread's function (i.e., [f]). Note
    that the events following an [TEexit] event are ignored. 
    (The same applies to [TEext Eexit] and [TEext Efail] events.) *)
Inductive thread_event :=
  | TEext (ev: event)
        (**r externally observable event *)
  | TEmem (ev: mem_event)
        (**r memory event *)
  | TEtau
        (**r thread-local event *)
  | TEexit
        (**r normal exit *)
  | TEstart (p: pointer) (vs: list val)
        (**r thread start (bootstrap) *)
  | TEexternalcallmem (i: ident) (l: list (pointer * memory_chunk + eventval))
        (**r external call action with arguments in memory *)
  | TEstartmem (f: pointer * memory_chunk + val)
               (args: list (pointer * memory_chunk + val))
        (**r thread start action with arguments in memory *)
  | TEoutofmem.

Lemma event_eq_dec: forall (x y : event), {x = y} + {x <> y}.
Proof. repeat (decide equality; auto using Val.eq_dec, Float.eq_dec, Int.eq_dec). Qed.

Lemma mem_event_eq_dec: forall (x y : mem_event), {x = y} + {x <> y}.
Proof. repeat (decide equality; auto using Float.eq_dec, Int.eq_dec, Val.eq_dec). Qed.

Lemma thread_event_eq_dec: forall (x y : thread_event), {x = y} + {x <> y}.
Proof. repeat (decide equality; auto using event_eq_dec, mem_event_eq_dec, 
                                      MPtr.eq_dec, Float.eq_dec, Int.eq_dec).
Qed.

Definition te_wt (e : thread_event) : Prop :=
  match e with
  | TEmem(MEread p c v)  => Val.has_type v (type_of_chunk c)
  | TEmem(MEwrite p c v) => Val.has_type v (type_of_chunk c)
  | _ => True
  end.

Definition te_samekind (e1 e2 : thread_event) : Prop :=
  match e1, e2 with
  | TEmem(MEread p1 c1 v1), TEmem(MEread p2 c2 v2) => p1 = p2 /\ c1 = c2 
          /\ (Val.has_type v2 (type_of_chunk c2) -> 
              Val.has_type v1 (type_of_chunk c1))
  | TEmem(MErmw p1 c1 v1 f1), TEmem(MErmw p2 c2 v2 f2) => p1 = p2 /\ c1 = c2 /\ f1 = f2
          /\ (Val.has_type v2 (type_of_chunk c2) -> 
              Val.has_type v1 (type_of_chunk c1))
  | TEmem(MEalloc p1 s1 k1), TEmem(MEalloc p2 s2 k2)   => s1 = s2 /\ k1 = k2 
  | TEext(Ereturn t1 rv1),  TEext (Ereturn t2 rv2) => t1 = t2 /\ 
      (Val.has_type (val_of_eval rv2) t2 -> 
       Val.has_type (val_of_eval rv1) t1) 
  | _, _ => e1 = e2
  end.

(** Less defined comparison in output values.
    In essence, this only relates write of an undefined value to a write
    of defined value to the same memory location. *)
Definition te_ldo (e1 e2 : thread_event) : Prop :=
  match e1, e2 with
  | TEmem(MEwrite p1 c1 v1), TEmem(MEwrite p2 c2 v2) => p1=p2 /\ c1=c2 /\ 
        Val.lessdef v1 v2
  | TEstart p1 v1, TEstart p2 v2 => p1=p2 /\ Val.lessdef_list v1 v2 
  | TEstartmem p1 a1, TEstartmem p2 a2 => p1=p2 /\ Val.lessdef_listsum a1 a2
  | _, _ => False
  end.

(** Less defined comparison in input labels. Note that unlike
    [ldo], [ldi] is reflexive. *)
Definition te_ldi (e1 e2 : thread_event) : Prop :=
  match e1, e2 with
  | TEmem(MEread p1 c1 v1), TEmem(MEread p2 c2 v2) => p1=p2 /\ c1=c2 /\ 
                                                      Val.lessdef v1 v2
  | TEmem(MErmw p1 c1 v1 f1), TEmem(MErmw p2 c2 v2 f2) => p1=p2 /\ c1=c2 /\ f1=f2 /\
                                                      Val.lessdef v1 v2
  | _, _ => e1 = e2
  end.

Lemma ldo_samekind_eq: 
  forall l1 l2 l, te_samekind l1 l2 -> te_ldo l l2 -> l1 = l2.
Proof.
  by intros;
     destruct l1 as [[]|[]| | | | | |]; destruct l2 as [[]|[]| | | | | |]; 
     destruct l as [[]|[]| | | | | |].
Qed.

Lemma ldo_not_tau: forall l1, te_ldo l1 TEtau -> False.
Proof. by intros; destruct l1 as [[]|[]| | | | | |]. Qed.

Lemma ldi_refl: forall l, te_ldi l l.
Proof. by intros; destruct l as [[]|[]| | | | | |]. Qed.

(** Basic facts about val_of_eval *)
Lemma val_of_eval_eq:
  forall {ev ev'},
    val_of_eval ev = val_of_eval ev' ->
    ev = ev'.
Proof.
  by intros; destruct ev; destruct ev'; clarify.
Qed.

Lemma map_val_of_eval_eq:
  forall {evs evs'},
    map val_of_eval evs = map val_of_eval evs' -> evs = evs'.
Proof.
  intros evs. 
  induction evs; intros [] E; try done.
  inv E; f_equal; eauto using @val_of_eval_eq. 
Qed.

Lemma lessdef_val_of_eval:
  forall ev v,
    Val.lessdef (val_of_eval ev) v -> v = val_of_eval ev.
Proof.
  by intros ev v LD; destruct ev; inv LD.
Qed.

Lemma lessdef_map_val_of_eval:
  forall ev v,
    Val.lessdef_list (map val_of_eval ev) v -> v = map val_of_eval ev.
Proof.
  induction ev; intros v LD. inv LD. done.
  inv LD. by rewrite (lessdef_val_of_eval a v2), (IHev vl2).
Qed.

(** Lifting val_of_val to external argument list *)
Definition val_of_eval_memarg (ev : pointer * memory_chunk + eventval) 
                            : pointer * memory_chunk + val :=
  match ev with 
    | inl pc => inl _ pc
    | inr v => inr _ (val_of_eval v)
  end.

Definition cast_value_to_chunk (c : memory_chunk) (v: val) := 
  match c, v with
  | Mint8signed, Vint n    => Vint (Int.zero_ext 8 n)
  | Mint8unsigned, Vint n  => Vint (Int.zero_ext 8 n)
  | Mint16signed, Vint n   => Vint (Int.zero_ext 16 n)
  | Mint16unsigned, Vint n => Vint (Int.zero_ext 16 n)
  | Mint32, Vint n         => Vint n
  | Mint32, Vptr p         => Vptr p
  | Mfloat32, Vfloat f => Vfloat(Float.singleoffloat f)
  | Mfloat64, Vfloat f => Vfloat f
  | _, _ => Vundef
  end.

Lemma cast_value_to_chunk_lessdef:
  forall c v v'
    (LD : Val.lessdef v v'),
      Val.lessdef (cast_value_to_chunk c v) (cast_value_to_chunk c v').
Proof.
  intros. inv LD. done. 
  by destruct c.
Qed.

Inductive mm_event :=
  | MMmem       (tid: thread_id) (m: mem_event)
  | MMreadfail  (tid: thread_id) (p: pointer) (c: memory_chunk)
  | MMfreefail  (tid: thread_id) (p: pointer) (k: mobject_kind)
  | MMoutofmem  (tid: thread_id) (i: int) (k: mobject_kind)
  | MMstart     (tid: thread_id) (newtid: thread_id)
  | MMexit      (tid: thread_id)
  | MMtau.

Lemma mm_event_dec (x y: mm_event) : {x = y} + {x<>y}.
Proof. repeat (decide equality; eauto using MPtr.eq_dec, Int.eq_dec, Val.eq_dec, peq). Qed.

Tactic Notation "event_cases" tactic(f) tactic(c) :=
    f; [
      c "Ecall" |
      c "Ereturn" |
      c "Eexit" |
      c "Efail" ].

Tactic Notation "mem_event_cases" tactic(f) tactic(c) :=
    f; [
      c "MEfence" |
      c "MEwrite" |
      c "MEread" |
      c "MErmw" |
      c "MEalloc" |
      c "MEfree"].

Tactic Notation "thread_event_cases" tactic(first) tactic(c) :=
    first; [
      c "TEext" |
      c "TEmem" |
      c "TEtau" |
      c "TEexit" |
      c "TEstart" |
      c "TEexternalcallmem" |
      c "TEstartmem" |
      c "TEoutofmem"].

Tactic Notation "mm_event_cases" tactic(first) tactic(c) :=
  first; [
    c "MMmem" |
    c "MMreadfail" |
    c "MMwritefail" |
    c "MMfreefail" |
    c "MMstart" |
    c "MMexit" |
    c "MMtau"].

