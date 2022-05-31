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
Require Import Values.
Require Import Mem.
Require Import Memeq.
Require Import Simulations.
Require Import Events.
Require Import Globalenvs.
Require Import Libtactics.

Section Localsimdef.

(** * Assumptions *)
Variables (SrcS TgtS : Type).

Variable src_step : SrcS -> thread_event -> SrcS -> Prop.
Variable tgt_step : TgtS -> thread_event -> TgtS -> Prop.  

(** State relation is parametrized on partitions and target memory, in
    addition to the usual source and target states. The idea is that
    the target memory can be related to environments. For example, in
    Machabstr, local variables live in thread-local environments, but
    in Machconcr they are laid out in memory, so to relate their
    values, one has to relate Machconcr memory to Machabstr state. The
    memory partitions are ranges of memory that are 'owned' by the
    thread. This is typically the stack region used by stack frames of
    the state.  Note that local variables can only be stored in memory
    that is owned by the target state, but not by the related source
    state. *)

Variable rel :       TgtS ->         (* target state *)
                     list arange  -> (* target allocation partition *)
                     mem ->          (* target memory *)
                     SrcS ->         (* source state *)
                     list arange ->  (* source partition *)
                     Prop.

(** Order for stuttering *)
Variable ord  : TgtS -> TgtS -> Prop.

(** Abbreviations *)
Notation slts := (mklts thread_labels src_step).
Notation src_taustep := (taustep slts).

(** * Simulation rules for individual target transitions *)

(** If the target does [tau] transition, then the source can:
- do an error, or
- also do tau, or
- stutter with decreasing measure, or
- allocate (a subregion of some target region), or
- free region from its partition.
*)
Definition tau_simulation ss ts ts' tm sp tp := 
  (* Either can do an error *)
  stuck_or_error _ ss \/
  (* or also can do tau *)
  (exists ss', src_taustep ss TEtau ss' /\
               rel ts' tp tm ss' sp) \/
  (* or stutter with decreasing measure *)
  (rel ts' tp tm ss sp /\
   ord ts' ts) \/
  (* or it can allocate within some Machconcr region *)
  (exists p, exists n,
               valid_alloc_range (p, n) /\
               (exists r, range_inside (p, n) r /\ In r tp /\ range_not_in (p, n) sp) /\
             exists ss', 
               src_taustep ss (TEmem (MEalloc p n MObjStack)) ss' /\
               rel ts' tp tm ss' ((p, n) :: sp)) \/
  (* or it can free region from its partition *)
  (exists p, exists n, exists sp', sp = (p, n) :: sp' /\
              exists ss', 
              src_taustep ss (TEmem (MEfree p MObjStack)) ss' /\
              rel ts' tp tm ss' sp').

(** If the target does a [read] then the source can:
- do an error, or 
- the read is a Machconcr-local access such that 
       we can do matching tau in source, or 
- do a read of any less defined value. *)

Definition read_simulation ss ts ts' tm sp tp p c v :=
  (* Either can do an error *)
  stuck_or_error _ ss \/
  (* either it is a Machconcr-local access such that 
       we can do matching tau in source *)
  (chunk_inside_range_list p c tp /\
   range_not_in (range_of_chunk p c) sp /\
   load_ptr c tm p <> None /\
   (load_ptr c tm p = Some v ->
    (exists ss', src_taustep ss TEtau ss' /\
                rel ts' tp tm ss' sp) \/
    (rel ts' tp tm ss sp /\ ord ts' ts) \/
    stuck_or_error _ ss)) \/
  (* or we can do a read of any less defined value *)
  (forall v' (LD : Val.lessdef v' v),
    exists ss', src_taustep ss (TEmem (MEread p c v')) ss' /\
                rel ts' tp tm ss' sp).

(** If the target does a [write] then the source can:
- do an error, or
- it is a target-local access such that 
     we can do matching tau or stutter in source, or
- do a  write of a less defined value. *)
Definition write_simulation ss ts ts' tm sp tp p c v :=
  (* Either can do an error *)
  stuck_or_error _ ss \/
  (* or it is a Machconcr-local access such that 
     we can do matching tau or stutter in source *)
  (chunk_inside_range_list p c tp /\
   range_not_in (range_of_chunk p c) sp /\
   exists tm', 
    store_ptr c tm p v = Some tm' /\
    ((exists ss', src_taustep ss TEtau ss' /\
                rel ts' tp tm' ss' sp) \/
     (rel ts' tp tm' ss sp /\ ord ts' ts))) \/
  (* or we can write a less defined value *)
  (exists v', Val.lessdef v' v /\
              exists ss',
              src_taustep ss (TEmem (MEwrite p c v')) ss' /\
              rel ts' tp tm ss' sp).

(** If the target does an [alloc] then the source can:
- do an error, or
- can simulate the alloc depending on object kind:
-- for stack object kind it can just do tau or stutter
-- for any other it must do the same allocation. *)
Definition alloc_simulation ss ts ts' tm sp tp p n k :=
  (* Either can do an error *)
  stuck_or_error _ ss \/
  (* Or can simulate the alloc depending on object kind *)
  match k with
    | MObjStack => 
       forall tm' (A: alloc_ptr (p, n) k tm = Some tm'),
       (* for stack object kind it can just do tau or stutter *) 
       (exists ss', src_taustep ss TEtau ss' /\
                    rel ts' ((p, n)::tp) tm' ss' sp) \/
       (rel ts' ((p, n) :: tp) tm' ss sp /\
        ord ts' ts)
    | _ =>
       (* for any other it must do the same allocation *)
       (exists ss', src_taustep ss (TEmem (MEalloc p n k)) ss' /\
                    rel ts' tp tm ss' sp)
  end.

(** If the target does an [alloc] then the source can:
- do an error, or
- can simulate the free depending on object kind:
-- for stack object kind it can just do tau or stutter,
-- for any other it must do the same free. *)
Definition free_simulation ss ts ts' tm sp tp p k :=
  (* Either can do an error *)
  stuck_or_error _ ss \/
  (* Or can simulate the free depending on object kind *)
  match k with
    | MObjStack => 
       exists n, exists tp', tp = (p, n) :: tp' /\
       forall tm' (A: free_ptr p k tm = Some tm'),
       range_not_in (p, n) sp /\
       (* for stack object kind it can just do tau or stutter *) 
       ((exists ss', src_taustep ss TEtau ss' /\
                    rel ts' tp' tm' ss' sp) \/
       (rel ts' tp' tm' ss sp /\
        ord ts' ts))
    | _ =>
       (* for any other it must do the same free *)
       (exists ss', src_taustep ss (TEmem (MEfree p k)) ss' /\
                    rel ts' tp tm ss' sp)
  end.

(** If the target does a [read-modify-write] then the source can do:
- an error, or
- a RMW with a less-defined value. *)
Definition rmw_simulation ss ts' tm sp tp p c v instr :=
  (* Either can do an error *)
  stuck_or_error _ ss \/
  (* Or can do a RMW with a less-defined value *)
  (forall v' (LD : Val.lessdef v' v),
    exists ss', src_taustep ss (TEmem (MErmw p c v' instr)) ss' /\
                rel ts' tp tm ss' sp).

(** Auxiliary definitions for thread-start and external-action simulations. *)
Fixpoint map_olist {A B} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
    | h :: t => optbind (fun h' => option_map (cons h') (map_olist f t))
                        (f h)
    | nil => Some nil
  end.

Lemma map_map_olist:
  forall A B C (f : A -> option B) (g : B -> option C) (l : list A),
    optbind (map_olist g) (map_olist f l) =
    map_olist (fun x => optbind g (f x)) l.
Proof.
  induction l as [|h l IH]; [done|].
  simpl; destruct (f h); [|done]; simpl. 
  rewrite <- IH.
  destruct (map_olist f l); simpl. done.
  by destruct (g b).
Qed.

Definition mem_arg (m : mem) (loc : pointer * memory_chunk + val) :=
  match loc with
    | inl (p, c) => load_ptr c m p
    | inr v => Some v
  end.

Definition mem_arglist (m : mem) (locs : list (pointer * memory_chunk + val)) :=
  map_olist (mem_arg m) locs.
  
Definition arglist_local {A} (l : list (pointer * memory_chunk + A)) 
           (tp sp : list arange) : Prop :=
  forall p c (IN : In (inl A (p, c)) l),
    chunk_inside_range_list p c tp /\
    range_not_in (range_of_chunk p c) sp.

Definition map_sum_r {A B C} (f : B -> C) (a : A + B) :=
  match a with
    | inl x => inl _ x
    | inr x => inr _ (f x)
  end.

(** If the target does a [thread-start] from memory arguments then the source can do:
- an error, or
- a start action using the arguments from memory. *)
Definition startmem_simulation ss ts' tm sp tp mfn margs :=
  (* Either can do an error *)
  stuck_or_error _ ss \/
  (* Or can do a start action *)
  exists vfnargs, exists fn, exists args,
    arglist_local (mfn :: margs) tp sp /\
    mem_arglist tm (mfn :: margs) = Some vfnargs /\
    Val.lessdef_list (Vptr fn :: args) vfnargs /\
    exists ss', 
      src_taustep ss (TEstart fn args) ss' /\
      rel ts' tp tm ss' sp.

(** If the target does a [ext-call] from memory arguments then the source can do:
- an error, or
- an external call using the arguments from memory. *)
Definition extcallmem_simulation ss ts' tm sp tp id margs :=
  (* Either can do an error *)
  stuck_or_error _ ss \/
  (* Or can do an external call *)
  exists vargs, exists evargs,
    arglist_local margs tp sp /\
    mem_arglist tm (map val_of_eval_memarg margs) = Some vargs /\
    map val_of_eval evargs = vargs /\
    exists ss',     
      src_taustep ss (TEext (Ecall id evargs)) ss' /\
      rel ts' tp tm ss' sp.

(** If the target does an [exit] then the source can do:
- an error, or
- an exit and make sure that it does not own any memory. *)
Definition exit_simulation ss (sp tp : list arange) :=
  (* Either can do an error *)
  stuck_or_error _ ss \/
  (* or can also do an exit *)
  exists ss', src_taustep ss TEexit ss' /\ tp = nil /\ sp = nil.

(** Generic simulation where the source can either do an error or
    match the transition exactly. *)

Definition same_ev_simulation ss ts' tm sp tp te :=
  (* Either can do an error *)
  stuck_or_error _ ss \/
  (* or can do the same *)
  exists ss', src_taustep ss te ss' /\
              rel ts' tp tm ss' sp.

(** Now we assemble the simulation definition from the pieces above. *)
Definition local_intro_simulation :=
  forall ss ts ts' tm sp tp l,
    tgt_step ts l ts' ->
    rel ts tp tm ss sp ->
    match l with
      | TEtau                 => tau_simulation ss ts ts' tm sp tp
      | TEmem (MEread p c v)  => read_simulation ss ts ts' tm sp tp p c v
      | TEmem (MEwrite p c v) => write_simulation ss ts ts' tm sp tp p c v
      | TEmem (MErmw p c v i) => rmw_simulation ss ts' tm sp tp p c v i
      | TEmem (MEalloc p n k) => alloc_simulation ss ts ts' tm sp tp p n k
      | TEmem (MEfree p k)    => free_simulation ss ts ts' tm sp tp p k
      | TEmem MEfence         => same_ev_simulation ss ts' tm sp tp l
      | TEext (Ecall id args) => same_ev_simulation ss ts' tm sp tp l
      | TEext (Ereturn ty ev) => same_ev_simulation ss ts' tm sp tp l
      | TEext Efail           => same_ev_simulation ss ts' tm sp tp l
      | TEext (Eexit _)       => same_ev_simulation ss ts' tm sp tp l
      | TEexit                => exit_simulation ss sp tp
      | TEstart _ _           => same_ev_simulation ss ts' tm sp tp l
      | TEexternalcallmem id args =>
          extcallmem_simulation ss ts' tm sp tp id args
      | TEstartmem fn args    => startmem_simulation ss ts' tm sp tp fn args
      | TEoutofmem            => True
    end.

(** Simulation of stuck states. *)
Definition stuck_simulation :=
  forall ss ts ss' tm sp tp l,
    src_step ss l ss' ->
    rel ts tp tm ss sp ->
    exists ts', exists l'', tgt_step ts l'' ts'.

(** [mem_agrees_on_local m m' tp sp] says that (target) memories [m] and [m'] 
    agree on all the local locations, i.e., locations that are in partition
    [tp] but not in [sp]. *)
Definition mem_agrees_on_local (m  : mem) (m' : mem) 
                               (tp : list arange) (sp : list arange) : Prop :=
  forall p c (CI : chunk_inside_range_list p c tp),
    match load_ptr c m p, load_ptr c m' p with
      | Some sv, Some tv => 
          range_not_in (range_of_chunk p c) sp -> sv = tv 
      | None, None => True
      | _, _ => False
    end.

(** We will require that a simulation relation only depends on the 
    thread-local part of memory (this is needed to show non-interference). *)
Definition simulation_local_invariant :=
  forall ts tp tm tm' ss sp 
    (MA: mem_agrees_on_local tm tm' tp sp)
    (MS: rel ts tp tm ss sp),
      rel ts tp tm' ss sp.
     
End Localsimdef.
