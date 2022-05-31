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
Require Import TSOmachine.
Require Import TSOsimulation.
Require Import Simulations.
Require Import Events.
Require Import Globalenvs.
Require Import Libtactics.
Require Import MMperthreadsimdef.

(** * Buffer relation *)

(** Irrelvant actions do not change partitions or values. *)
Definition buffer_item_irrelevant (bi : buffer_item) :=
  match bi with
    | BufferedAlloc _ _ MObjHeap => True
    | BufferedFree _ MObjHeap => True
    | BufferedAlloc _ _ MObjGlobal => True
    | BufferedFree _ MObjGlobal => True
    | _ => False
  end.

(** Applies a buffer item to a partition. For stack
allocations/deallocations this means adding/removing the
allocated/deallocated range to/from the partition. *)
Definition part_update  (bi : buffer_item)
                        (part : list arange)
                     :  option (list arange) :=
  match bi with
    | BufferedAlloc p n MObjStack => 
        if valid_alloc_range_dec (p, n)
          then if range_in_dec (p, n) part 
            then None
            else Some ((p, n) :: part)
          else None
    | BufferedFree p MObjStack =>
        match part with 
          | (p', n') :: part' => if Ptr.eq_dec p p' then Some part' else None
          | _ => None
        end
    | BufferedAlloc p n _ => Some part
    | BufferedFree p _ => Some part
    | BufferedWrite p c v => Some part
  end.

Notation part_update_buffer := (fold_left_opt part_update).

Definition non_stack k :=
  match k with
    | MObjStack => False
    | _ => True
  end.

Inductive buffers_related : 
  list buffer_item -> (* Machconcr buffer *)
  list arange ->      (* Machconcr partition *)
  list buffer_item -> (* Machabstr buffer *)
  list arange ->      (* Machabstr partition *)
  Prop :=

| buffers_related_empty:
  forall tp sp,
    buffers_related nil tp nil sp

| buffers_related_irrelevant:
  forall tp sp bi sb tb
    (BIIR: buffer_item_irrelevant bi)
    (BR:   buffers_related tb tp sb sp),
    buffers_related (bi :: tb) tp (bi :: sb) sp

| buffers_related_write:
  forall tp sp p c v v' sb tb
    (LD:   Val.lessdef v' v)
    (BR:   buffers_related tb tp sb sp),
    buffers_related (BufferedWrite p c v :: tb) tp (BufferedWrite p c v' :: sb) sp

| buffers_related_local_write:
  forall tp sp p c v sb tb
    (CI: chunk_inside_range_list p c tp)
    (CNI: range_not_in (range_of_chunk p c) sp)
    (ALG: pointer_chunk_aligned p c)
    (BR: buffers_related tb tp sb sp),
    buffers_related (BufferedWrite p c v :: tb) tp sb sp

| buffers_related_salloc:
  forall tp sp p n sb tb r
    (RNIN: range_not_in (p, n) sp)
    (RIr: range_inside (p, n) r)
    (INtp:In r tp) 
    (VAR: valid_alloc_range (p, n))
    (BR: buffers_related tb tp sb ((p, n) :: sp)),
    buffers_related tb tp (BufferedAlloc p n MObjStack :: sb) sp
                    

| buffers_related_sfree:
  forall tp sp p n sb tb
    (BR: buffers_related tb tp sb sp),
    buffers_related tb tp (BufferedFree p MObjStack :: sb) ((p, n) :: sp)
                    

| buffers_related_talloc:
  forall tp sp p n sb tb
    (RNIN: range_not_in (p, n) tp)
    (VAR: valid_alloc_range (p, n))
    (BR: buffers_related tb ((p, n) :: tp) sb sp),
    buffers_related (BufferedAlloc p n MObjStack :: tb) tp sb sp

| buffers_related_tfree:
  forall tp sp p n sb tb
    (RNIN: range_not_in (p, n) sp)
    (BR: buffers_related tb tp sb sp),
    buffers_related (BufferedFree p MObjStack :: tb) ((p, n) :: tp) sb sp.


Tactic Notation "buffers_related_cases" tactic(first) tactic(c) :=
    first; [
      c "buffers_related_empty" |
      c "buffers_related_irrelevant" |
      c "buffers_related_write" |
      c "buffers_related_local_write" |
      c "buffers_related_salloc" |
      c "buffers_related_sfree" |
      c "buffers_related_talloc" |
      c "buffers_related_tfree"].

(** Memories are related for non-stack object if the objects are
    allocated at exactly the same places. *)
Definition non_stack_mem_related (tm : mem) (sm : mem) : Prop :=
  forall r k,
    match k with 
      | MObjStack => True
      | _ => range_allocated r k tm <-> range_allocated r k sm
    end.

(** Memories are related for values if for any location, the value in the 
    Machabstr memory (if defined at all) is less defined than the value
    at the same location in Machconcr memory. *)
Definition load_values_related (tm : mem) (sm : mem) := 
  forall p c,
      match load_ptr c tm p, load_ptr c sm p with
        | Some tv, Some sv => Val.lessdef sv tv
        | _, None => True
        | _, _ => False
      end.

(** Partitioning among threads is a function that assigns a 
    list of owned regions to each thread id. *)
Definition partitioning := positive -> list arange.

(** Partitioning is disjoint if the regions are pairwise disjoint. *)
Definition partitioning_disjoint (part : partitioning) : Prop :=
  forall x y, x <> y -> range_lists_disjoint (part x) (part y).

Definition mem_related_with_partitioning
                                 (m : mem) 
                                 (part : positive -> list arange) : Prop :=
  partitioning_disjoint part /\
  (forall t, range_list_disjoint (part t)) /\
  (forall r, (exists t, In r (part t)) <-> 
              range_allocated r MObjStack m).

Lemma fold_left_opt_dest:
  forall {A B f} {h:A} {t} {v:B} {v'},
  fold_left_opt f (h :: t) v = Some v' ->
  exists v'',
    f h v = Some v'' /\
    fold_left_opt f t v'' = Some v'.
Proof.
  intros A B f h t v v' FLO. 
  simpl in FLO.
  destruct (f h v) as [v''|] _eqn : E; try done.
  exists v''. by split.
Qed.

Lemma fold_left_opt_app_dest:
  forall {A B f} {l1 : list A} {l2} {v:B} {v'},
  fold_left_opt f (l1 ++ l2) v = Some v' ->
  exists v'',
    fold_left_opt f l1 v = Some v'' /\
    fold_left_opt f l2 v'' = Some v'.
Proof.
  intros A B f l1 l2 v v' FLO. 
  rewrite fold_left_opt_app in FLO.
  destruct (fold_left_opt f l1 v) as [v''|] _eqn : E; try done.
  exists v''. by split.
Qed.

Lemma biir_part_update:
  forall bi p,
    buffer_item_irrelevant bi ->
    part_update bi p = Some p.
Proof.
  intros. by destruct bi as [|p' n []|p' []].
Qed.

Lemma buffers_related_suffix:
  forall tb tp sb sp tb' tp' sb' sp'
    (BR1: buffers_related tb tp sb sp)
    (BR2: buffers_related tb' tp' sb' sp')
    (PUs: part_update_buffer sb' sp' = Some sp)
    (PUt: part_update_buffer tb' tp' = Some tp),
    buffers_related (tb' ++ tb) tp' (sb' ++ sb) sp' .
Proof.
  intros tb tp sb sp tb' tp' sb' sp' BR BR'.

  (buffers_related_cases (induction BR') Case);
  simpl; intros PUBs PUBt.
      
  Case "buffers_related_empty".
    by inv PUBs; inv PUBt.
  
  Case "buffers_related_irrelevant".
    rewrite biir_part_update in PUBs, PUBt; try done; [].
    by eapply buffers_related_irrelevant; eauto. 

  Case "buffers_related_write".
    eapply buffers_related_write; try edone.
    by apply IHBR'.

  Case "buffers_related_local_write".
    eapply buffers_related_local_write; try edone.
    by apply IHBR'.

  Case "buffers_related_salloc".
    eapply buffers_related_salloc; try edone.
    apply IHBR'; try done. 
    destruct valid_alloc_range_dec; try done.
    by destruct range_in_dec.

  Case "buffers_related_sfree".
    eapply buffers_related_sfree; try edone.
    apply IHBR'; try done. 
    by destruct Ptr.eq_dec.

  Case "buffers_related_talloc".
    eapply buffers_related_talloc; try edone.
    apply IHBR'; try done. 
    destruct valid_alloc_range_dec; try done.
    by destruct range_in_dec.

  Case "buffers_related_tfree".
    eapply buffers_related_tfree; try edone.
    by apply IHBR'; try done; destruct Ptr.eq_dec.
Qed.

Definition range_list_allocated (p : list arange)
                                (m : mem) : Prop := 
  forall r : arange, In r p -> range_allocated r MObjStack m.

(* facts about mem_related_with_partitioning *)

Lemma mem_related_with_partitioning_ext:
  forall m part part',
    mem_related_with_partitioning m part ->
    (forall t, part t = part' t) ->
    mem_related_with_partitioning m part'.
Proof.
  intros m part part' (PD & RLD & MRWP) E.
  split.
    intros t t'. rewrite <- ! E. apply PD.
  split.
    intro t; rewrite <- ! E; apply RLD.
  intro r; split.
    intros [t IN]. rewrite <- E in IN.
    apply (proj1 (MRWP r)).
    eby eexists.
  intro RA. 
  destruct (proj2 (MRWP r) RA) as [t' IN]. exists t'.
  by rewrite <- E.
Qed.

Lemma alloc_ptr_stack_preserves_mem_partitioning:
  forall m m' p n part t,
    mem_related_with_partitioning m part ->
    alloc_ptr (p, n) MObjStack m = Some m' ->
    mem_related_with_partitioning m'
      (tupdate t ((p, n) :: (part t)) part).
Proof.
  intros m m' p n part t [PD [LD MR]] AP. unfold tupdate.
  split.
    (* Partitions are pairwise disjoint *)
    intros t1 t2 N r IN r' IN'.
    destruct (peq t1 t) as [-> | Nt1]; 
      destruct (peq t2 t) as [-> | Nt2]; try done; 
          try (eapply PD; [apply N | apply IN | apply IN']).
    
    simpl in IN. 
    destruct IN as [<- | IN]; 
      [|eapply PD; [apply N | apply IN | apply IN']].
    destruct (ranges_disjoint_dec (p, n) r') as [DISJ | OVER]. done.
    byContradiction.
    apply (proj2 (proj2 (proj2 (alloc_someD AP))) _ MObjStack OVER).
    apply (proj1 (MR _)); eexists; eassumption.
    (* The symmetric case *)
    simpl in IN'. 
    destruct IN' as [<- | IN']; 
      [|eapply PD; [apply N | apply IN | apply IN']].
    destruct (ranges_disjoint_dec (p, n) r) as [DISJ | OVER]. 
      by apply ranges_disjoint_comm.
    byContradiction.
    apply (proj2 (proj2 (proj2 (alloc_someD AP))) _ MObjStack OVER).
    apply (proj1 (MR _)); eexists; eassumption.
  split.
    (* Each partition is still disjoint *)
    intros t'.
    destruct (peq t' t) as [_ | N].
      split. apply LD.
      intros r IN.
      destruct (ranges_disjoint_dec (p, n) r) as [DISJ | OVER]. done.
      byContradiction.
      apply (proj2 (proj2 (proj2 (alloc_someD AP))) _ MObjStack OVER).
      apply (proj1 (MR _)); eexists; eassumption.
    apply LD.
  (* All partitions are allocated *)
  intro r.
  split.
    intros [t' IN].
    (* Allocation *)
    destruct (peq t' t) as [_ | N];
      try (apply (alloc_preserves_allocated AP); 
          apply (proj1 (MR _)); eexists; eassumption).
      simpl in IN; destruct IN as [<- | IN].
        apply (proj1 (alloc_someD AP)).
    apply (alloc_preserves_allocated AP); 
      apply (proj1 (MR _)); eexists; eassumption. 
  intro RA. 
  destruct (alloc_preserves_allocated_back AP _ _ RA)
    as [[-> _] | RAo].
    exists t. destruct (peq t t); try apply in_eq; done.
  destruct (proj2 (MR _) RAo) as [t' IN'].
  exists t'. 
  destruct (peq t' t) as [-> | N]; try apply in_cons; done.
Qed.

Lemma alloc_ptr_non_stack_preserves_mem_partitioning:
  forall m m' p n k part,
    mem_related_with_partitioning m part ->
    match k with MObjStack => False | _ => True end ->
    alloc_ptr (p, n) k m = Some m' ->
    mem_related_with_partitioning m' part.
Proof.
  intros m m' p n k part [PD [LD MR]] NS AP.
  split. 
    intros t1 t2 N r IN r' IN'.
    eby eapply (PD _ _ N r IN r' IN').
  split. apply LD.
  intro r.
  split.
    intros [t' IN].
    (* Allocation *)
    apply (alloc_preserves_allocated AP); 
      apply (proj1 (MR _)); eexists; eassumption.
  intro RA. 
  destruct (alloc_preserves_allocated_back AP _ _ RA)
    as [[-> <-] | RAo]; try done.
  destruct (proj2 (MR _) RAo); vauto.
Qed.

Lemma alloc_ptr_non_stack_preserves_mem_partitioning_upd:
  forall m m' p n k part t,
    mem_related_with_partitioning m part ->
    match k with MObjStack => False | _ => True end ->
    alloc_ptr (p, n) k m = Some m' ->
    mem_related_with_partitioning m'
      (tupdate t (part t) part).
Proof.
  intros.
  eapply mem_related_with_partitioning_ext. 
    eby eapply alloc_ptr_non_stack_preserves_mem_partitioning.
  intro t'.
  by unfold tupdate; destruct (peq t' t); vauto.
Qed.
  
Lemma store_ptr_preserves_mem_partitioning:
  forall m m' c p v part,
    mem_related_with_partitioning m part ->
    store_ptr c m p v = Some m' ->
    mem_related_with_partitioning m' part.
Proof.
  intros m m' c p v part [PD [LD MR]] ST.
  split. done.
  split. done.
  (* All partitions are allocated *)
  intro r.
  split.
    intros [t' IN]. 
    apply (proj1 (store_preserves_allocated_ranges ST _ _)).
    apply (proj1 (MR _)). eby eexists.
  intro RA.
  apply (proj2 (store_preserves_allocated_ranges ST _ _)) in RA.
  apply (proj2 (MR _) RA).
Qed.

Lemma store_ptr_preserves_mem_partitioning2:
  forall m m' c p v part t,
    mem_related_with_partitioning m part ->
    store_ptr c m p v = Some m' ->
    mem_related_with_partitioning m'
      (tupdate t (part t) part).
Proof.
  intros m m' c p v part t [PD [LD MR]] ST. unfold tupdate.
  split. intros x y NE. 
    destruct (peq x t) as [-> | Nx]; destruct (peq y t) as [-> | Ny];
      apply (PD _ _ NE).
  split. intro t'. destruct (peq t' t); apply LD.
  (* All partitions are allocated *)
  intro r.
  split.
    intros [t' IN]. 
    apply (proj1 (store_preserves_allocated_ranges ST _ _)).
    apply (proj1 (MR _)). destruct (peq t' t); eby eexists.
  intro RA.
  apply (proj2 (store_preserves_allocated_ranges ST _ _)) in RA.
  destruct (proj2 (MR _) RA) as [t' IN].
  exists t'. by destruct (peq t' t) as [-> | _].
Qed.

Lemma ranges_disjoint_dont_overlap:
  forall r r',
    ranges_disjoint r r' ->
    ranges_overlap r r' ->
    False.
Proof. intros r r' D O. apply O, D. Qed.

Lemma range_disjoint_remove:
  forall p l,
    range_list_disjoint l ->
    range_list_disjoint (range_remove p l).
Proof.
  induction l as [|[ph nh]  l IH].
  done.

  simpl. 
  intros [DISJ RNI].
  destruct (Ptr.eq_dec ph p) as [-> | N]. auto. 
  simpl. split. by apply IH. 
  intros [] IN'. eby eapply RNI, in_range_remove.
Qed.

Lemma free_ptr_preserves_mem_partitioning:
  forall m m' p n rest k part t,
    mem_related_with_partitioning m part ->
    free_ptr p k m = Some m' ->
    part t = (p, n) :: rest ->
    mem_related_with_partitioning m'
      (tupdate t rest part).
Proof.
  intros m m' p n rest k part t [PD [LD MR]] FP INP. unfold tupdate.
  pose proof (free_cond_spec p k m) as Fspec.
  rewrite FP in Fspec. destruct Fspec as [n' Fspec].
  assert (INpe: exists t, In (p, n) (part t)). exists t. by rewrite INP; left. 
  destruct (alloc_ranges_same Fspec (proj1 (MR _) INpe)) as [-> ->].
  split.
    (* Partitions are pairwise disjoint *)
    intros t1 t2 N r IN r' IN'.
    destruct (peq t1 t) as [-> | Nt1]; 
      destruct (peq t2 t) as [-> | Nt2]; try done; 
        try (eapply PD; [apply N | apply IN | apply IN']).
      destruct r as [rp rn].
      eapply PD; [apply N | | apply IN']. rewrite INP. by right.
    (* The symmetric case *)
    destruct r'.
    eapply PD; [apply N | apply IN | ]. rewrite INP; by right.
  split.
    (* Each partition is still disjoint *)
    intros t'.
    destruct (peq t' t) as [_ | N]. 
      specialize (LD t); rewrite INP in LD; simpl in LD; tauto.
    by apply LD.
  (* All partitions are allocated *)
  intro r.
  split.
    intros [t' IN].
    (* Free *)
    assert (INpn : In (p, n) (part t)). by rewrite INP; left.
    destruct (peq t' t) as [<- | N].
      destruct r as [pr nr]. 
      assert (IN2 : In (pr, nr) (part t')). by rewrite INP; right.
      assert (IN': exists t, In (pr, nr) (part t)). eexists; eassumption.
      apply (proj1 (MR _)) in IN'.
      destruct (free_preserves_allocated FP _ _ IN') as [|[E _]]. done.
      simpl in E. subst.
      byContradiction.
      specialize (LD t'); rewrite INP in LD; simpl in LD; destruct LD as [RLD RNI].
      destruct (alloc_ranges_same Fspec IN') as [<- _].
      specialize (RNI (p, n) IN). 
      revert RNI. apply ranges_overlap_refl.
      eby eapply valid_alloc_range_non_empty, allocated_range_valid.
    assert (IN': exists t, In r (part t)). eexists; eassumption.
    apply (proj1 (MR _)) in IN'. 
    destruct r as [pr nr].
    destruct (free_preserves_allocated FP _ _ IN') as [|[E _]]. done.
    simpl in E. subst.
    byContradiction.
    eapply ranges_disjoint_dont_overlap.
      apply (PD _ _ N _ IN _ INpn).
    eapply non_empty_same_ptr_overlap;
      eapply valid_alloc_range_non_empty, allocated_range_valid, (proj1 (MR _));
        eexists; eassumption.
  intro RA. 
  (* Free *)
  pose proof (free_preserves_allocated_back FP _ _ RA) as RAo.
  destruct (proj2 (MR _) RAo) as [t' IN'].
  exists t'. 
  destruct (peq t' t) as [-> | N]; try done.
  destruct r as [pr nr].
  rewrite INP in IN'. simpl in IN'. destruct IN' as [E | IN'].
    inv E.
    destruct (free_not_allocated FP _ _ RA).
  done.
Qed.

Lemma free_ptr_non_stack_preserves_mem_partitioning:
  forall m m' p k part,
    mem_related_with_partitioning m part ->
    match k with MObjStack => False | _ => True end ->
    free_ptr p k m = Some m' ->
    mem_related_with_partitioning m' part.
Proof.
  intros m m' p k part [PD [LD MR]] NS FP. unfold tupdate.
  split. 
    intros t1 t2 N r IN r' IN'.
    eby eapply (PD _ _ N r IN r' IN').
  split. by intros t'; apply LD. 
  intro r.
  split.
    intros [t' IN].
    assert (RA : range_allocated r MObjStack m).
      eby apply (proj1 (MR _)); eby eexists.
    by destruct (free_preserves_allocated FP _ _ RA)
      as [RA' | [<- <-]].
  intro RA. 
  apply (free_preserves_allocated_back FP) in RA.
  by destruct (proj2 (MR _) RA) as [t' IN']; vauto.
Qed.

Lemma free_ptr_non_stack_preserves_mem_partitioning_upd:
  forall m m' p k part t,
    mem_related_with_partitioning m part ->
    match k with MObjStack => False | _ => True end ->
    free_ptr p k m = Some m' ->
    mem_related_with_partitioning m'
      (tupdate t (part t) part).
Proof.
  intros.
  eapply mem_related_with_partitioning_ext. 
    eby eapply free_ptr_non_stack_preserves_mem_partitioning.
  intro t'.
  by unfold tupdate; destruct (peq t' t); vauto.
Qed.

Lemma apply_buffer_item_preserves_mem_partitioning:
  forall m m' bi part part' t,
    mem_related_with_partitioning m part ->
    apply_buffer_item bi m = Some m' ->
    part_update bi (part t) = Some part' ->
    mem_related_with_partitioning m' (tupdate t part' part).
Proof.
  intros m m' bi part part' t MRP ABI PU.
  buffer_item_cases (destruct bi as [p c v|p n k|p k]) Case.
  
  Case "BufferedWrite".
    simpl in ABI, PU.
    replace part' with (part t) in *.
      eby eapply store_ptr_preserves_mem_partitioning2.
    by inv PU.
  
  Case "BufferedAlloc".
    unfold part_update, apply_buffer_item in *.
    destruct k;
    destruct (valid_alloc_range_dec (p, n)); try destruct range_in_dec;
      try done; inv PU;
        try (by refine (alloc_ptr_non_stack_preserves_mem_partitioning_upd
          _ _ _ _ _ _ _ MRP _ ABI)); 
        try apply (alloc_ptr_stack_preserves_mem_partitioning 
          _ _ _ _ _ _ MRP ABI). 

  Case "BufferedFree".
    unfold part_update, apply_buffer_item in *.
    destruct k; inv PU; try done;
      try (by refine (free_ptr_non_stack_preserves_mem_partitioning_upd
                      _ _ _ _ _ _ MRP _ ABI)).
    destruct (part t) as [|[p' n'] l] _eqn:Ep. done.
    destruct Ptr.eq_dec as [E|]; [|done]. clarify.
    eby eapply free_ptr_preserves_mem_partitioning.
Qed.

Lemma apply_buffer_preserves_mem_partitioning:
  forall b m m' part part' t,
    mem_related_with_partitioning m part ->
    apply_buffer b m = Some m' ->
    part_update_buffer b (part t) = Some part' ->
    mem_related_with_partitioning m' (tupdate t part' part).
Proof.
  induction b as [|bi br IH];
    intros m m' part part' t MRWP AB PUB; simpl in AB, PUB.

  inv AB. inv PUB.
  eapply mem_related_with_partitioning_ext. edone.
  intro t'. unfold tupdate.
  by destruct peq; subst.

  destruct (apply_buffer_item bi m) as [mi|] _eqn : ABI;
    destruct (part_update bi (part t)) as [pi|] _eqn : PU; 
      try done; unfold optbind in *.
  eapply mem_related_with_partitioning_ext.
  eapply IH. 
  - eapply apply_buffer_item_preserves_mem_partitioning. 
      eapply MRWP. apply ABI. apply PU.
  - apply AB.
  - eby rewrite tupdate_s. 
  - by intro t'; unfold tupdate; destruct peq.
Qed.


Lemma apply_buffer_consD:
  forall {bi b m m'}
    (AB : apply_buffer (bi :: b) m = Some m'),
    exists mi, apply_buffer_item bi m = Some mi /\
               apply_buffer b mi = Some m'.
Proof.
  intros.
  simpl in AB. destruct apply_buffer_item; try done.
  eby eexists; split. 
Qed.  

(* mem_agrees_on_local for unbuffering *)

Lemma mem_agrees_on_local_preserved_by_irrelevant:
  forall bi tm tm' sp tp tmx tmx'
    (BIIR: buffer_item_irrelevant bi)
    (ABI : apply_buffer_item bi tm = Some tmx)
    (ABI': apply_buffer_item bi tm' = Some tmx')
    (RLA : range_list_allocated tp tm)
    (RLA': range_list_allocated tp tm')
    (MA  : mem_agrees_on_local tm tm' tp sp),
           mem_agrees_on_local tmx tmx' tp sp.
Proof.
  intros.

  (buffer_item_cases (destruct bi as [p c v | p n k | p k]) Case);
    intros r' p' CI; specialize (MA r' p' CI);
      destruct (chunk_inside_range_listD CI) as [rc (INrc & RIrc)].

  Case "BufferedWrite". done.

  Case "BufferedAlloc".
    assert(ranges_disjoint (range_of_chunk r' p') (p, n)).
      eapply ranges_disjoint_comm, disjoint_inside_disjoint_r, RIrc.
      simpl in ABI; apply (alloc_allocatedD ABI (RLA _ INrc)).
    by destruct k; try done; simpl in ABI, ABI';
      rewrite (load_alloc_other ABI), (load_alloc_other ABI').
  
  Case "BufferedFree".
    destruct(free_someD ABI) as [n RA].
    destruct(free_someD ABI') as [n' RA'].
    simpl in ABI, ABI'.
    rewrite (load_free_other ABI RA), (load_free_other ABI' RA'); try done.
    - destruct (ranges_are_disjoint RA' (RLA' _ INrc)) as [[_ E] |]. by subst.
      by eapply ranges_disjoint_comm, disjoint_inside_disjoint_r, RIrc.
    - destruct (ranges_are_disjoint RA (RLA _ INrc)) as [[_ E] |]. by subst.
      by eapply ranges_disjoint_comm, disjoint_inside_disjoint_r, RIrc.
Qed.

Lemma mem_agrees_on_local_preserved_by_write:
  forall p c v tm tm' sp tp tmx tmx'
    (ABI : apply_buffer_item (BufferedWrite p c v) tm = Some tmx)
    (ABI': apply_buffer_item (BufferedWrite p c v) tm' = Some tmx')
    (MA  : mem_agrees_on_local tm tm' tp sp),
           mem_agrees_on_local tmx tmx' tp sp.
Proof.
  intros. simpl in ABI, ABI'.
  intros p' c' CI; specialize (MA p' c' CI);
    destruct (chunk_inside_range_listD CI) as [rc (INrc & RIrc)].
  assert (CAP := store_preserves_chunk_allocation ABI p' c').
  assert (CAP' := store_preserves_chunk_allocation ABI' p' c').
  assert (LStm := load_chunk_allocated_spec c' tm p').
  assert (LStm' := load_chunk_allocated_spec c' tm' p').
  assert (LStmx := load_chunk_allocated_spec c' tmx p').
  assert (LStmx' := load_chunk_allocated_spec c' tmx' p').
  destruct (load_ptr c' tm p') as [] _eqn : Ltm; 
    destruct (load_ptr c' tm' p') as [] _eqn : Ltm'; try done.
    apply CAP in LStm. apply CAP' in LStm'.
    destruct (load_ptr c' tmx p') as [] _eqn : Ltmx; 
      destruct (load_ptr c' tmx' p') as [] _eqn : Ltmx'; try done; [].
    intro RNI; specialize (MA RNI). subst.
    rewrite <- Ltm' in Ltm.
    rewrite (load_eq_preserved_by_store Ltm ABI ABI') in Ltmx.
    by clarify'.
  by destruct (load_ptr c' tmx p') as [] _eqn : Ltmx; 
    destruct (load_ptr c' tmx' p') as [] _eqn : Ltmx';
      try apply CAP in LStmx; try apply CAP' in LStmx'.
Qed.

Lemma alloc_preserves_chunk_allocation:
  forall {r k m m'} (A : alloc_ptr r k m = Some m'),
    forall p c (CA : chunk_allocated_and_aligned p c m),
      chunk_allocated_and_aligned p c m'.
Proof.
  intros.
  destruct CA as [[r' [k' [RI RA]]] PA]. split; [|done].
  exists r'; exists k'; split. done.
  eby eapply alloc_preserves_allocated.
Qed.  

Lemma mem_agrees_on_local_preserved_by_talloc:
  forall p n tm tm' sp tp tmx tmx'
    (*RLA : range_list_allocated tp tm*)
    (*RLA': range_list_allocated tp tm'*)
    (ABI : apply_buffer_item (BufferedAlloc p n MObjStack) tm = Some tmx)
    (ABI': apply_buffer_item (BufferedAlloc p n MObjStack) tm' = Some tmx')
    (MA  : mem_agrees_on_local tm tm' tp sp),
           mem_agrees_on_local tmx tmx' ((p, n)::tp) sp.
Proof.
  intros. simpl in ABI, ABI'.
  intros p' c' CI. specialize (MA p' c').
  destruct (chunk_inside_range_listD CI) as [rc (INpnrc & RIrc)].
  destruct (in_inv INpnrc) as [<- | INrc].
    assert (LStmx := load_chunk_allocated_spec c' tmx p').
    assert (LStmx' := load_chunk_allocated_spec c' tmx' p').
    by destruct (load_ptr c' tmx p') as [] _eqn : Ltmx; 
      destruct (load_ptr c' tmx' p') as [] _eqn : Ltmx'; try done;
        rewrite (load_alloc_inside ABI RIrc), (load_alloc_inside ABI' RIrc) in *;
          clarify; try (destruct LStmx as (?&?)); try (destruct LStmx' as (?&?)).
  exploit MA. eby eapply chunk_inside_range_listI. intro MA'.
  assert (CAP := alloc_preserves_chunk_allocation ABI p' c').
  assert (CAP' := alloc_preserves_chunk_allocation ABI' p' c').
  assert (LStm := load_chunk_allocated_spec c' tm p').
  assert (LStm' := load_chunk_allocated_spec c' tm' p').
  assert (LStmx := load_chunk_allocated_spec c' tmx p').
  assert (LStmx' := load_chunk_allocated_spec c' tmx' p').
  destruct (load_ptr c' tm p') as [] _eqn : Ltm; 
    destruct (load_ptr c' tm' p') as [] _eqn : Ltm'; try done.
    apply CAP in LStm. apply CAP' in LStm'.
    destruct (load_ptr c' tmx p') as [] _eqn : Ltmx; 
      destruct (load_ptr c' tmx' p') as [] _eqn : Ltmx'; try done; [].
    intro RNI; specialize (MA' RNI). subst.
    rewrite <- Ltm' in Ltm.
    rewrite (load_eq_preserved_by_alloc Ltm ABI ABI') in Ltmx.
    by clarify'.
  rewrite <- Ltm' in Ltm.
  rewrite (load_eq_preserved_by_alloc Ltm ABI ABI').
  by destruct (load_ptr c' tmx' p').
Qed.

Lemma mem_agrees_on_local_preserved_by_tfree:
  forall p n tm tm' sp tp tmx tmx'
    (RA  : range_allocated (p, n) MObjStack tm)
    (RA' : range_allocated (p, n) MObjStack tm')
    (RNI : range_not_in (p, n) tp)
    (ABI : apply_buffer_item (BufferedFree p MObjStack) tm = Some tmx)
    (ABI': apply_buffer_item (BufferedFree p MObjStack) tm' = Some tmx')
    (MA  : mem_agrees_on_local tm tm' ((p, n)::tp) sp),
           mem_agrees_on_local tmx tmx' tp sp.
Proof.
  intros. simpl in ABI, ABI'.
  intros p' c' CI. specialize (MA p' c').
  exploit MA. 
    destruct (chunk_inside_range_listD CI) as [r' [IN RI]].
    eapply chunk_inside_range_listI. eby right. done.
  intro MA'.
  destruct (ranges_disjoint_dec (range_of_chunk p' c') (p, n)) as [DISJ | OVER].
    by rewrite (load_free_other ABI RA DISJ), (load_free_other ABI' RA' DISJ).
  by rewrite (load_free_overlap ABI RA OVER), (load_free_overlap ABI' RA' OVER).
Qed.

Lemma mem_agrees_on_local_preserved_by_salloc:
  forall p n tm tm' sp tp 
    (MA  : mem_agrees_on_local tm tm' tp sp),
           mem_agrees_on_local tm tm' tp ((p, n)::sp).
Proof.
  intros. 
  intros p' c' CI. specialize (MA p' c' CI).
  destruct (load_ptr c' tm p') as [] _eqn : Ltm; 
    destruct (load_ptr c' tm' p') as [] _eqn : Ltm'; try done.
  intro RNI; apply MA.
  intros r IN. apply RNI. by right.
Qed.

Fixpoint remove_frees_from_part (sp : list arange) (b : list buffer_item) :=
  match b with
    | nil => sp
    | BufferedFree p MObjStack :: b => range_remove p (remove_frees_from_part sp b)
    | _ :: b => remove_frees_from_part sp b
  end.

Lemma in_rfree_part:
  forall p n b sp,
    In (p, n) (remove_frees_from_part sp b) <->
    In (p, n) sp /\ ~ In (BufferedFree p MObjStack) b.
Proof.
  induction b as [|bi b]; intros; simpl. tauto.

  destruct bi as [p' c' v'|p' n' k'|p' []];
    try (specialize (IHb sp); destruct IHb as [IHl IHr]; split; 
      [intro; split; [|intros [|]]; try done; tauto |
       intros [IN O]; apply IHr; split; [|intro IN'; elim O]; tauto]).
  
  specialize (IHb sp); destruct IHb as [IHl IHr].
  split. 
    intro IN. apply in_range_removeD in IN. destruct IN as [NE IN].
    specialize (IHl IN). split. tauto.
    intros [E|]; clarify; tauto.
  intros [IN O]. apply in_range_removeI.
  apply IHr. tauto.
  intro E; subst; tauto. 
Qed.

Lemma mem_agrees_on_local_mono_sp:
  forall tm tm' tp sp sp'
  (SUB: forall r, In r sp -> In r sp')
  (MA:  mem_agrees_on_local tm tm' tp sp),
    mem_agrees_on_local tm tm' tp sp'.
Proof.
  intros. intros p c IN. specialize (MA p c IN).
  destruct load_ptr; destruct load_ptr; try done; [].
  intro RNI; apply MA.
  intros r' IN'. eapply RNI.
  eauto.
Qed.

Lemma remove_frees_from_part_unbuffer:
  forall r sp b bi
  (IN:  In r (remove_frees_from_part sp (bi :: b))),
        In r (remove_frees_from_part sp b).
Proof.
  intros. destruct r as [p n]. 
  apply <- in_rfree_part. apply in_rfree_part in IN.
  destruct IN as [IN NIN]. 
  split. done.
  intro IN'; elim NIN. by right.
Qed.

Lemma mem_agrees_on_local_unbuffer:
  forall tm tm' tp sp bi b
  (MA:  mem_agrees_on_local tm tm' tp (remove_frees_from_part sp (bi :: b))),
    mem_agrees_on_local tm tm' tp (remove_frees_from_part sp b).
Proof.
  intros. eapply mem_agrees_on_local_mono_sp; [|edone].
  intros r IN. eby eapply remove_frees_from_part_unbuffer.
Qed.

Lemma mem_agrees_on_local_preserved_by_sfree:
  forall p n tm tm' sp tp b
    (RNI : range_not_in (p, n) sp)
    (MA  : mem_agrees_on_local tm tm' tp 
                               (remove_frees_from_part ((p, n)::sp) (BufferedFree p MObjStack::b))),
           mem_agrees_on_local tm tm' tp (remove_frees_from_part sp b).
Proof.
  intros.
  eapply mem_agrees_on_local_mono_sp; [|edone].
  intros [p' n'] IN. simpl in IN.
  apply <- in_rfree_part.
  apply in_range_removeD in IN. destruct IN as [N IN].
  apply -> in_rfree_part in IN. destruct IN as [IN NIN].
  simpl in IN. destruct IN as [E | IN]. by inv E.
  tauto.
Qed.

Lemma part_update_irrelevant:
  forall {bi} (BIIR : buffer_item_irrelevant bi) part,
  part_update bi part = Some part.
Proof.
  intros.
  by destruct bi as [|p n []|p []].
Qed.

Lemma range_list_allocated_irrelevant:
  forall bi tm tm' tp
    (BIIR: buffer_item_irrelevant bi)
    (ABI: apply_buffer_item bi tm = Some tm')
    (RLA: range_list_allocated tp tm),
      range_list_allocated tp tm'.
Proof.
  intros. intros r IN. specialize (RLA r IN).
  destruct bi as [|p n []|p []]; try done; simpl in ABI;
   try (by apply (alloc_preserves_allocated ABI));
     by destruct (free_preserves_allocated ABI _ _ RLA) as [A|[E1 E2]].
Qed.

Lemma range_list_allocated_part_alloc:
  forall p n tm tm' tp 
    (A:   alloc_ptr (p, n) MObjStack tm = Some tm')
    (RLA: range_list_allocated tp tm),
      range_list_allocated ((p, n)::tp) tm'.
Proof.
  intros. intros r IN.
  simpl in IN. destruct IN as [<- | IN].
    apply alloc_someD in A; tauto.
  apply (alloc_preserves_allocated A); auto.
Qed.

Lemma range_list_allocated_part_free:
  forall p n tm tm' tp 
    (F:   free_ptr p MObjStack tm = Some tm')
    (RNI: range_not_in (p, n) tp)
    (RLA: range_list_allocated ((p, n)::tp) tm),
      range_list_allocated tp tm'.
Proof.
  intros. intros [p' n'] IN.
  pose proof (RLA _ (in_eq _ _)) as RA'.
  specialize (RLA (p', n')).
  exploit RLA. by right. 
  intro RA. 
  destruct (free_preserves_allocated F _ _ RA) as [|[E _]]; [done|].
  simpl in E; subst.
  destruct (alloc_ranges_same RA RA') as [<- _].
  specialize (RNI (p, n') IN). 
  byContradiction. revert RNI. apply ranges_overlap_refl.
  eby eapply valid_alloc_range_non_empty, allocated_range_valid.
Qed.

(*
Lemma part_update_write:
  forall p c v part,
  part_update (BufferedWrite p c v) part = Some part.
Proof. done. Qed.
*)

Lemma range_list_allocated_write:
  forall p c v tm tm' tp
    (ABI: apply_buffer_item (BufferedWrite p c v) tm = Some tm')
    (RLA: range_list_allocated tp tm),
      range_list_allocated tp tm'.
Proof.
  intros. intros r IN. specialize (RLA r IN). simpl in ABI.
  by apply (store_preserves_allocated_ranges ABI _ _).
Qed.

Lemma irrelevant_agrees_on_local:
  forall bi tm tm' tp sp t
    (BIIR: buffer_item_irrelevant bi)
    (ABI : apply_buffer_item bi tm = Some tm')
    (MRPt: mem_related_with_partitioning tm tp),
      mem_agrees_on_local tm tm' (tp t) sp.
Proof.
  intros.
  intros r c CI.
  destruct (chunk_inside_range_listD CI) as [r' [IN RI]].
  assert (RA: range_allocated r' MObjStack tm).
    destruct MRPt as (_ & _ & A). apply -> A.
    eby eexists.
  destruct bi as [|p n k|p k]; try done; simpl in ABI.
  (* Alloc *)
  rewrite (load_alloc_other ABI).
    by destruct load_ptr. 
  eapply disjoint_inside_disjoint, RI.
  apply ranges_disjoint_comm. eby eapply (alloc_allocatedD ABI).
  (* Free *)
  destruct (free_someD ABI) as [n RA'].
  erewrite (load_free_other ABI).
      by destruct load_ptr. 
    edone.
  eapply disjoint_inside_disjoint, RI.
  by destruct (ranges_are_disjoint RA RA') as [[_ <-]|].
Qed.

Lemma buffers_related_part_update_buffer:
  forall sb sp tb tp
    (BR: buffers_related tb tp sb sp),
    exists sp', part_update_buffer sb sp = Some sp'.
Proof.
  intros.
  (buffers_related_cases (induction BR) Case); try done.

  Case "buffers_related_empty".
    eby eexists.
   
  Case "buffers_related_irrelevant".
    simpl. by rewrite part_update_irrelevant. 

  Case "buffers_related_salloc".
    simpl. destruct valid_alloc_range_dec; [|done].
    destruct range_in_dec as [[? [IN O]]|]; eauto.
    by specialize (RNIN _ IN).      

  Case "buffers_related_sfree".
    simpl. by destruct Ptr.eq_dec. 
Qed.

Lemma range_remove_comm:
  forall p p' l,
    range_remove p (range_remove p' l) =
    range_remove p' (range_remove p l).
Proof.
  induction l as [|[pr nr] l IH]. done.
  simpl.
  by destruct (Ptr.eq_dec pr p') as [<-|N];
    destruct (Ptr.eq_dec pr p) as [<-|N']; simpl; subst; try done;
      rewrite IH; (repeat destruct Ptr.eq_dec).
Qed.

Lemma range_remove_comm_remove_frees:
  forall p b sp,
    range_remove p (remove_frees_from_part sp b) =
    remove_frees_from_part (range_remove p sp) b.
Proof.
  induction b as [|bi b IH]. done.

  intros.
  destruct bi as [| |p' []]; simpl; auto.
  by rewrite <- IH, range_remove_comm.
Qed.

Lemma range_remove_not_in:
  forall p n sp
    (RNE: range_non_empty (p, n))
    (RNEsp: forall r, In r sp -> range_non_empty r)
    (RNI: range_not_in (p, n) sp),
      range_remove p sp = sp.
Proof.
  induction sp as [|[p' n'] sp IH]. done.
  simpl.
  destruct Ptr.eq_dec as [<- | N]; intros.
    specialize (RNI _ (in_eq _ _)).
    by elim (non_empty_same_ptr_overlap _ _ _ RNE (RNEsp _ (in_eq _ _))).
  f_equal; apply IH.
  - done.
  - intros r IN. eby eapply RNEsp; right.
  - intros r IN. eby eapply RNI; right.
Qed.

Lemma remove_disjoint:
  forall {p n sp m}
    (RLD: range_list_disjoint ((p, n)::sp))
    (RLA: range_list_allocated ((p, n)::sp) m),
    range_remove p sp = sp.
Proof.
  intros.
  simpl in RLD; destruct RLD as [RLD RNI].
  eapply range_remove_not_in; [| |edone].
  - eapply valid_alloc_range_non_empty, allocated_range_valid, RLA.
    by left.
  - intros r IN.
    eapply valid_alloc_range_non_empty, allocated_range_valid, RLA.
    by right.
Qed.  

Lemma range_of_chunk_not_empty:
  forall p c,
    range_non_empty (range_of_chunk p c).
Proof.
  intros p c.
  unfold range_non_empty, range_of_chunk, snd.
  rewrite size_chunk_repr. by pose proof (size_chunk_pos c); omega.
Qed.  

Lemma unbuffer_write_free:
  forall p c v  t t' rest r sp' stso sp
    (US:  unbuffer_safe stso)
    (RO:  ranges_overlap (range_of_chunk p c) r)
    (IN:  In r sp)
    (RLA: range_list_allocated sp stso.(tso_mem))
    (RLD: range_list_disjoint sp)
    (PU:  part_update_buffer (tso_buffers stso t) sp = Some sp')
    (NEt: t <> t')
    (Ebt: tso_buffers stso t' = BufferedWrite p c v :: rest),
      In r (remove_frees_from_part sp (tso_buffers stso t)).
Proof.
  intros until stso.
  remember (tso_buffers stso t) as bt.
  revert stso Heqbt.
  
  induction bt as [|bi btrest IH]; intros. done.

  inversion US; subst; destruct (ABIS _ _ _ (sym_eq Heqbt)) as [m' ABI].
  pose proof (UNBS _ _ _ _ (sym_eq Heqbt) ABI) as US'.
  specialize (IH (mktsostate (tupdate t btrest (tso_buffers stso)) m')).
  simpl in IH. rewrite tupdate_s in IH. specialize (IH (refl_equal _)).

  (buffer_item_cases (destruct bi as [p' c' v' | p' n' k' | p' k']) Case).

  Case "BufferedWrite".
    exploit IH; try edone.
    - eby eapply range_list_allocated_write.
    - rewrite tupdate_o. done. by intro E; subst.

  Case "BufferedAlloc".
    destruct k';
    (* Global, heap *)
    try (by exploit IH; try edone;
      try (by eapply range_list_allocated_irrelevant; try edone);
        rewrite tupdate_o; [|intro E; subst]).
    (* Stack *)
    specialize (IH ((p', n') :: sp)).
    exploit IH; try edone.
    - by right.
    - eby eapply range_list_allocated_part_alloc.
    - split. done.
      intros r' IN'. simpl in ABI.
      destruct (alloc_someD ABI) as (_ & _ & _ & ROA).
      destruct (ranges_disjoint_dec (p', n') r'). done.
      specialize (RLA _ IN').
      by specialize (ROA _ _ n RLA).
    - simpl in PU. destruct valid_alloc_range_dec; [|done].
      by destruct range_in_dec.
    - by rewrite tupdate_o; [|intro E; subst].
    destruct r as [pr nr].
    intro RF.
    apply <- in_rfree_part. apply -> in_rfree_part in RF.
    split. done.
    destruct RF as [_ NIN].
    by intro INf; elim NIN; destruct INf.
    
  Case "BufferedFree".  
    destruct k';
    (* Global, heap *)
    try (by exploit IH; try edone;
      try (by eapply range_list_allocated_irrelevant; try edone);
        rewrite tupdate_o; [|intro E; subst]).
    (* Stack *)
    simpl in PU. destruct sp as [|[spp n'] sp]. done.
    destruct Ptr.eq_dec; [|done].
    subst spp.
    simpl. rewrite range_remove_comm_remove_frees.
    simpl. destruct Ptr.eq_dec; [|done].
    rewrite (remove_disjoint RLD RLA).
    destruct r as [rp rn].
    simpl in ABI.
    destruct IN as [E | IN].
      byContradiction.
      inv E.
      assert (RA := RLA _ (in_eq _ _)).
      inv US'; clear UNBS0.
      specialize (ABIS0 t'). simpl in ABIS0. 
      rewrite tupdate_o in ABIS0; [|by intro; subst].
      destruct (ABIS0 _ _ Ebt) as [mw W]; clear ABIS0; simpl in W.
      apply store_chunk_allocated_someD in W.
      destruct W as [[r' [k' [RI' RA']]] _].
      assert (RAm := free_preserves_allocated_back ABI _ _ RA').
      destruct (ranges_are_disjoint RA RAm) as [[<- <-] | DISJ].        
        by apply (free_not_allocated ABI _ _ RA').
      eapply RO. apply ranges_disjoint_comm.
      by eapply disjoint_inside_disjoint_r, RI'.    
    eapply IH; try done.
    - eby destruct RLD; eapply range_list_allocated_part_free.
    - by destruct RLD.
    - by rewrite tupdate_o; [|intro E; subst].
Qed.  
      
Lemma non_stack_mem_related_sym:
  forall m m',
    non_stack_mem_related m m' -> non_stack_mem_related m' m.
Proof.
  intros m m' NSR r k. 
  specialize (NSR r k).
  destruct k; try done; by apply iff_sym.
Qed.

(* Machinery for proving preservation for non_stack_mem_related *)
Definition stack_or_write_item (bi : buffer_item) : Prop :=
  match bi with
    | BufferedAlloc _ _ MObjStack => True
    | BufferedFree _ MObjStack => True
    | BufferedWrite _ _ _ => True
    | _ => False
  end.

Lemma non_stack_mem_rel_preserved_by_stack_or_write:
  forall tm sm bi sm',
    non_stack_mem_related tm sm ->
    apply_buffer_item bi sm = Some sm' ->
    stack_or_write_item bi ->
    non_stack_mem_related tm sm'.
Proof.
  intros tm sm bi sm' NSMR ABI SOW r k.
  unfold apply_buffer_item, stack_or_write_item in *.
  specialize (NSMR r k).
  destruct k; try done; (
    split;
    [intro RA; apply NSMR in RA; destruct bi as [? ? ? | ? ? [] | ? []]; try done;
      [apply (store_preserves_allocated_ranges ABI r _) |
       eapply alloc_preserves_allocated |
       destruct (free_preserves_allocated ABI _ _ RA)as [ | []]] |
     intro RA; apply NSMR; destruct bi as [? ? ? | ? ? [] | ? []]; try done;
      [apply (store_preserves_allocated_ranges ABI r _) |
       destruct (alloc_preserves_allocated_back ABI _ _ RA) as [[]|] |
       eapply free_preserves_allocated_back]]); 
        edone.
Qed.

Lemma non_stack_mem_rel_preserved_by_stack_or_write_tgt:
  forall tm sm bi tm',
    non_stack_mem_related tm sm ->
    apply_buffer_item bi tm = Some tm' ->
    stack_or_write_item bi ->
    non_stack_mem_related tm' sm.
Proof.
  intros tm sm bi tm' NSMR ABI SOW.
  apply non_stack_mem_related_sym in NSMR.
  eby eapply non_stack_mem_related_sym, 
    non_stack_mem_rel_preserved_by_stack_or_write.
Qed.

Lemma sim_alloc_preserves_non_stack_mem_related:
  forall tm sm tm' sm' p n k,
    non_stack_mem_related tm sm ->
    alloc_ptr (p, n) k tm = Some tm' ->
    alloc_ptr (p, n) k sm = Some sm' -> 
    non_stack_mem_related tm' sm'.
Proof.
  intros tm sm tm' sm' p n k NSR APt APs.
  intros r' k'; specialize (NSR r' k'); destruct k'; try done;
    (split; intro RA; [
    destruct (alloc_preserves_allocated_back APt _ _ RA) 
      as [[-> <-] | RA2]; try done; [
      by apply (proj1 (alloc_someD APs)) |
      by apply (alloc_preserves_allocated APs), NSR] |
    destruct (alloc_preserves_allocated_back APs _ _ RA) 
      as [[-> <-] | RA2]; try done; [
      by apply (proj1 (alloc_someD APt)) |
      by apply (alloc_preserves_allocated APt), NSR]]). 
Qed.

Lemma sim_free_preserves_non_stack_mem_related:
  forall tm sm tm' sm' p k,
    non_stack_mem_related tm sm ->
    free_ptr p k tm = Some tm' ->
    free_ptr p k sm = Some sm' -> 
    non_stack_mem_related tm' sm'.
Proof.
  intros tm sm tm' sm' p k NSR FPt FPs.
  
  intros [p' n'] k'; specialize (NSR (p', n') k'); destruct k'; try done;
    (split; intro RA; [
    pose proof (free_preserves_allocated_back FPt _ _ RA) as RA';
    apply NSR in RA'; destruct (free_preserves_allocated FPs _ _ RA') 
      as [? | [<- <-]]; try done; 
        destruct (free_not_allocated FPt _ _ RA) |
    pose proof (free_preserves_allocated_back FPs _ _ RA) as RA';
    apply NSR in RA'; destruct (free_preserves_allocated FPt _ _ RA') 
      as [? | [<- <-]]; try done; 
        destruct (free_not_allocated FPs _ _ RA)]).
Qed.

Lemma sim_irrelevant_preserves_non_stack_mem_related:
  forall tm sm tm' sm' bi,
    non_stack_mem_related tm sm ->
    buffer_item_irrelevant bi ->
    apply_buffer_item bi tm = Some tm' ->
    apply_buffer_item bi sm = Some sm' -> 
    non_stack_mem_related tm' sm'.
Proof.
  intros tm sm tm' sm' bi NSR BIIR ABIt ABIs.
  unfold apply_buffer_item, buffer_item_irrelevant in *.
  destruct bi as [p c v | p n k | p k].
  
  (* Write *)
  intros r' k'. specialize (NSR r' k'). 
  destruct k'; try done;
    (eapply iff_trans; 
      [eapply iff_sym; 
        apply (store_preserves_allocated_ranges ABIt) |
       eapply iff_trans; 
         [edone | 
          apply (store_preserves_allocated_ranges ABIs)]]).
  eby eapply sim_alloc_preserves_non_stack_mem_related.
  eby eapply sim_free_preserves_non_stack_mem_related.
Qed.  

Lemma alloc_ptr_tgt_preserves_load_rel:
  forall tm sm tm' r k
    (LVR: load_values_related tm sm)
    (A:   alloc_ptr r k tm = Some tm')
    (NA:  forall r' k', range_allocated r' k' sm ->
                        ranges_disjoint r' r),
      load_values_related tm' sm.
Proof.
  intros. intros p c. specialize (LVR p c).
  destruct (load_ptr c sm p) as [cmv|] _eqn : SL.
    destruct (load_chunk_allocated_someD SL) as [[rl [kl [RIl RAl]]] _].
    rewrite (load_alloc_other A). done.
    eapply disjoint_inside_disjoint_l; eauto.
  by destruct (load_ptr c tm p) as [csv|] _eqn : TL;
    destruct (load_ptr c tm' p) as [csv'|] _eqn : TL'.
Qed.

Lemma alloc_ptr_src_preserves_load_rel:
  forall tm sm sm' r k r' k'
    (LVR: load_values_related tm sm)
    (A:   alloc_ptr r k sm = Some sm')
    (RI:  range_inside r r')
    (RA:  range_allocated r' k' tm),
      load_values_related tm sm'.
Proof.
  intros. intros p c. specialize (LVR p c).
  destruct (load_ptr c sm p) as [sv|] _eqn : SL.
    by rewrite (load_some_alloc SL A).
  destruct (ranges_disjoint_dec (range_of_chunk p c) r) as [RD | RO].
    by rewrite (load_alloc_other A), SL.
  destruct (load_ptr c sm' p) as [sv'|] _eqn : SL'; [|done].
  pose proof (load_chunk_allocated_noneD SL) as CNA.
  destruct (load_chunk_allocated_someD SL') as [[rsv' [ksv' [RIsc' RAsv']]] ALG].
  destruct (alloc_preserves_allocated_back A _ _ RAsv') as [[<- <-] | RAsv].
    rewrite (load_alloc_inside A) in SL'; try done; []. inv SL'.
    destruct (load_ptr c tm p) as [] _eqn : TL. vauto.
    apply (load_chunk_allocated_noneD TL).
    split; [|done].
    eexists; eexists. eby split; [eapply range_inside_trans|].
  elim CNA. split; [|done].
  eby eexists; eexists; split.
Qed.

Lemma free_ptr_tgt_preserves_load_rel:
  forall tm sm tm' p n k
    (LVR: load_values_related tm sm)
    (F:   free_ptr p k tm = Some tm')
    (RA:  range_allocated (p, n) k tm)
    (NA:  forall r' k', range_allocated r' k' sm ->
                        ranges_disjoint r' (p, n)),
      load_values_related tm' sm.
Proof.
  intros. intros p' c'. specialize (LVR p' c').
  destruct (load_ptr c' sm p') as [sv|] _eqn : SL.
    erewrite (load_free_other F); try edone; [].
    destruct (load_chunk_allocated_someD SL) as [[rs [ks [RIs ROs]]] ALG].
    eapply disjoint_inside_disjoint_l, RIs.
    eby eapply NA.
  by destruct (load_ptr c' tm' p').
Qed.

Lemma free_ptr_src_preserves_load_rel:
  forall tm sm sm' p k
    (LVR: load_values_related tm sm)
    (F:   free_ptr p k sm = Some sm'),
      load_values_related tm sm'.
Proof.
  intros. intros p' c'. specialize (LVR p' c').
  destruct (free_someD F) as [n RAs].
  destruct (ranges_disjoint_dec (range_of_chunk p' c') (p, n)) as [D|O].
    by rewrite (load_free_other F RAs D). 
  by rewrite (load_free_overlap F RAs O); destruct (load_ptr c' tm p').
Qed.

Lemma local_write_preserves_load_rel:
  forall tm sm c p v tm'
    (LVR: load_values_related tm sm)
    (S:   store_ptr c tm p v = Some tm')
    (CNI: forall r k (RA: range_allocated r k sm),
            ranges_disjoint (range_of_chunk p c) r),
      load_values_related tm' sm.
Proof.
  intros. intros p' c'. specialize (LVR p' c').
  destruct (ranges_disjoint_dec (range_of_chunk p c) 
                                (range_of_chunk p' c')) as [D|O].
    by rewrite <- (load_store_other S).
  destruct (load_ptr c' sm p') as [sv|] _eqn : SL; 
    [|by destruct (load_ptr c' tm' p')].
  destruct (load_chunk_allocated_someD SL) as [[r' [k' [RI RA]]] ALG].
  elim O. eapply disjoint_inside_disjoint_r, RI.
  eby eapply CNI.
Qed.

Lemma write_preserves_load_rel:
  forall tm sm c p v v' tm' sm'
    (LVR: load_values_related tm sm)
    (LD:  Val.lessdef v' v)
    (St:  store_ptr c tm p v = Some tm')
    (Ss:  store_ptr c sm p v' = Some sm'),
      load_values_related tm' sm'.
Proof.
  intros. intros p' c'. specialize (LVR p' c').
  destruct (ranges_disjoint_dec (range_of_chunk p c) 
                                (range_of_chunk p' c')) as [D|O].
    by rewrite <- (load_store_other Ss), <- (load_store_other St).
  destruct (range_eq_dec (range_of_chunk p c) (range_of_chunk p' c')).
    inv e.
    assert (Esc: size_chunk c = size_chunk c')
      by (by destruct c; destruct c'; compute in H1).
    rewrite (load_store_similar St Esc), (load_store_similar Ss Esc).
    destruct compatible_chunks. by apply Val.load_result_lessdef.
    vauto.
  destruct (load_ptr c' sm' p') as [sv'|] _eqn : SL'.
    pose proof SL' as SL''. 
    rewrite (load_store_overlap Ss O n) in SL''. inv SL''.
      destruct (load_ptr c' sm p') as [sv|] _eqn : SL. 
        destruct (load_ptr c' tm' p') as [tv'|] _eqn : TL;
          destruct (load_ptr c' tm p') as [tv|] _eqn : TL'; try done.
        apply load_chunk_allocated_noneD in TL; apply load_chunk_allocated_someD in TL'.
        elim TL. by apply -> (store_preserves_chunk_allocation St p' c').
      apply load_chunk_allocated_someD in SL'; apply load_chunk_allocated_noneD in SL.
      elim SL. by apply <- (store_preserves_chunk_allocation Ss p' c').
    by apply load_chunk_allocated_someD in SL''.
  by destruct (load_ptr c' tm' p').
Qed.

Lemma irrelevant_preserves_load_rel:
  forall tm sm tm' sm' bi
    (LVR:  load_values_related tm sm)
    (NSR:  non_stack_mem_related tm sm)
    (ABIt: apply_buffer_item bi tm = Some tm')
    (ABIs: apply_buffer_item bi sm = Some sm')
    (BIIR: buffer_item_irrelevant bi),
      load_values_related tm' sm'.
Proof.
  intros. intros p' c'. specialize (LVR p' c').
  (buffer_item_cases (destruct bi as [p c v|p n k|p k]) Case);
    simpl in ABIt, ABIs, BIIR.
 
  Case "BufferedWrite". done.

  Case "BufferedAlloc".
    destruct (ranges_disjoint_dec (range_of_chunk p' c') (p, n)) as [D|O].
      by rewrite (load_alloc_other ABIt), (load_alloc_other ABIs).
    destruct (range_inside_dec (range_of_chunk p' c') (p, n)) as [RI|NRI].
      destruct (load_ptr c' sm' p') as [sv'|] _eqn : SL'.
        destruct (load_chunk_allocated_someD SL').
        by rewrite (load_alloc_inside ABIt); 
          rewrite (load_alloc_inside ABIs) in SL'; vauto.
      by destruct (load_ptr c' tm' p').
    by rewrite (load_alloc_overlap ABIt), (load_alloc_overlap ABIs).

  Case "BufferedFree".
    assert (RAn: exists n, range_allocated (p, n) k tm /\
                           range_allocated (p, n) k sm).
      destruct (free_someD ABIt) as [n RA].
      eexists. split. edone.
      specialize (NSR (p, n) k).
      destruct k; try done; by apply NSR.
    destruct RAn as [n [RAt RAs]].
    destruct (ranges_disjoint_dec (range_of_chunk p' c') (p, n)) as [D|O].
      by rewrite (load_free_other ABIt RAt D), (load_free_other ABIs RAs D).
    by rewrite (load_free_overlap ABIt RAt O), (load_free_overlap ABIs RAs O).
Qed.

(* Partition injectivity *)
Definition partition_injective  (tp : list arange)
                                (sp : list arange) : Prop :=
  forall r (IN : In r sp),
    exists r', range_inside r r' /\ In r' tp.

Lemma alloc_src_partition_injective:
  forall r' r tp sp
    (RIr:  range_inside r' r)
    (INtp: In r tp)
    (PI:   partition_injective tp sp),
      partition_injective tp (r'::sp).
Proof.
  intros. 
  intros ri IN. simpl in IN. destruct IN as [E | IN].
    inv E. eexists. eby split.
  eby eapply PI.
Qed.

Lemma alloc_tgt_partition_injective:
  forall r tp sp
    (PI:   partition_injective tp sp),
      partition_injective (r::tp) sp.
Proof.
  intros. 
  intros r' IN. destruct (PI r' IN) as [ri (RI' & IN')].
  eexists. split. edone. by right.
Qed.

Lemma free_tgt_partition_injective:
  forall r tp sp
    (RNIN: range_not_in r sp)
    (MR:   forall r' (IN: In r' sp), range_non_empty r')
    (PI:   partition_injective (r::tp) sp),
      partition_injective tp sp.
Proof.
  intros. 
  intros r' IN. destruct (PI r' IN) as [ri (RI' & IN')].
  simpl in IN'. destruct IN' as [<- | IN']; eauto.
  by exploit ranges_overlap_refl; eauto using disjoint_inside_disjoint_l.
Qed.

Lemma free_src_partition_injective:
  forall r tp sp
    (PI:   partition_injective tp (r::sp)),
      partition_injective tp sp.
Proof.
  intros. 
  intros r' IN. apply (PI r' (in_cons _ _ _ IN)). 
Qed.

Inductive tso_related_witt  (ts : tso_state)
                            (tp : partitioning)
                            (ss : tso_state) 
                            (sp : partitioning)
                            : Prop :=
| tso_related_witt_intro: forall
  (* Non-stack allocations are the same *)
  (NSMR: non_stack_mem_related ts.(tso_mem) ss.(tso_mem))
  (* Memory contents are related *)
  (LR  : load_values_related ts.(tso_mem) ss.(tso_mem))
  (* Memory restrictions are the same *)
  (MR  : mrestr ts.(tso_mem) = mrestr ss.(tso_mem))
  (* cstm and csmmp are partitionings consistent with the memory *)
  (MRPt: mem_related_with_partitioning ts.(tso_mem) tp)
  (MRPs: mem_related_with_partitioning ss.(tso_mem) sp)
  (* Partitions must be injective *)
  (PI  : forall t, partition_injective (tp t) (sp t))
  (* Buffers must be related *)
  (BR  : forall t, 
            buffers_related (ts.(tso_buffers) t) (tp t)
                            (ss.(tso_buffers) t) (sp t)),
  tso_related_witt ts tp ss sp.

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

Lemma irrelevant_preserves_mem_partitioning:
  forall bi m m' part
    (BIIR: buffer_item_irrelevant bi)
    (MRWP: mem_related_with_partitioning m part)
    (ABI:  apply_buffer_item bi m = Some m'),
      mem_related_with_partitioning m' part.
Proof.     
  intros.
  by destruct bi as [|p n []|p []]; try done; simpl in *;
      try (by eapply alloc_ptr_non_stack_preserves_mem_partitioning; 
              try edone);
      eapply free_ptr_non_stack_preserves_mem_partitioning; try edone.
Qed.

(** Preservation of tso_related_witt *)
Lemma irrelevant_preserves_tso_related_witt:
  forall ts tp ss sp t btrest bsrest tm' sm' bi
    (REL:  tso_related_witt ts tp ss sp)
    (BIIR: buffer_item_irrelevant bi)
    (ABIt: apply_buffer_item bi ts.(tso_mem) = Some tm')
    (ABIs: apply_buffer_item bi ss.(tso_mem) = Some sm')
    (Bt:   ts.(tso_buffers) t = bi :: btrest)
    (Bs:   ss.(tso_buffers) t = bi :: bsrest)
    (BRr:  buffers_related btrest (tp t) bsrest (sp t)),
      tso_related_witt 
        (mktsostate (tupdate t btrest ts.(tso_buffers)) tm') tp
        (mktsostate (tupdate t bsrest ss.(tso_buffers)) sm') sp.
Proof.        
  intros. inv REL.
  constructor.
  - eby eapply sim_irrelevant_preserves_non_stack_mem_related.
  - eby eapply irrelevant_preserves_load_rel.
  - by simpl; rewrite (mem_consistent_with_restr_apply_item ABIt),
                      (mem_consistent_with_restr_apply_item ABIs).
  - eby eapply irrelevant_preserves_mem_partitioning.
  - eby eapply irrelevant_preserves_mem_partitioning.
  - done.
  - intro t'; simpl.
    destruct (peq t' t) as [<- | N].
      by rewrite !tupdate_s. 
    by specialize (BR t'); rewrite !tupdate_o. 
Qed.


Lemma write_preserves_tso_related_witt:
  forall ts tp ss sp t btrest bsrest tm' sm' p c v v'
    (REL:  tso_related_witt ts tp ss sp)
    (ABIt: apply_buffer_item (BufferedWrite p c v) ts.(tso_mem) = Some tm')
    (ABIs: apply_buffer_item (BufferedWrite p c v') ss.(tso_mem) = Some sm')
    (LD:   Val.lessdef v' v)
    (Bt:   ts.(tso_buffers) t = BufferedWrite p c v :: btrest)
    (Bs:   ss.(tso_buffers) t = BufferedWrite p c v' :: bsrest)
    (BRr:  buffers_related btrest (tp t) bsrest (sp t)),
      tso_related_witt 
        (mktsostate (tupdate t btrest ts.(tso_buffers)) tm') tp
        (mktsostate (tupdate t bsrest ss.(tso_buffers)) sm') sp.
Proof.
  intros. inv REL.
  constructor.
  - eby eapply non_stack_mem_rel_preserved_by_stack_or_write_tgt; try edone;
    eapply non_stack_mem_rel_preserved_by_stack_or_write.
  - eby eapply write_preserves_load_rel.
  - by simpl; rewrite (mem_consistent_with_restr_apply_item ABIt),
                      (mem_consistent_with_restr_apply_item ABIs).
  - eby eapply store_ptr_preserves_mem_partitioning.
  - eby eapply store_ptr_preserves_mem_partitioning.
  - done.
  - intro t'; simpl.
    destruct (peq t' t) as [<- | N].
      by rewrite !tupdate_s. 
    by specialize (BR t'); rewrite !tupdate_o. 
Qed.

Lemma mrwp_alloc_in:
  forall {m part r} 
    (MRWP: mem_related_with_partitioning m part)
    (RA:   range_allocated r MObjStack m),
      exists t, In r (part t).
Proof.  
  intros.
  destruct MRWP as (_ & _ & A).
  by apply <- A.
Qed.  

Lemma mrwp_in_alloc:
  forall {m part r t}
    (MRWP: mem_related_with_partitioning m part)
    (IN:   In r (part t)),
      range_allocated r MObjStack m.
Proof.  
  intros.
  destruct MRWP as (_ & _ & A).
  apply -> A; vauto.
Qed.  

Lemma local_write_preserves_tso_related_witt:
  forall ts tp ss sp t btrest tm' p c v 
    (REL:  tso_related_witt ts tp ss sp)
    (ABIt: apply_buffer_item (BufferedWrite p c v) ts.(tso_mem) = Some tm')
    (CI:   chunk_inside_range_list p c (tp t))
    (CNI:  range_not_in (range_of_chunk p c) (sp t))
    (Bt:   ts.(tso_buffers) t = BufferedWrite p c v :: btrest)
    (BRr:  buffers_related btrest (tp t) (tso_buffers ss t) (sp t)),
      tso_related_witt 
        (mktsostate (tupdate t btrest ts.(tso_buffers)) tm') tp
        ss sp.
Proof.
  intros. inv REL.
  destruct (chunk_inside_range_listD CI) as [rt (INt & RIt)].
  pose proof (mrwp_in_alloc MRPt INt) as RAt.
  constructor.
  - eby eapply non_stack_mem_rel_preserved_by_stack_or_write_tgt; try edone.  - eapply local_write_preserves_load_rel; try edone. 
    intros r k RA. specialize (NSMR r k). 
    destruct k; try (by eapply disjoint_inside_disjoint_l, RIt;
      apply NSMR in RA;
        destruct (ranges_are_disjoint RAt RA) as [[_ N] | X]).
    destruct (mrwp_alloc_in MRPs RA) as [t' RAt'].
    destruct (peq t' t) as [-> | N]. 
      eby eapply CNI.
    destruct (PI t' _ RAt') as [rt' (RIrt' & INrt')].
    eapply disjoint_inside_disjoint_l, RIt.
    eapply disjoint_inside_disjoint_r, RIrt'.
    apply ranges_disjoint_comm.
    apply (proj1 MRPt _ _ N _ INrt' _ INt).
  - by simpl; rewrite (mem_consistent_with_restr_apply_item ABIt).
  - eby eapply store_ptr_preserves_mem_partitioning.
  - done.
  - done.
  - intro t'; simpl.
    destruct (peq t' t) as [<- | N].
      by rewrite !tupdate_s. 
    by specialize (BR t'); rewrite !tupdate_o. 
Qed.

Lemma salloc_preserves_tso_related_witt:
  forall ts tp ss sp t bsrest sm' p n r
    (REL:  tso_related_witt ts tp ss sp)
    (ABIs: apply_buffer_item (BufferedAlloc p n MObjStack) 
                             ss.(tso_mem) = Some sm')
    (Bs:   ss.(tso_buffers) t = BufferedAlloc p n MObjStack :: bsrest)
    (RNIN: range_not_in (p, n) (sp t))
    (RIr:  range_inside (p, n) r)
    (INtp: In r (tp t)) 
    (VAR:  valid_alloc_range (p, n))
    (BRr:  buffers_related (tso_buffers ts t) (tp t) 
                           bsrest ((p, n)::(sp t))),
      tso_related_witt 
        ts tp
        (mktsostate (tupdate t bsrest ss.(tso_buffers)) sm') 
        (tupdate t ((p, n)::(sp t)) sp).
Proof.
  intros. inv REL.
  constructor. 
  - eby eapply non_stack_mem_rel_preserved_by_stack_or_write.
  - simpl in *. 
    eapply alloc_ptr_src_preserves_load_rel; try edone.
    eby eapply mrwp_in_alloc.
  - by simpl; rewrite (mem_consistent_with_restr_apply_item ABIs).
  - done.
  - simpl in *.
    eby eapply alloc_ptr_stack_preserves_mem_partitioning.
  - intro t'.
    by unfold tupdate; destruct (peq t' t) as [<- | N];
      eauto using alloc_src_partition_injective.
  - intro t'; simpl.
    destruct (peq t' t) as [<- | N].
      by rewrite !@tupdate_s. 
    by specialize (BR t'); rewrite !@tupdate_o. 
Qed.

Lemma sfree_preserves_tso_related_witt:
  forall ts tp ss sp t bsrest sptrest sm' p n
    (REL:  tso_related_witt ts tp ss sp)
    (ABIs: apply_buffer_item (BufferedFree p MObjStack) 
                             ss.(tso_mem) = Some sm')
    (Bs:   ss.(tso_buffers) t = BufferedFree p MObjStack :: bsrest)
    (Bspt: sp t = (p, n)::sptrest)
    (BRr:  buffers_related (tso_buffers ts t) (tp t) 
                           bsrest sptrest),
      tso_related_witt 
        ts tp
        (mktsostate (tupdate t bsrest ss.(tso_buffers)) sm') 
        (tupdate t sptrest sp).
Proof.
  intros. inv REL.
  constructor. 
  - eby eapply non_stack_mem_rel_preserved_by_stack_or_write.
  - simpl in *. 
    eapply free_ptr_src_preserves_load_rel; try edone.
  - by simpl; rewrite (mem_consistent_with_restr_apply_item ABIs).
  - done.
  - simpl in *.
    eby eapply free_ptr_preserves_mem_partitioning.
  - intro t'.
    unfold tupdate; destruct (peq t' t) as [<- | N]; eauto.
    specialize (PI t'); rewrite Bspt in PI.
    eby eapply free_src_partition_injective.
  - intro t'; simpl.
    destruct (peq t' t) as [<- | N].
      by rewrite !@tupdate_s. 
    by specialize (BR t'); rewrite !@tupdate_o. 
Qed.

Lemma talloc_preserves_tso_related_witt:
  forall ts tp ss sp t btrest tm' p n
    (REL:  tso_related_witt ts tp ss sp)
    (ABIt: apply_buffer_item (BufferedAlloc p n MObjStack) 
                             ts.(tso_mem) = Some tm')
    (Bt:   ts.(tso_buffers) t = BufferedAlloc p n MObjStack :: btrest)
    (RNIN: range_not_in (p, n) (tp t))
    (VAR:  valid_alloc_range (p, n))
    (BRr:  buffers_related btrest ((p, n)::(tp t))
                           (tso_buffers ss t) (sp t)),
      tso_related_witt 
        (mktsostate (tupdate t btrest ts.(tso_buffers)) tm') 
        (tupdate t ((p, n)::(tp t)) tp)
        ss sp.
Proof.
  intros. inv REL.
  constructor. 
  - eby eapply non_stack_mem_rel_preserved_by_stack_or_write_tgt.
  - simpl in *. 
    eapply alloc_ptr_tgt_preserves_load_rel; try edone.
    intros r k RA.
    specialize (NSMR r k).
    destruct k; try (eby apply NSMR in RA; 
        eapply ranges_disjoint_comm, alloc_allocatedD).
    destruct (mrwp_alloc_in MRPs RA) as [t' INt'].
    destruct (PI _ _ INt') as [r' [RIr' INr']].    
    eapply disjoint_inside_disjoint_l, RIr'.
    eapply ranges_disjoint_comm, alloc_allocatedD; try edone.
    eby eapply mrwp_in_alloc.
  - by simpl; rewrite (mem_consistent_with_restr_apply_item ABIt).
  - simpl in *.
    eby eapply alloc_ptr_stack_preserves_mem_partitioning.
  - done.
  - intro t'.
    by unfold tupdate; destruct (peq t' t) as [<- | N];
      eauto using alloc_tgt_partition_injective.
  - intro t'; simpl.
    destruct (peq t' t) as [<- | N].
      by rewrite !@tupdate_s. 
    by specialize (BR t'); rewrite !@tupdate_o. 
Qed.

Lemma tfree_preserves_tso_related_witt:
  forall ts tp ss sp t btrest btptrest tm' p n
    (REL:  tso_related_witt ts tp ss sp)
    (ABIt: apply_buffer_item (BufferedFree p MObjStack) 
                             ts.(tso_mem) = Some tm')
    (Bt:   ts.(tso_buffers) t = BufferedFree p MObjStack :: btrest)
    (Etpt: tp t = (p, n)::btptrest)
    (RNIN: range_not_in (p, n) (sp t))
    (BRr:  buffers_related btrest btptrest
                           (tso_buffers ss t) (sp t)),
      tso_related_witt 
        (mktsostate (tupdate t btrest ts.(tso_buffers)) tm') 
        (tupdate t btptrest tp)
        ss sp.
Proof.
  intros. inv REL.
  constructor. 
  - eby eapply non_stack_mem_rel_preserved_by_stack_or_write_tgt.
  - simpl in *. 
    assert (INpn: In (p, n) (tp t)) by (by rewrite Etpt; left).
    pose proof (mrwp_in_alloc MRPt INpn) as RApn.
    eapply free_ptr_tgt_preserves_load_rel; try edone.
    intros r k RA.
    specialize (NSMR r k).
    destruct k;
      try (by apply NSMR in RA;
        destruct (ranges_are_disjoint RA RApn) as [[_ ?]|]).
    destruct (mrwp_alloc_in MRPs RA) as [t' INt'].
    destruct (peq t' t) as [<- | N].
      by apply ranges_disjoint_comm; eauto.
    destruct (PI _ _ INt') as [r' [RIr' INr']].
    eapply disjoint_inside_disjoint_l, RIr'.
    apply (proj1 MRPt _ _ N _ INr' _ INpn).
  - by simpl; rewrite (mem_consistent_with_restr_apply_item ABIt).
  - simpl in *.
    eby eapply free_ptr_preserves_mem_partitioning.
  - done.
  - intro t'.
    unfold tupdate; destruct (peq t' t) as [<- | N]; eauto.
    eapply free_tgt_partition_injective; try edone.
      intros r' IN'. 
      eby eapply valid_alloc_range_non_empty, allocated_range_valid,
        mrwp_in_alloc.
    specialize (PI t'). by rewrite Etpt in PI.
  - intro t'; simpl.
    destruct (peq t' t) as [<- | N].
      by rewrite !@tupdate_s. 
    by specialize (BR t'); rewrite !@tupdate_o. 
Qed.

(* Opposite simulation (to show unbuffer safety for allocations *)
Inductive tso_related_witt_sf  (ts : tso_state)
                               (tp : partitioning)
                               (ss : tso_state) 
                               (sp : partitioning)
                               : Prop :=
| tso_related_witt_sf_intro: forall
  (US:   unbuffer_safe ts)
  (FS:   tso_fin_sup ss)
  (TREL: tso_related_witt ts tp ss sp),
    tso_related_witt_sf ts tp ss sp.

Definition tso_related_sf ts ss :=
  exists tp, exists sp, tso_related_witt_sf ts tp ss sp.

Lemma sf_rel_sim:
  forall ts t ss bi b m'
    (TREL: tso_related_sf ts ss)
    (Bt:   ss.(tso_buffers) t = bi :: b)
    (ABIs: apply_buffer_item bi ss.(tso_mem) = Some m'),
    exists ts', tso_related_sf ts' (mktsostate (tupdate t b ss.(tso_buffers)) m').
Proof.
  intros. destruct TREL as [tp [sp REL]].
  assert (BRt:
    buffers_related (tso_buffers ts t) (tp t) (tso_buffers ss t) (sp t)).
    inv REL. inv TREL. by eauto.
  remember (tso_buffers ts t) as tb.
  remember (tp t) as tpt.
  remember (tso_buffers ss t) as sb.
  remember (sp t) as spt.
  revert tp ts Heqtpt Heqtb REL.

  (buffers_related_cases (induction BRt) Case); intros; inv Bt.
 
  Case "buffers_related_irrelevant".
    inv REL. 
    assert (A: exists tm', apply_buffer_item bi ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    exists (mktsostate (tupdate t tb ts.(tso_buffers)) tm').
    exists tp0. exists sp.
    constructor. done.
    eby eapply tso_fin_sup_tupdate.
    eby eapply irrelevant_preserves_tso_related_witt.

  Case "buffers_related_write".
    inv REL. 
    assert (A: exists tm', apply_buffer_item (BufferedWrite p c v) ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    exists (mktsostate (tupdate t tb ts.(tso_buffers)) tm').
    exists tp0. exists sp.
    constructor. done.
    eby eapply tso_fin_sup_tupdate.
    eby eapply write_preserves_tso_related_witt.

  Case "buffers_related_local_write".
    inv REL. 
    assert (A: exists tm', apply_buffer_item (BufferedWrite p c v) ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    eapply IHBRt; try done.
    - instantiate (1 := mktsostate (tupdate t tb ts.(tso_buffers)) tm').
      by simpl; rewrite tupdate_s.
    - constructor. done. done.
      eby eapply local_write_preserves_tso_related_witt.

  Case "buffers_related_salloc".
    inv REL.
    eexists. eexists. eexists.
    econstructor. edone. 
    eby eapply tso_fin_sup_tupdate.
    eby eapply salloc_preserves_tso_related_witt.

  Case "buffers_related_sfree".
    inv REL.
    eexists. eexists. eexists.
    econstructor. edone.
    eby eapply tso_fin_sup_tupdate.
    eby eapply sfree_preserves_tso_related_witt; try edone; symmetry. 
    
  Case "buffers_related_talloc".
    inv REL. 
    assert (A: exists tm', apply_buffer_item (BufferedAlloc p n MObjStack) ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    eapply IHBRt; try done.
    - instantiate (1 := tupdate t ((p, n)::(tp0 t)) tp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t tb ts.(tso_buffers)) tm').
      by simpl; rewrite tupdate_s.
    - constructor. done. done.
      eby eapply talloc_preserves_tso_related_witt.

  Case "buffers_related_tfree".
    inv REL. 
    assert (A: exists tm', apply_buffer_item (BufferedFree p MObjStack) ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    eapply IHBRt.
    - done.
    - done.
    - done.
    - instantiate (1 := tupdate t tp tp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t tb ts.(tso_buffers)) tm').
      by simpl; rewrite tupdate_s.
    - constructor. done. done.
      eby eapply tfree_preserves_tso_related_witt; try edone; symmetry.
Qed.


Lemma alloc_stack_src_buff_impl_part_update_succ:
  forall ts tp ss sp t bi sbr
    (REL: tso_related_witt_sf ts tp ss sp)
    (Bs:  ss.(tso_buffers) t = bi :: sbr),
      part_update bi (sp t) <> None.
Proof.
  intros.
  assert (BRt:
    buffers_related (tso_buffers ts t) (tp t) (tso_buffers ss t) (sp t)).
    inv REL. inv TREL. by eauto.
  remember (tso_buffers ts t) as tb.
  remember (tp t) as tpt.
  remember (tso_buffers ss t) as sb.
  remember (sp t) as spt.
  revert tp ts Heqtpt Heqtb REL.

  (buffers_related_cases (induction BRt) Case); intros; inv Bs.
 
  Case "buffers_related_irrelevant".
    by rewrite part_update_irrelevant.

  Case "buffers_related_write". done.

  Case "buffers_related_local_write".
    inv REL. 
    assert (A: exists tm', apply_buffer_item (BufferedWrite p c v) ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    eapply IHBRt; try done.
    - instantiate (1 := mktsostate (tupdate t tb ts.(tso_buffers)) tm').
      by simpl; rewrite tupdate_s.
    - constructor. done. done.
      eby eapply local_write_preserves_tso_related_witt.

  Case "buffers_related_salloc".
    simpl. destruct valid_alloc_range_dec; [|done].
    by destruct range_in_dec as [[? [IN O]]|]; eauto.

  Case "buffers_related_sfree".
    simpl. by destruct Ptr.eq_dec.
    
  Case "buffers_related_talloc".
    inv REL. 
    assert (A: exists tm', apply_buffer_item (BufferedAlloc p n MObjStack) ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    eapply IHBRt; try done.
    - instantiate (1 := tupdate t ((p, n)::(tp0 t)) tp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t tb ts.(tso_buffers)) tm').
      by simpl; rewrite tupdate_s.
    - constructor. done. done.
      eby eapply talloc_preserves_tso_related_witt.

  Case "buffers_related_tfree".
    inv REL. 
    assert (A: exists tm', apply_buffer_item (BufferedFree p MObjStack) ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    eapply IHBRt; auto.
    - instantiate (1 := tupdate t tp tp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t tb ts.(tso_buffers)) tm').
      by simpl; rewrite tupdate_s.
    - constructor. done. done.
      eby eapply tfree_preserves_tso_related_witt; try edone; symmetry.
Qed.  

Lemma tso_pc_rel_valid_alloc_range_src_buff:
  forall {ts tp ss sp t p n k sbr}
    (REL: tso_related_witt_sf ts tp ss sp)
    (Bs:  ss.(tso_buffers) t = BufferedAlloc p n k :: sbr),
      valid_alloc_range (p, n) /\
      restricted_pointer p (tso_mem ss).
Proof.
  intros.
  assert (BRt:
    buffers_related (tso_buffers ts t) (tp t) (tso_buffers ss t) (sp t)).
    inv REL. inv TREL. by eauto.
  remember (tso_buffers ts t) as tb.
  remember (tp t) as tpt.
  remember (tso_buffers ss t) as sb.
  remember (sp t) as spt.
  revert tp ts Heqtpt Heqtb REL.

  (buffers_related_cases (induction BRt) Case); intros; inv Bs.
 
  Case "buffers_related_irrelevant".
    inv REL. inv US. destruct (ABIS _ _ _ (sym_eq Heqtb)) as [m' ABI].
    simpl in ABI; destruct (alloc_someD ABI) as (? & _ & ? & _).
    split. eby eapply allocated_range_valid. 
    unfold restricted_pointer. inv TREL. by rewrite <- MR.

  Case "buffers_related_local_write".
    inv REL. 
    assert (A: exists tm', apply_buffer_item (BufferedWrite p0 c v) ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    eapply IHBRt; try done.
    - instantiate (1 := mktsostate (tupdate t tb ts.(tso_buffers)) tm').
      by simpl; rewrite tupdate_s.
    - constructor. done. done.
      eby eapply local_write_preserves_tso_related_witt.

  Case "buffers_related_salloc". 
    split. done.
    inv REL. inv TREL.
    pose proof (mrwp_in_alloc MRPt INtp) as RA. destruct r as [[br or] nr].
    apply range_allocated_consistent_with_restr in RA.
    unfold restricted_pointer; rewrite <- MR.
    destruct p. destruct RIr. by subst.

  Case "buffers_related_talloc".
    inv REL. 
    assert (A: exists tm', apply_buffer_item (BufferedAlloc p0 n0 MObjStack) ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    eapply IHBRt; try done.
    - instantiate (1 := tupdate t ((p0, n0)::(tp0 t)) tp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t tb ts.(tso_buffers)) tm').
      by simpl; rewrite tupdate_s.
    - constructor. done. done.
      eby eapply talloc_preserves_tso_related_witt.

  Case "buffers_related_tfree".
    inv REL. 
    assert (A: exists tm', apply_buffer_item (BufferedFree p0 MObjStack) ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    eapply IHBRt; auto.
    - instantiate (1 := tupdate t tp tp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t tb ts.(tso_buffers)) tm').
      by simpl; rewrite tupdate_s.
    - constructor. done. done.
      eby eapply tfree_preserves_tso_related_witt; try edone; symmetry.
Qed.

Definition non_stack_kind (k : mobject_kind) :=
  match k with
    |  MObjStack => False
    | _ => True
  end.

Definition non_stack_item (bi : buffer_item) :=
  match bi with 
    | BufferedAlloc pi ni ki => non_stack_kind ki
    | BufferedFree pi ki => non_stack_kind ki
    | _ => False
  end.

Lemma irrelevant_src_buff_impl_tgt_success:
  forall ts ss t bi sbr
    (REL: tso_related_sf ts ss)
    (Bt:  ss.(tso_buffers) t = bi :: sbr)
    (NSI: non_stack_item bi),
    exists ts', exists tbr,
      tso_related_sf ts' ss /\
      ts'.(tso_buffers) t = bi :: tbr.
Proof.
  intros.
  destruct REL as [tp [sp REL]].
  assert (BRt:
    buffers_related (tso_buffers ts t) (tp t) (tso_buffers ss t) (sp t)).
    inv REL. inv TREL. by eauto.
  remember (tso_buffers ts t) as tb.
  remember (tp t) as tpt.
  remember (tso_buffers ss t) as sb.
  remember (sp t) as spt.
  revert tp ts Heqtpt Heqtb REL.

  (buffers_related_cases (induction BRt) Case); intros; inv Bt.

  Case "buffers_related_irrelevant".
    inversion REL; subst.
    assert (A: exists tm', apply_buffer_item bi ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    eexists. eexists. split. eexists; eexists; edone. eby symmetry.

  Case "buffers_related_write". done.

  Case "buffers_related_local_write".
    inv REL. 
    assert (A: exists tm', apply_buffer_item (BufferedWrite p c v) ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    eapply IHBRt; try done.
    - instantiate (1 := mktsostate (tupdate t tb ts.(tso_buffers)) tm').
      by simpl; rewrite tupdate_s.
    - constructor. done. done.
      eby eapply local_write_preserves_tso_related_witt.

  Case "buffers_related_salloc". done.

  Case "buffers_related_sfree". done.
    
  Case "buffers_related_talloc".
    inv REL. 
    assert (A: exists tm', apply_buffer_item (BufferedAlloc p n MObjStack) ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    eapply IHBRt; try done.
    - instantiate (1 := tupdate t ((p, n)::(tp0 t)) tp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t tb ts.(tso_buffers)) tm').
      by simpl; rewrite tupdate_s.
    - constructor. done. done.
      eby eapply talloc_preserves_tso_related_witt.

  Case "buffers_related_tfree".
    inv REL. 
    assert (A: exists tm', apply_buffer_item (BufferedFree p MObjStack) ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    eapply IHBRt; auto.
    - instantiate (1 := tupdate t tp tp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t tb ts.(tso_buffers)) tm').
      by simpl; rewrite tupdate_s.
    - constructor. done. done.
      eby eapply tfree_preserves_tso_related_witt; try edone; symmetry.
Qed.

Lemma tso_rel_sf_range_allocated:
  forall ts ss p n k,
    tso_related_sf ts ss ->
    range_allocated (p, n) k ss.(tso_mem) ->
    exists r',
      range_inside (p, n) r' /\
      range_allocated r' k ts.(tso_mem). 
Proof.
  intros ts ss p n k [tp [sp TWREL]] RA.
  inv TWREL. inv TREL.
  destruct k;
    try (by exists (p, n); split; 
      [apply range_inside_refl | ];
      try apply (NSMR (p, n) MObjGlobal); 
        try apply (NSMR (p, n) MObjHeap)).
  destruct (mrwp_alloc_in MRPs RA) as [t INPs].
  destruct (PI _ _ INPs) as [r [RIN INPt]].
  exists r. split. done. apply (mrwp_in_alloc MRPt INPt).
Qed.

Lemma tso_rel_sf_non_stack_alloc_contr:
  forall ts ss r k pi ni ki b t,
  tso_related_sf ts ss ->
  range_allocated r k (tso_mem ss) ->
  ranges_overlap (pi, ni) r ->
  tso_buffers ss t = BufferedAlloc pi ni ki :: b ->
  non_stack_kind ki ->
  False.
Proof.
  intros ts ss r k pi ni ki b t TREL RA RO Bs NS.
  destruct (irrelevant_src_buff_impl_tgt_success _ _ _ _ _
    TREL Bs NS) as [ts' [tsr [TREL' BD']]].
  pose proof TREL' as [tp [sp REL]].  inv REL.
  destruct (unbuffer_unbuffer_safe US BD') as [tm' [ABIT _]].
  unfold apply_buffer_item in ABIT. 
  pose proof (alloc_cond_spec (pi, ni) ki (tso_mem ts')) as AST'.
  rewrite ABIT in AST'. destruct AST' as (_ & _ & RP' & RNA') .
  destruct r as [p n].
  destruct (tso_rel_sf_range_allocated _ _ _ _ _ TREL' RA) 
    as [rt [RIt RAt]].
  eapply RNA'. 2 : apply RAt.
  eapply ranges_overlap_comm, overlap_inside_overlap.
  apply ranges_overlap_comm, RO. done.
Qed.


Lemma alloc_stack_src_buff_impl_tgt_partition:
  forall ts ss t p n sbr
    (REL: tso_related_sf ts ss)
    (Bt:  ss.(tso_buffers) t = BufferedAlloc p n MObjStack :: sbr),
    exists ts', exists r, exists tp, exists sp,
      tso_related_witt_sf ts' tp ss sp /\
      range_inside (p, n) r /\
      In r (tp t) /\
      range_not_in (p, n) (sp t).
Proof.
  intros.
  destruct REL as [tp [sp REL]].
  assert (BRt:
    buffers_related (tso_buffers ts t) (tp t) (tso_buffers ss t) (sp t)).
    inv REL. inv TREL. by eauto.
  remember (tso_buffers ts t) as tb.
  remember (tp t) as tpt.
  remember (tso_buffers ss t) as sb.
  remember (sp t) as spt.
  revert tp ts Heqtpt Heqtb REL.

  (buffers_related_cases (induction BRt) Case); intros; inv Bt.

  Case "buffers_related_irrelevant". done.

  Case "buffers_related_local_write".
    inv REL. 
    assert (A: exists tm', apply_buffer_item (BufferedWrite p0 c v) ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    eapply IHBRt; try done.
    - instantiate (1 := mktsostate (tupdate t tb ts.(tso_buffers)) tm').
      by simpl; rewrite tupdate_s.
    - constructor. done. done.
      eby eapply local_write_preserves_tso_related_witt.

  Case "buffers_related_salloc". 
    eexists; eexists; eexists; eexists.
    by repeat (split; try edone).

  Case "buffers_related_talloc".
    inv REL. 
    assert (A: exists tm', apply_buffer_item (BufferedAlloc p0 n0 MObjStack) ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    eapply IHBRt; try done.
    - instantiate (1 := tupdate t ((p0, n0)::(tp0 t)) tp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t tb ts.(tso_buffers)) tm').
      by simpl; rewrite tupdate_s.
    - constructor. done. done.
      eby eapply talloc_preserves_tso_related_witt.

  Case "buffers_related_tfree".
    inv REL. 
    assert (A: exists tm', apply_buffer_item (BufferedFree p0 MObjStack) ts.(tso_mem) = Some tm' /\ 
                           unbuffer_safe (mktsostate (tupdate t tb ts.(tso_buffers)) tm')).
      simpl in US.
      by destruct (unbuffer_unbuffer_safe US (sym_eq Heqtb)) 
        as [? (? & ?)]; vauto.
    destruct A as [tm' (ABIt & USt)].
    eapply IHBRt; auto.
    - instantiate (1 := tupdate t tp tp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t tb ts.(tso_buffers)) tm').
      by simpl; rewrite tupdate_s.
    - constructor. done. done.
      eby eapply tfree_preserves_tso_related_witt; try edone; symmetry.
Qed.

Lemma pointer_in_range_list_in:
  forall p l,
    pointer_in_range_list p l = true ->
    exists n, In (p, n) l.
Proof.
  intros p. induction l as [|[p' n'] l IH]. done.
  simpl; destruct (Ptr.eq_dec p p') as [-> | N].
    intro. eexists. left; reflexivity.
  intro H. destruct (IH H). eexists; right; eassumption.
Qed.

Lemma alloc_unbuffer_safe:
  forall p n k t ss ts ss' ab
    (REL: tso_related_sf ts ss)
    (USs: unbuffer_safe ss')
    (Eab: ab = nil \/ ab = BufferedAlloc p n k :: nil)
    (Ebs: ss.(tso_buffers) t = ss'.(tso_buffers) t ++ ab)
    (Ebo: forall t', t' <> t -> ss.(tso_buffers) t' = ss'.(tso_buffers) t')
    (RAS: forall r k (RA: range_allocated r k ss'.(tso_mem)),
                      range_allocated r k ss.(tso_mem)),
      unbuffer_safe ss.
Proof.
  intros until 1.
  generalize REL; intros (aa & bb & [_ FS _]); clear aa bb.
  destruct FS as [l [NDUP DOM]].

  remember (buffers_measure l ss.(tso_buffers)) as bsize.
  revert ss ts ss' ab REL DOM NDUP Heqbsize.
  induction bsize as [|bsize IH]; intros.

  (* Base case *)
  by constructor; [intros t' bi b Bs | intros t' bi b m' Bs];
    destruct (In_dec peq t' l) as [IN | NIN]; 
      try (by rewrite (buffer_measure_zero _ _ _ Heqbsize IN) in Bs);
        rewrite DOM in Bs.

  (* Step case *)
  pose proof REL as [tp [sp TREL]].
  constructor.
  intros t' bi b Bs.
  destruct USs as [ss' MABI US].
  destruct (apply_buffer_item bi (tso_mem ss)) as [m|] _eqn : FAIL. eby eexists.
  byContradiction.
  destruct bi as [pi ci vi | pi ni ki | pi ki].
      (* Write succeeds because we have more stuff allocated *)
      assert (Bs' : exists br, tso_buffers ss' t' = BufferedWrite pi ci vi :: br).
        destruct (peq t' t) as [-> | N].
          rewrite Bs in Ebs. 
          destruct (tso_buffers ss' t) as [| bi' br']. by destruct Eab as [-> | ->].
          rewrite <- app_comm_cons in Ebs. inv Ebs.
          eby eexists.
        rewrite (Ebo _ N) in Bs.
        eby eexists.
      destruct Bs' as [br Bs'].
      destruct (MABI _ _ _ Bs') as [m' ABI].
      simpl in ABI. 
      pose proof (store_chunk_allocated_spec ci (tso_mem ss') pi vi) as SS'. 
      pose proof (store_chunk_allocated_spec ci (tso_mem ss) pi vi) as SS.
      rewrite ABI in SS'. destruct SS' as [[r' [k' [RI' RA']]] CA].
      apply RAS in RA'.
      simpl in FAIL; rewrite FAIL in SS. apply SS.
      split. eexists; eexists; eby split. done.
    (* Allocation *)
    unfold apply_buffer_item in FAIL. apply alloc_noneD in FAIL.
    destruct (tso_pc_rel_valid_alloc_range_src_buff TREL Bs) as [VAR RS].
    destruct FAIL as [NVAR | [NRES | [r' [k' (RO' & RA')]]]].
      by elim NVAR.
      by elim NRES.
    destruct ki; try eby eapply tso_rel_sf_non_stack_alloc_contr.
    destruct (alloc_stack_src_buff_impl_tgt_partition _ _ _ _ _ _ REL Bs) 
      as [ts' [rt [tp' [sp' [TREL' [RI' [BD' NIP']]]]]]].
    inv TREL'. inv TREL0.
    assert (RAt:= mrwp_in_alloc MRPt BD'). 
    destruct k' as [] _eqn : Ek;
      try by specialize (NSMR r' k'); rewrite Ek in NSMR; apply NSMR in RA';
        destruct (ranges_are_disjoint RAt RA') as [[_ ?] | DISJ];
           try done; eapply ranges_disjoint_dont_overlap; 
             [apply DISJ | eby eapply overlap_inside_overlap].
    destruct (mrwp_alloc_in MRPs RA') as [tr INtr].
    destruct (peq tr t') as [-> | N].
      specialize (NIP' r' INtr).
      by pose proof (ranges_disjoint_dont_overlap _ _ NIP' RO').
    destruct r' as [p' n'].
    destruct (PI tr _ INtr) as [rt' [RIrt' INrt']].
    pose proof (proj1 MRPt _ _ N _ INrt') as DISJ.
    specialize (DISJ _ BD').
    eapply ranges_disjoint_dont_overlap.
    apply DISJ.
    eapply overlap_inside_overlap, RIrt'.
    by eapply ranges_overlap_comm, overlap_inside_overlap, RI'.        
  (* Free *)    
  pose proof (free_cond_spec pi ki (tso_mem ss)) as FS.
  unfold apply_buffer_item in FAIL. rewrite FAIL in FS.
  destruct ki as [] _eqn : Eki;
    try by pose proof (irrelevant_src_buff_impl_tgt_success _ _ _ _ _ 
        REL Bs) as TGSUCC;
      destruct (TGSUCC I) as [ts' [tbr [TREL' BD']]];
        destruct TREL' as [tp' [sp' TREL']]; inversion TREL'; inversion TREL0;
            destruct (unbuffer_unbuffer_safe US0 BD') as [tm' [ABIT _]];
                unfold apply_buffer_item in ABIT;
                  destruct (free_someD ABIT) as [n' RA'];
                      specialize (NSMR (pi, n') ki); rewrite Eki in NSMR; 
                        apply NSMR in RA'; specialize (FS _ RA').
  pose proof (alloc_stack_src_buff_impl_part_update_succ _ _ _ _ _ _ _
    TREL Bs) as PU.
  simpl in PU. destruct (sp t') as [|[px nx] rest] _eqn:Espt'. done.
  destruct Ptr.eq_dec as [|]; [|done].
  assert (INPs : In (px, nx) (sp t')). by rewrite Espt'; left.
  apply (FS nx). inv TREL. inv TREL0.
  apply (mrwp_in_alloc MRPs INPs).

  (* Proof of preservation of the induction hypothesis *)
  intros t' bi sbr sm' BD ABIs.
  pose proof (sf_rel_sim _ _ _ _ _ _ REL BD ABIs) as [ts' TREL'].
  destruct (In_dec peq t' l) as [INR | NINR].
    2: by rewrite DOM in BD.
  pose proof (preserve_dom_unbuffer _ _ _ _ _ BD DOM) as NDOM.
  destruct (measure_down_unbuffer _ _ _ _ _ NDUP BD INR) 
    as [s [BS SBS]].
  rewrite <- Heqbsize in SBS. inv SBS.
  destruct (peq t' t) as [-> | N].
    rewrite Ebs in BD. 
    destruct (tso_buffers ss' t) as [|bssh' bsst'] _eqn : Ebss'.
      simpl in BD. subst. destruct Eab as [|Eab]; [done|].
      inv Eab.
      eapply (IH _ _ ss') with (ab := nil); try edone. by left.
      simpl. by rewrite tupdate_s, Ebss'.
      intros tx Nx. simpl. by rewrite tupdate_o; [rewrite Ebo|]. 
      intros r' k' RA'. apply RAS in RA'. simpl.
      unfold apply_buffer_item in ABIs.
      eby eapply alloc_preserves_allocated.
    (* Unbuffering old stuff *)
    rewrite <- app_comm_cons in BD. inv BD.
    destruct (unbuffer_unbuffer_safe USs Ebss') as [ssm' [ABIss' US']].
    eapply (IH _ _ (mktsostate
      (tupdate t bsst' ss'.(tso_buffers)) ssm') ab); try edone.
    simpl. by rewrite ! tupdate_s.
    intros t' Nt'. simpl. by rewrite ! tupdate_o; [apply Ebo | | ].
    simpl. eby eapply sim_apply_item_preserves_alloc_impl.
  (* Unbuffering another thread *)
  pose proof BD as BD'. rewrite Ebo in BD'; [|done].
  destruct (unbuffer_unbuffer_safe USs BD') as [ssm' [ABIss' US']].
  eapply (IH _ _ (mktsostate 
    (tupdate t' sbr ss'.(tso_buffers)) ssm') ab); try edone.
  simpl. rewrite ! tupdate_o; try done; intro E; by rewrite E in N.
  intros t'' N''. simpl. 
    unfold tupdate. by destruct (peq t'' t'); try rewrite Ebo. 
  simpl. eby eapply sim_apply_item_preserves_alloc_impl.
Qed.


(** Unbuffer safety for free/write fail simulation. *)
Inductive tso_related_fw  (ts : tso_state)
                          (ss : tso_state) 
                          : Prop :=
| tso_related_witt_fw_intro: forall tp sp
  (USs:  unbuffer_safe ss)
  (* FS:   tso_fin_sup ss *)
  (REL: tso_related_witt ts tp ss sp),
    tso_related_fw ts ss.

Definition write_or_free (bi : buffer_item) :=
    match bi with
      | BufferedFree _ _ => True
      | BufferedWrite _ _ _ => True
      | _ => False 
    end.


Definition writes_or_frees (b : list buffer_item) :=
  forall bi (IN: In bi b), write_or_free bi.

Lemma tso_pc_related_unsafe_store_sim:
  forall ts ss t bi tbr
    (TREL: tso_related_fw ts ss)
    (TB:   ts.(tso_buffers) t = bi :: tbr)
    (WF:   write_or_free bi),
      apply_buffer_item bi ts.(tso_mem) <> None.
Proof.
  intros.
  inv TREL.
  assert (BRt:
    buffers_related (tso_buffers ts t) (tp t) (tso_buffers ss t) (sp t)).
    inv REL. by eauto.
  remember (tso_buffers ts t) as tb.
  remember (tp t) as tpt.
  remember (tso_buffers ss t) as sb.
  remember (sp t) as spt.
  revert sp ss Heqspt Heqsb USs (*FS*) REL.

  (buffers_related_cases (induction BRt) Case); intros; inv TB; intro ABIt.

  Case "buffers_related_irrelevant".
    destruct bi as [p c v|p n k|p k]; try done; [].
    destruct (unbuffer_unbuffer_safe USs (sym_eq Heqsb)) as [sm' [ABIs _]].
    simpl in ABIs, ABIt.
    destruct (free_someD ABIs) as [n RA].
    pose proof (free_noneD ABIt n).
    inv REL. specialize (NSMR (p, n) k).
    by destruct k; try done; apply NSMR in RA.

  Case "buffers_related_write".
    destruct (unbuffer_unbuffer_safe USs (sym_eq Heqsb)) as [sm' [ABIs _]].
    simpl in ABIt, ABIs.
    destruct (store_chunk_allocated_someD ABIs) as [[r' [k' [RI RA]]] PCAL].
    pose proof (store_chunk_allocated_noneD ABIt) as STS.
    elim STS. split; [|done]. inv REL. specialize (NSMR r' k').
    destruct k'; try (eby eexists; eexists; split; [|apply NSMR in RA]).
    destruct (mrwp_alloc_in MRPs RA) as [t' IN'].
    destruct (PI _ _ IN') as [rt (RIt & INt)].
    eexists. eexists. split. by eapply range_inside_trans, RIt.
    eby eapply mrwp_in_alloc.    

  Case "buffers_related_local_write".
    inv REL.
    pose proof (store_chunk_allocated_noneD ABIt) as STS.
    elim STS.
    split. destruct (chunk_inside_range_listD CI) as [rs (INs & RIs)].
    eexists. eexists. split. edone. eby eapply mrwp_in_alloc.
    edone.

  Case "buffers_related_salloc".
    inv REL.
    assert (A: exists sm', apply_buffer_item (BufferedAlloc p n MObjStack) ss.(tso_mem) = Some sm' /\ 
                           unbuffer_safe (mktsostate (tupdate t sb ss.(tso_buffers)) sm')).
      simpl in USs.
      by destruct (unbuffer_unbuffer_safe USs (sym_eq Heqsb)) 
        as [? (? & ?)]; vauto.
    destruct A as [sm' (ABIs & USs')].
    eapply IHBRt; try done.
    - instantiate (1 := tupdate t ((p, n)::(sp0 t)) sp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t sb ss.(tso_buffers)) sm').
      by simpl; rewrite tupdate_s.
    - done.
    (*- by eapply tso_fin_sup_tupdate.*)
    - eby eapply salloc_preserves_tso_related_witt.

  Case "buffers_related_sfree".
    inv REL.
    assert (A: exists sm', 
      apply_buffer_item (BufferedFree p MObjStack) ss.(tso_mem) = Some sm' /\ 
      unbuffer_safe (mktsostate (tupdate t sb ss.(tso_buffers)) sm')).
      simpl in USs.
      by destruct (unbuffer_unbuffer_safe USs (sym_eq Heqsb)) 
        as [? (? & ?)]; vauto.
    destruct A as [sm' (ABIs & USs')].
    eapply IHBRt; auto.
    - instantiate (1 := tupdate t sp sp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t sb ss.(tso_buffers)) sm').
      by simpl; rewrite tupdate_s.
    - done.
    (*- by eapply tso_fin_sup_tupdate.*)
    - eby eapply sfree_preserves_tso_related_witt; try edone; symmetry.

  Case "buffers_related_talloc". done.

  Case "buffers_related_tfree".
    inv REL.
    simpl in ABIt. 
    elim (free_noneD ABIt n).
    eapply (mrwp_in_alloc MRPt). instantiate (1 := t). rewrite <- Heqtpt.
    by left.
Qed.

Lemma tso_related_fw_sim:
  forall {bi ts tm' tbr ss t}
    (ABIt: apply_buffer_item bi ts.(tso_mem) = Some tm')
    (Bt:   ts.(tso_buffers) t = bi :: tbr)
    (TREL: tso_related_fw ts ss),
      exists ss',
      tso_related_fw (mktsostate (tupdate t tbr ts.(tso_buffers))
                                      tm') 
                           ss'.
Proof.
  intros.
  inv TREL.
  assert (BRt:
    buffers_related (tso_buffers ts t) (tp t) (tso_buffers ss t) (sp t)).
    inv REL. by eauto.
  remember (tso_buffers ts t) as tb.
  remember (tp t) as tpt.
  remember (tso_buffers ss t) as sb.
  remember (sp t) as spt.
  revert sp ss Heqspt Heqsb USs REL.

  (buffers_related_cases (induction BRt) Case); intros; inv Bt.
 
  Case "buffers_related_irrelevant".
    assert (A: exists sm', apply_buffer_item bi ss.(tso_mem) = Some sm' /\ 
                           unbuffer_safe (mktsostate (tupdate t sb ss.(tso_buffers)) sm')).
      simpl in USs.
      by destruct (unbuffer_unbuffer_safe USs (sym_eq Heqsb)) 
        as [? (? & ?)]; vauto.
    destruct A as [sm' (ABIs & USs')].
    exists (mktsostate (tupdate t sb ss.(tso_buffers)) sm').
    econstructor. done. 
    eby eapply irrelevant_preserves_tso_related_witt.

  Case "buffers_related_write".
    assert (A: exists sm', 
      apply_buffer_item (BufferedWrite p c v') ss.(tso_mem) = Some sm' /\ 
      unbuffer_safe (mktsostate (tupdate t sb ss.(tso_buffers)) sm')).
      simpl in USs.
      by destruct (unbuffer_unbuffer_safe USs (sym_eq Heqsb)) 
        as [? (? & ?)]; vauto.
    destruct A as [sm' (ABIs & USs')].
    exists (mktsostate (tupdate t sb ss.(tso_buffers)) sm').
    econstructor. done. 
    eby eapply write_preserves_tso_related_witt.

  Case "buffers_related_local_write".
    exists ss.
    econstructor. done.
    eby eapply local_write_preserves_tso_related_witt.

  Case "buffers_related_salloc".
    assert (A: exists sm', 
      apply_buffer_item (BufferedAlloc p n MObjStack) ss.(tso_mem) = Some sm' /\ 
      unbuffer_safe (mktsostate (tupdate t sb ss.(tso_buffers)) sm')).
      simpl in USs.
      by destruct (unbuffer_unbuffer_safe USs (sym_eq Heqsb)) 
        as [? (? & ?)]; vauto.
    destruct A as [sm' (ABIs & USs')].
    exploit IHBRt; try done.
    - instantiate (1 := tupdate t ((p, n)::(sp0 t)) sp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t sb ss.(tso_buffers)) sm').
      by simpl; rewrite tupdate_s.
    - done.
    - eby eapply salloc_preserves_tso_related_witt.

  Case "buffers_related_sfree".
    assert (A: exists sm', 
      apply_buffer_item (BufferedFree p MObjStack) ss.(tso_mem) = Some sm' /\ 
      unbuffer_safe (mktsostate (tupdate t sb ss.(tso_buffers)) sm')).
      simpl in USs.
      by destruct (unbuffer_unbuffer_safe USs (sym_eq Heqsb)) 
        as [? (? & ?)]; vauto.
    destruct A as [sm' (ABIs & USs')].
    exploit IHBRt; auto.
    - instantiate (1 := tupdate t sp sp0).
      by rewrite tupdate_s.     
    - instantiate (1 := mktsostate (tupdate t sb ss.(tso_buffers)) sm').
      by simpl; rewrite tupdate_s.
    - done.
    - eby eapply sfree_preserves_tso_related_witt; try edone; symmetry.

  Case "buffers_related_talloc".
    exists ss.
    econstructor. done.
    eby eapply talloc_preserves_tso_related_witt.

  Case "buffers_related_tfree".
    exists ss.
    econstructor. done.
    eby eapply tfree_preserves_tso_related_witt; try edone; symmetry.
Qed.

Lemma unbuffer_safety_rev_write_free_gen:
  forall t ts ts' ss fw
    (FS:   tso_fin_sup ts)
    (TREL: tso_related_fw ts ss)
    (US:   unbuffer_safe ts')
    (DAL:  writes_or_frees fw)
    (SBT:  ts.(tso_buffers) t = ts'.(tso_buffers) t ++ fw)
    (SBO:  forall t', t' <> t -> ts.(tso_buffers) t' = ts'.(tso_buffers) t')
    (MR:   mrestr ts.(tso_mem) = mrestr ts'.(tso_mem))
    (RAS:  forall r k (RA: range_allocated r k ts.(tso_mem)),
                 range_allocated r k ts'.(tso_mem)),
    unbuffer_safe ts.
Proof.
  intros until 1. destruct FS as [l [NDUP DOM]].
  
  remember (buffers_measure l ts.(tso_buffers)) as bsize.
  revert ss ts ts' fw DOM NDUP Heqbsize.
  induction bsize as [|bsize IH]; intros.

  (* Base case *)
  by constructor; [intros t' bi b Bs | intros t' bi b m' Bs];
    destruct (In_dec peq t' l) as [IN | NIN]; 
      try (by rewrite (buffer_measure_zero _ _ _ Heqbsize IN) in Bs);
        rewrite DOM in Bs.

  (* Step case *)
  constructor.
  intros t' bi b Bs.
  destruct US as [ts' MABI US].
  destruct (apply_buffer_item bi (tso_mem ts)) as [m|] _eqn : FAIL. eby eexists.
  byContradiction.
  destruct bi as [pi ci vi | pi ni ki | pi ki].
      (* Write succeeds because the simulation relation says so *)
      by apply (tso_pc_related_unsafe_store_sim _ _ _ _ _ TREL Bs).
    (* Alloc succeeds because we have a more-allocated memory where 
       the alloc succeeds *)
    assert (Bs' : exists br, tso_buffers ts' t' = BufferedAlloc pi ni ki :: br).
      destruct (peq t' t) as [-> | N].
        rewrite Bs in SBT. 
        destruct (tso_buffers ts' t) as [| bi' br'].
           simpl in SBT. rewrite <- SBT in DAL.
             by specialize (DAL _ (in_eq _ _)).
          rewrite <- app_comm_cons in SBT. inv SBT.
        eby eexists.
      rewrite (SBO _ N) in Bs.
      eby eexists.
    destruct Bs' as [br Bs'].
    destruct (MABI _ _ _ Bs') as [m' ABI].
    unfold apply_buffer_item in ABI, FAIL. 
    pose proof (alloc_cond_spec (pi, ni) ki (tso_mem ts')) as AS'.
    pose proof (alloc_cond_spec (pi, ni) ki (tso_mem ts)) as AS.
    rewrite FAIL in AS. rewrite ABI in AS'.
    destruct AS' as (RA' & VAR' & RP' & OVNA').
    inv TREL. inv REL.
    simpl in RP'. unfold restricted_pointer in RP'. rewrite <- MR in RP'.
    destruct AS as [NVAR | [NRP | [r' [k' [OVER RA]]]]]; [done | done | ].
    apply RAS in RA.
    eby eapply OVNA'.
  (* Free succeeds because of the simulation *)
  by apply (tso_pc_related_unsafe_store_sim _ _ _ _ _ TREL Bs).

  (* Proof of preservation of the induction hypothesis *)
  intros t' bi tbr tm' BD ABIt.
  destruct (tso_related_fw_sim ABIt BD TREL) as [ss' TREL'].
  destruct (In_dec peq t' l) as [INR | NINR].
    2: by rewrite DOM in BD.
  pose proof (preserve_dom_unbuffer _ _ _ _ _ BD DOM) as NDOM.
  destruct (measure_down_unbuffer _ _ _ _ _ NDUP BD INR) 
    as [s [BS SBS]].
  rewrite <- Heqbsize in SBS. inv SBS.
  destruct (peq t' t) as [-> | N].
    rewrite SBT in BD. 
    destruct (tso_buffers ts' t) as [|btsh' btst'] _eqn : Ebts'.
      (* Unbuffering the newly buffered allocs *)
      simpl in BD. subst. pose proof (DAL _ (in_eq _ _)) as DALh. 
      assert (NDAL : writes_or_frees tbr).
        intros bi' IN'. by eapply DAL, in_cons.
      eapply (IH _ _ ts' tbr); try edone. 
      simpl. rewrite tupdate_s. by rewrite Ebts'.
      intros tx Nx. simpl. by rewrite tupdate_o; [rewrite SBO|].
      simpl. by rewrite (mem_consistent_with_restr_apply_item ABIt).
      simpl. intros r' k' RA'. apply RAS.
      unfold apply_buffer_item in ABIt.
      destruct bi; try done.
        by apply (store_preserves_allocated_ranges ABIt _ _).
      by apply (free_preserves_allocated_back ABIt).
    (* Unbuffering old stuff *)
    rewrite <- app_comm_cons in BD. inv BD.
    destruct (unbuffer_unbuffer_safe US Ebts') as [stm' [ABIts' US']].
    eapply (IH _ _ (mktsostate 
      (tupdate t btst' ts'.(tso_buffers)) stm') fw); try edone.
    simpl. by rewrite ! tupdate_s.
    intros t' Nt'. simpl. by rewrite ! tupdate_o; [apply SBO | | ].
    simpl. by rewrite (mem_consistent_with_restr_apply_item ABIt),
                      (mem_consistent_with_restr_apply_item ABIts').
    eby eapply sim_apply_item_preserves_alloc_impl.
  (* Unbuffering another thread *)
  pose proof BD as BD'. rewrite SBO in BD'; [|done].
  destruct (unbuffer_unbuffer_safe US BD') as [stm' [ABIts' US']].
  eapply (IH _ _ (mktsostate (tupdate t' tbr ts'.(tso_buffers)) stm') fw); try edone.
  simpl. rewrite ! tupdate_o; try done; intro E; by rewrite E in N.
  intros t'' N''. simpl. 
    unfold tupdate. by destruct (peq t'' t'); try rewrite SBO. 
  simpl. by rewrite (mem_consistent_with_restr_apply_item ABIt),
                    (mem_consistent_with_restr_apply_item ABIts').
  eby eapply sim_apply_item_preserves_alloc_impl.
Qed.
