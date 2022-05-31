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

(** Equivalence relations on memories. *)

Require Import Coqlib.
Require Import Specif.
Require Import Maps.
Require Import Ast.
Require Import Pointers.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Libtactics.
Require Import Permutation.
(* Require Import TSOmachine. *)

(*============================================================================*)
(** * Quotienting on range lists *)

Lemma range_lists_disjoint_ext:
  forall {l1 l1' l2 l2'}
    (EQ1: list_equiv l1 l1')
    (EQ2: list_equiv l2 l2')
    (DISJ: range_lists_disjoint l1 l2),
    range_lists_disjoint l1' l2'.
Proof.
  unfold range_lists_disjoint, range_not_in; intros.
  by apply DISJ; [apply (proj2 (EQ1 _)) | apply (proj2 (EQ2 _))].
Qed.

(*============================================================================*)
(** * Load equality on memories *)

Lemma load_eq_preserved_by_store:
  forall {c m mx p c' p' v' m' mx'}
    (Leq: load_ptr c m p = load_ptr c mx p)
    (ST: store_ptr c' m  p' v' = Some m')
    (STx: store_ptr c' mx p' v' = Some mx'),
  load_ptr c m' p = load_ptr c mx' p.
Proof.
  intros.
  pose proof (load_chunk_allocated_spec c m p) as LDAL.
  pose proof (load_chunk_allocated_spec c mx p) as LDALX.
  pose proof (load_chunk_allocated_spec c m' p) as LDAL'.
  pose proof (load_chunk_allocated_spec c mx' p) as LDALX'.
  destruct (load_ptr c m p) as [v|] _eqn : SMLD.
    (* Load SUCCESS *)
    destruct (range_eq_dec (range_of_chunk p' c') (range_of_chunk p c))
      as [RCeq | RCneq].
      (* Reading exactly the memory written by the unbuffered store *)
      injection RCeq. 
      intro SCeqm.
      assert (SCeq: size_chunk c' = size_chunk c).
      destruct c; destruct c'; simpl in *; compute in SCeqm; done.
      intro Peq; subst.
      by rewrite (load_store_similar ST SCeq), (load_store_similar STx SCeq).
    (* Reading from different memory; two cases: *)
    destruct (ranges_disjoint_dec (range_of_chunk p' c') 
                                         (range_of_chunk p c)) 
        as [RDISJ | ROVER].
      (* Ranges completely disjoint *)
      rewrite <- (load_store_other ST RDISJ), SMLD.
      by rewrite <- (load_store_other STx RDISJ).
      (* Ranges overlap *)
      apply (store_preserves_chunk_allocation ST _ _) in LDAL.
      rewrite (load_store_overlap ST ROVER RCneq LDAL).
      destruct (load_ptr c mx p) as [v''|] _eqn : SMLD'.
      apply (store_preserves_chunk_allocation STx p c) in LDALX.
      rewrite (load_store_overlap STx ROVER RCneq LDALX).
      done.
      by destruct (load_ptr c mx' p);
        [apply (store_preserves_chunk_allocation STx _ _) in LDALX'|].
    (* Load FAIL *)
    apply sym_eq in Leq. rewrite Leq in LDALX.
    destruct (load_ptr c m' p) as [cmv|] _eqn : E2;
      destruct (load_ptr c mx' p) as [cmv'|] _eqn : E3;
        try apply (store_preserves_chunk_allocation STx _ _) in LDALX';
          try apply (store_preserves_chunk_allocation ST _ _) in LDAL';
            try done.
Qed.

Lemma load_eq_preserved_by_alloc:
  forall {c m mx p r' k' m' mx'}
    (Leq: load_ptr c m p = load_ptr c mx p)
    (AP: alloc_ptr r' k' m = Some m')
    (APx: alloc_ptr r' k' mx = Some mx'),
  load_ptr c m' p = load_ptr c mx' p.
Proof.
  intros; destruct r' as [p' n'].
  pose proof (load_chunk_allocated_spec c m p) as LDAL.
  pose proof (load_chunk_allocated_spec c mx p) as LDALX.
  pose proof (load_chunk_allocated_spec c m' p) as LDAL'.
  pose proof (load_chunk_allocated_spec c mx' p) as LDALX'.
  destruct (pointer_chunk_aligned_dec p c) as [CA | CNA].
    2: destruct (load_ptr c m' p); destruct (load_ptr c mx' p);
      try done; destruct LDAL'; destruct LDALX'; done.
  destruct (range_inside_dec (range_of_chunk p c) (p', n')) as [RI | RNI].
    (* loads inside the newly allocated region *)
    rewrite (load_alloc_inside AP); try done;
      rewrite (load_alloc_inside APx); done.
  destruct (ranges_disjoint_dec (range_of_chunk p c) 
                                       (p', n')) as [DISJ | OVER].
    (* loads outside *)
    rewrite (load_alloc_other AP); try done;
      rewrite (load_alloc_other APx); done.
  (* loads overlap *)
  destruct (alloc_someD AP) as [APA _].
  destruct (alloc_someD APx) as [APA' _].
  destruct (load_ptr c m' p).
    destruct LDAL' as [[r [k [RI RA]]] _].
    destruct (ranges_are_disjoint RA APA) as [[-> ->] | DISJ]; try done. 
    eby elim OVER; eapply disjoint_inside_disjoint.
  destruct (load_ptr c mx' p); try done.
  destruct LDALX' as [[r [k [RI RA]]] _].
  destruct (ranges_are_disjoint RA APA') as [[-> ->] | DISJ]; try done. 
  eby elim OVER; eapply disjoint_inside_disjoint.
Qed.

Lemma load_eq_preserved_by_free_same_size:
  forall {c m mx p p' n' k' m' mx'}
    (Leq: load_ptr c m p = load_ptr c mx p)
    (RA: range_allocated (p', n') k' m)
    (FP: free_ptr p' k' m = Some m')
    (RAx: range_allocated (p', n') k' mx)
    (FPx: free_ptr p' k' mx = Some mx'),
  load_ptr c m' p = load_ptr c mx' p.
Proof.
  intros.
  destruct (ranges_disjoint_dec (range_of_chunk p c) 
                                       (p', n')) as [DISJ | OVER].
    by rewrite (load_free_other FP RA DISJ),
               (load_free_other FPx RAx DISJ).
  by rewrite (load_free_overlap FP RA OVER), 
             (load_free_overlap FPx RAx OVER).
Qed.

Lemma load_eq_preserved_by_free_diff_block:
  forall {c m mx p p' k' m' mx'}
    (Leq: load_ptr c m p = load_ptr c mx p)
    (DB: MPtr.block p <> MPtr.block p')
    (FP: free_ptr p' k' m = Some m')
    (FPx: free_ptr p' k' mx = Some mx'),
  load_ptr c m' p = load_ptr c mx' p.
Proof.
  intros.
  destruct (free_someD FP) as [n RA].
  destruct (free_someD FPx) as [nx RAx].
  rewrite (load_free_other FP RA); 
    [|by destruct p; destruct p'; simpl in *; left].
  by rewrite (load_free_other FPx RAx);
    [|by destruct p; destruct p'; simpl in *; left].
Qed.

(*============================================================================*)
(** * Equality on allocated ranges *)

(** The allocation ranges are equal *)
Definition arange_eq (Cond: _ -> bool) m1 m2 :=
    (forall r k (COND: Cond k), range_allocated r k m1 <-> range_allocated r k m2)
 /\ (mrestr m1 = mrestr m2).

Lemma arange_eq_sub:
  forall {m1 m2} C D,
    arange_eq C m1 m2 ->
    (forall k, D k = true -> C k) ->
    arange_eq D m1 m2.
Proof. by destruct 1; split; auto. Qed.

Lemma arange_eq_refl:
 forall C m, arange_eq C m m. 
Proof. done. Qed.

Lemma arange_eq_sym:
  forall {C m1 m2}, arange_eq C m1 m2 -> arange_eq C m2 m1.
Proof. by destruct 1 as [A R]; repeat split; try done; by eapply A. Qed.  

Lemma arange_eq_trans:
  forall C x y z,
    arange_eq C x y ->
    arange_eq C y z ->
    arange_eq C x z.
Proof.
  intros C x y z (X & ?) (Y & ?); split; [intros r k|congruence].
  specialize (X r k); specialize (Y r k); tauto.
Qed.

Lemma arange_eq_store:
  forall {m m' chunk p v} C,
    store_ptr chunk m p v = Some m' ->
    arange_eq C m' m.
Proof.
  intros m m' chunk p v STO.
  split; [split|].
      eby apply <- @store_preserves_allocated_ranges.
    eby apply -> @store_preserves_allocated_ranges. 
  eby eapply restr_of_store.
Qed.

Lemma range_in_allocated_arange:
  forall {m1 m2 r}
    (EQ: arange_eq (fun _ => true) m1 m2)
    (RA: range_in_allocated r m1),
    range_in_allocated r m2.
Proof.
  intros; destruct RA as (? & ? & ? & ?).
  eby do 2 eexists; split; [|eapply (proj1 EQ)].
Qed.

Lemma chunk_allocated_and_aligned_arange:
  forall {m1 m2 chunk p}
    (EQ: arange_eq (fun _ => true) m1 m2)
    (CA: chunk_allocated_and_aligned p chunk m1),
    chunk_allocated_and_aligned p chunk m2.
Proof.
  intros; destruct CA as [? ?]; split; try done.
  eby eapply range_in_allocated_arange.
Qed.

Lemma range_list_of_mem_arange:
  forall {m1 m2}
    (EQ: arange_eq (fun _ => true) m1 m2),
  list_equiv (range_list_of_mem m1) (range_list_of_mem m2).
Proof.
  intros; intro x.
  eapply iff_trans; [apply range_list_of_mem_alloc|].
  eapply iff_trans; [|apply iff_sym; apply range_list_of_mem_alloc].
  split; intros [k RA]; exists k; pose proof (proj1 EQ x k (refl_equal _)); tauto.
Qed.


Lemma load_ptr_none_arange:
  forall {m1 m2 chunk p}
    (LD: load_ptr chunk m1 p = None)
    (EQ: arange_eq (fun _ => true) m1 m2),
    load_ptr chunk m2 p = None.
Proof.
  intros.
  assert (X1 := load_chunk_allocated_spec chunk m1 p).
  assert (X2 := load_chunk_allocated_spec chunk m2 p).
  do 2 destruct load_ptr; try done. 
  eby elim X1; eapply chunk_allocated_and_aligned_arange; try apply @arange_eq_sym.
Qed.

Lemma load_ptr_some_arange:
  forall m1 m2 chunk p v1
    (H1: load_ptr chunk m1 p = Some v1)
    (EQ: arange_eq (fun _ => true) m1 m2),
  exists v2, load_ptr chunk m2 p = Some v2.
Proof.
  intros.
  assert (X1 := load_chunk_allocated_spec chunk m1 p).
  assert (X2 := load_chunk_allocated_spec chunk m2 p).
  do 2 destruct load_ptr; vauto. 
  eby elim X2; eapply chunk_allocated_and_aligned_arange.
Qed.

Lemma store_ptr_none_arange:
  forall {m1 m2 chunk p v} v'
    (STO: store_ptr chunk m1 p v = None)
    (EQ: arange_eq (fun _ => true) m1 m2),
    store_ptr chunk m2 p v' = None.
Proof.
  intros.
  assert (X1 := store_chunk_allocated_spec chunk m1 p v).
  assert (X2 := store_chunk_allocated_spec chunk m2 p v').
  do 2 destruct store_ptr; try done. 
  eby elim X1; eapply chunk_allocated_and_aligned_arange; try apply @arange_eq_sym.
Qed.

Lemma store_ptr_some_arange1:
  forall C m1 m2 chunk p v v' m1' m2'
    (STO1: store_ptr chunk m1 p v = Some m1')
    (STO2: store_ptr chunk m2 p v' = Some m2')
    (REQ: arange_eq C m1 m2),
    arange_eq C m1' m2'.
Proof. 
  intros; destruct REQ as [RA ?].
  split.
    intros.
    pose proof (store_preserves_allocated_ranges STO1 r k).
    pose proof (store_preserves_allocated_ranges STO2 r k).
    specialize (RA r k).
    tauto.
  by rewrite (restr_of_store STO1), (restr_of_store STO2).
Qed.

Lemma store_ptr_some_arange:
  forall m1 m2 chunk p v v' m1'
    (H1: store_ptr chunk m1 p v = Some m1')
    (EQ: arange_eq (fun _ => true) m1 m2),
  exists m2', store_ptr chunk m2 p v' = Some m2' /\ arange_eq (fun _ => true) m1' m2'.
Proof.
  intros; destruct (store_ptr chunk m2 p v') as [m2'|] _eqn: H2;
    [|by rewrite (store_ptr_none_arange _ H2 (arange_eq_sym EQ)) in H1].
  exists m2'; split; try done.
  eby eapply store_ptr_some_arange1.
Qed.

Lemma alloc_ptr_none_arange:
  forall m1 m2 r k,
    alloc_ptr r k m1 = None ->
    arange_eq (fun _ => true) m1 m2 ->
    alloc_ptr r k m2 = None.
Proof.
  intros m1 m2 r k H EQ.
  pose proof (alloc_cond_spec r k m1) as A1; destruct (alloc_ptr r k m1); try done.
  pose proof (alloc_cond_spec r k m2) as A2; destruct (alloc_ptr r k m2); try done.
  destruct A2 as [RA [? [? AL]]].
  destruct A1 as [|[|[[? ?] [? [? RA']]]]]; try done.
    destruct (fst r) as [b ofs]; simpl in *.
    by rewrite (proj2 EQ) in *.
  exploit AL; try edone.
  eby eapply (proj1 ((proj1 EQ) _ _ (refl_equal _))).
Qed.

Lemma alloc_ptr_some_arange1:
  forall C m1 m2 r k m1' m2',
    alloc_ptr r k m1 = Some m1' ->
    alloc_ptr r k m2 = Some m2' ->
    arange_eq C m1 m2 ->
    arange_eq C m1' m2'.
Proof.
  intros C m1 m2 r k m1' m2' H1 H2 [RA ?]; split.
    intros r0 k0.
    pose proof (RA r0 k0) as EQ'.
    pose proof (alloc_preserves_allocated_iff H1 r0 k0) as A1.
    pose proof (alloc_preserves_allocated_iff H2 r0 k0) as A2.
    tauto.
  by rewrite (restr_of_alloc H1), (restr_of_alloc H2).
Qed.

Lemma alloc_ptr_some_arange:
  forall m1 m2 r k m1',
    alloc_ptr r k m1 = Some m1' ->
    arange_eq (fun _ => true) m1 m2 ->
    (exists m2', alloc_ptr r k m2 = Some m2' /\ arange_eq (fun _ => true) m1' m2').
Proof.
  intros m1 m2 r k m1' H1 EQ.
  destruct (alloc_ptr r k m2) as [m2'|] _eqn: H2;
    [|by rewrite (alloc_ptr_none_arange _ _ _ _ H2 (arange_eq_sym EQ)) in H1].
  exists m2'; split; try done.
  eby eapply alloc_ptr_some_arange1.
Qed.

Lemma free_ptr_none_arange:
  forall C m1 m2 p k,
    free_ptr p k m1 = None ->
    arange_eq C m1 m2 ->
    C k ->
    free_ptr p k m2 = None.
Proof.
  intros C m1 m2 p k H [EQ ?] CC.
  pose proof (free_noneD H) as A1.
  pose proof (free_cond_spec p k m2) as A2; destruct (free_ptr p k m2); try done.
  destruct A2 as [n ?].
  by elim (A1 n); apply (proj2 (EQ _ _ CC)).
Qed.

Lemma free_ptr_some_arange1:
  forall C m1 m2 p k m1' m2',
    free_ptr p k m1 = Some m1' ->
    free_ptr p k m2 = Some m2' ->
    arange_eq C m1 m2 ->
    arange_eq C m1' m2'.
Proof.
  intros C m1 m2 p k m1' m2' H1 H2 [RA ?].
  split.
    split; intro H3.
      pose proof (free_preserves_allocated_back H1 _ _ H3) as X.
      apply (proj1 (RA r k0 COND)) in X.
      destruct (free_preserves_allocated H2 _ _ X) as [|[]]; clarify.
      eby destruct r; eapply free_not_allocated in H1; elim H1.
    pose proof (free_preserves_allocated_back H2 _ _ H3) as X.
    apply (proj2 (RA r k0 COND)) in X.
    destruct (free_preserves_allocated H1 _ _ X) as [|[]]; clarify.
    eby destruct r; eapply free_not_allocated in H2; elim H2.
  by rewrite (restr_of_free H1), (restr_of_free H2).
Qed.

Lemma free_ptr_some_arange:
  forall C m1 m2 p k m1',
    free_ptr p k m1 = Some m1' ->
    arange_eq C m1 m2 ->
    C k ->
    (exists m2', free_ptr p k m2 = Some m2' /\ arange_eq C m1' m2').
Proof.
  intros C m1 m2 p k m1' H1 EQ CC.
  destruct (free_ptr p k m2) as [m2'|] _eqn: H2;
    [|by rewrite (free_ptr_none_arange _ _ _ _ _ H2 (arange_eq_sym EQ)) in H1].
  exists m2'; split; try done.
  eby eapply free_ptr_some_arange1.
Qed.

Lemma load_eq_preserved_by_free_arange:
  forall {c m mx p p' k' m' mx'}
    (Leq: load_ptr c m p = load_ptr c mx p)
    (FP: free_ptr p' k' m = Some m')
    (FPx: free_ptr p' k' mx = Some mx')
    (Req: arange_eq (fun _ => true) m mx),
  load_ptr c m' p = load_ptr c mx' p.
Proof.
  intros.
  pose proof (free_someD FP) as [n RA].
  pose proof (proj1 (proj1 Req _ _ (refl_equal _)) RA).
  eby eapply load_eq_preserved_by_free_same_size.  
Qed.

(*============================================================================*)
(** * Less definedness on memories *)

Definition opt_lessdef vo vo' := 
  match vo, vo' with
    | Some v, Some v' => Val.lessdef v v'
    | None, _ => True
    | _, _ => False
  end.

Definition mem_lessdef (m m': mem) :=
  forall p c, opt_lessdef (load_ptr c m p) (load_ptr c m' p).

Definition mem_lessdef_in_range (m m': mem) (r: arange) :=
  forall p c,
    range_inside (range_of_chunk p c) r -> 
    opt_lessdef (load_ptr c m p) (load_ptr c m' p).

Lemma opt_lessdef_refl:
  forall v, opt_lessdef v v.
Proof. by intros [[]|]; vauto. Qed.

Hint Resolve opt_lessdef_refl.

Lemma mem_lessdef_refl:
  forall m, mem_lessdef m m.
Proof. by intros m p c; destruct load_ptr. Qed.

Hint Resolve mem_lessdef_refl.

Lemma opt_lessdef_sim_write:
  forall tm sm tm' sm' p c v v' p' c'
    (LDrel: opt_lessdef (load_ptr c' sm p') (load_ptr c' tm p'))
    (tSTO: store_ptr c tm p v = Some tm')
    (sSTO: store_ptr c sm p v' = Some sm')
    (vLDEF: Val.lessdef v' v),
    opt_lessdef (load_ptr c' sm' p') (load_ptr c' tm' p').
Proof.
  intros.
  pose proof (load_chunk_allocated_spec c' tm p') as Ct.
  pose proof (load_chunk_allocated_spec c' tm' p') as Ct'.
  pose proof (load_chunk_allocated_spec c' sm p') as Cs.
  pose proof (load_chunk_allocated_spec c' sm' p') as Cs'.

     destruct (load_ptr c' tm p') as [v1|] _eqn: tLD;
     destruct (load_ptr c' sm p') as [v2|] _eqn: sLD; clarify;
     destruct (load_ptr c' tm' p') as [] _eqn: tLD';
     destruct (load_ptr c' sm' p') as [] _eqn: sLD'; clarify;
     try apply (store_preserves_chunk_allocation tSTO _ _) in Ct;
     try apply (store_preserves_chunk_allocation tSTO _ _) in Ct';
     try apply (store_preserves_chunk_allocation sSTO _ _) in Cs; 
     try apply (store_preserves_chunk_allocation sSTO _ _) in Cs'; simpl in *; clarify.

    destruct (range_eq_dec (range_of_chunk p c) (range_of_chunk p' c'))
      as [RCeq | RCneq].
      (* Reading exactly the memory written by the unbuffered store *)
      injection RCeq. 
      intro SCeqm.
      assert (SCeq: size_chunk c = size_chunk c').
      destruct c; destruct c'; simpl in *; compute in SCeqm; done.
      intro Peq; subst.
      rewrite (load_store_similar tSTO SCeq), (load_store_similar sSTO SCeq) in *; vauto.
      by destruct compatible_chunks; auto using Val.load_result_lessdef. 

    (* Reading from different memory; two cases: *)
    destruct (ranges_disjoint_dec (range_of_chunk p c) 
                                         (range_of_chunk p' c')) 
        as [RDISJ | ROVER].
      (* Ranges completely disjoint *)
     by rewrite <- (load_store_other tSTO RDISJ), <- (load_store_other sSTO RDISJ) in *; clarify'. 

      (* Ranges overlap *)
     by  rewrite (load_store_overlap tSTO ROVER RCneq Ct),
              (load_store_overlap sSTO ROVER RCneq Cs) in *; vauto.
Qed.

Lemma opt_lessdef_sim_alloc:
  forall tm sm tm' sm' p n k p' c'
    (LREL: opt_lessdef (load_ptr c' sm p') (load_ptr c' tm p'))
    (ACT: alloc_ptr (p, n) k tm = Some tm')
    (ACS: alloc_ptr (p, n) k sm = Some sm'),
    opt_lessdef (load_ptr c' sm' p') (load_ptr c' tm' p').
Proof.
  intros.
  destruct (ranges_disjoint_dec (range_of_chunk p' c') (p, n))
    as [DISJ | OVER].
    by rewrite (load_alloc_other ACT), (load_alloc_other ACS).
  destruct (range_inside_dec (range_of_chunk p' c') (p, n))
    as [RI | NRI].
    destruct (pointer_chunk_aligned_dec p' c') as [ALG | NALG].
      by rewrite (load_alloc_inside ACT), (load_alloc_inside ACS); vauto.
    assert (LDT := load_chunk_allocated_spec c' tm' p'). 
    assert (LDS := load_chunk_allocated_spec c' sm' p'). 
    destruct (load_ptr c' tm' p'); [by case NALG; destruct LDT|].
    by destruct (load_ptr c' sm' p'); [by case NALG; destruct LDS|].
  by rewrite (load_alloc_overlap ACT), (load_alloc_overlap ACS).
Qed.

Lemma opt_lessdef_sim_free_same_size:
  forall tm sm tm' sm' p k n p' c'
    (LREL: opt_lessdef (load_ptr c' sm p') (load_ptr c' tm p'))
    (Ft: free_ptr p k tm = Some tm')
    (Fs: free_ptr p k sm = Some sm')
    (RAt: range_allocated (p, n) k tm)
    (RAs: range_allocated (p, n) k sm),
    opt_lessdef (load_ptr c' sm' p') (load_ptr c' tm' p').
Proof.
  intros.
  destruct (ranges_disjoint_dec (range_of_chunk p' c') (p, n))
    as [DISJ | OVER].
    by rewrite (load_free_other Ft RAt DISJ);
       rewrite (load_free_other Fs RAs DISJ).
  by rewrite (load_free_overlap Ft RAt OVER);
     rewrite (load_free_overlap Fs RAs OVER).
Qed.

Lemma mem_lessdef_sim_write:
  forall tm sm tm' sm' c p v v' 
    (LREL: mem_lessdef sm tm)
    (tSTO: store_ptr c tm p v = Some tm')
    (sSTO: store_ptr c sm p v' = Some sm')
    (vLDEF: Val.lessdef v' v),
    mem_lessdef sm' tm'.
Proof.
  intros; intros p' c'; specialize (LREL p' c').
  eby eapply opt_lessdef_sim_write.
Qed.

Lemma mem_lessdef_sim_alloc:
  forall tm sm tm' sm' p n k
    (LREL: mem_lessdef sm tm)
    (ACT: alloc_ptr (p, n) k tm = Some tm')
    (ACS: alloc_ptr (p, n) k sm = Some sm'),
    mem_lessdef sm' tm'.
Proof.
  intros; intros p' c'; specialize (LREL p' c').
  eby eapply opt_lessdef_sim_alloc.
Qed.

Lemma mem_lessdef_sim_free_same_size:
  forall tm sm tm' sm' p n k
    (LREL: mem_lessdef sm tm)
    (Ft: free_ptr p k tm = Some tm')
    (Fs: free_ptr p k sm = Some sm')
    (RAt: range_allocated (p, n) k tm)
    (RAs: range_allocated (p, n) k sm),
    mem_lessdef sm' tm'.
Proof.
  intros; intros p' c'; specialize (LREL p' c').
  eby eapply opt_lessdef_sim_free_same_size.
Qed.

Lemma mem_lessdef_alloc_src:
  forall tm sm sm' p n k
    (LREL: mem_lessdef sm tm)
    (RA: range_in_allocated (p, n) tm)
    (ACS: alloc_ptr (p, n) k sm = Some sm'),
    mem_lessdef sm' tm.
Proof.
  intros; intros p' c'; specialize (LREL p' c').
  destruct RA as (r' & k' & IN & RA).
  destruct (ranges_disjoint_dec (range_of_chunk p' c') (p, n))
    as [DISJ | OVER].
    by rewrite (load_alloc_other ACS).
  destruct (range_inside_dec (range_of_chunk p' c') (p, n))
    as [RI | NRI].
    destruct (pointer_chunk_aligned_dec p' c') as [ALG | NALG].
      rewrite (load_alloc_inside ACS); try done.
      assert (CA:= load_chunk_allocated_spec c' tm p').
      destruct (load_ptr c' tm p'); vauto.
      case CA; split; try done; exists r'; exists k'; split; try done. 
      eby eapply range_inside_trans.
    assert (LDS := load_chunk_allocated_spec c' sm' p'). 
    by destruct (load_ptr c' sm' p'); [by case NALG; destruct LDS|destruct load_ptr].
  by rewrite (load_alloc_overlap ACS); destruct load_ptr.
Qed.

Lemma mem_lessdef_free_src:
  forall tm sm sm' p k
    (LREL: mem_lessdef sm tm)
    (F: free_ptr p k sm = Some sm'),
    mem_lessdef sm' tm.
Proof.
  intros; intros p' c'; specialize (LREL p' c').
  pose proof (free_someD F) as [n RA].
  destruct (ranges_disjoint_dec (range_of_chunk p' c') (p, n))
    as [DISJ | OVER].
    eby erewrite (load_free_other F).
  erewrite (load_free_overlap F); try eassumption.
  by destruct (load_ptr c' sm p').
Qed.

Lemma mem_lessdef_clear_src:
  forall tm sm r
    (LREL: mem_lessdef sm tm),
    mem_lessdef (clear_range r sm) tm.
Proof.
  intros; intros p' c'; specialize (LREL p' c').
  destruct (load_ptr c' (clear_range r sm) p') as [] _eqn: LD.
  destruct (load_clear_back LD) as (? & LD' & LDEF); rewrite LD' in *.
    destruct (load_ptr c' tm p'); simpl in *; clarify.
    by inv LREL; clarify; inv LDEF; clarify.
  by eapply load_clear_none in LD; rewrite LD in *.
Qed.

(*============================================================================*)
(** * Partial load equality *)

Definition mem_agrees_on (m m' : mem) (rs : list arange) : Prop :=
  forall r p c,
    In r rs ->
    range_inside (range_of_chunk p c) r ->
    load_ptr c m p = load_ptr c m' p.

Lemma mem_agrees_on_sym:
  forall {m m' rs} (H: mem_agrees_on m m' rs),
  mem_agrees_on m' m rs.
Proof.
  eby unfold mem_agrees_on; intros; symmetry; eapply H.
Qed.

Lemma mem_agrees_on_trans:
  forall {x y z rs}
    (X: mem_agrees_on x y rs)
    (Y: mem_agrees_on y z rs),
  mem_agrees_on x z rs.
Proof.
  intros; intros r p c IN RI; 
  specialize (X _ _ _ IN RI);
  specialize (Y _ _ _ IN RI); congruence.
Qed.

Lemma mem_agrees_on_app:
  forall {m m' s1 s2},
    mem_agrees_on m m' (s1 ++ s2) <->
    mem_agrees_on m m' s1 /\ mem_agrees_on m m' s2.
Proof.
  split; [by intros MA; split; intros r p c IN; apply MA; auto using in_or_app|].
  intros [MA1 MA2]; intros r p c IN. apply -> in_app in IN; destruct IN;
    [by apply MA1 | by apply MA2].
Qed.

Lemma mem_agrees_on_perm:
  forall {m m' l l'}
    (P: Permutation l l')
    (MA: mem_agrees_on m m' l),
    mem_agrees_on m m' l'.
Proof.
  intros; intros r p c IN; apply MA.
  eby eapply Permutation_in; try apply Permutation_sym.
Qed.

Lemma mem_agrees_on_list_equiv:
  forall {m m' l l'}
    (EQ: list_equiv l l')
    (MA: mem_agrees_on m m' l),
    mem_agrees_on m m' l'.
Proof.
  by intros; intros r p c IN; eapply MA, EQ.
Qed.

Lemma mem_agrees_on_preserved_by_store:
  forall {m mx l c p v m' mx'}
    (EQ: mem_agrees_on m mx l)
    (ST: store_ptr c m p v = Some m')
    (STx: store_ptr c mx p v = Some mx'),
  mem_agrees_on m' mx' l.
Proof.
  intros; intros r p' c' IN P; specialize (EQ r p' c' IN P).
  eby eapply load_eq_preserved_by_store.
Qed.

Lemma mem_agrees_on_preserved_by_alloc:
  forall {m mx l r k m' mx'}
    (EQ: mem_agrees_on m mx l)
    (A: alloc_ptr r k m = Some m')
    (Ax: alloc_ptr r k mx = Some mx'),
  mem_agrees_on m' mx' l.
Proof.
  intros; intros r' p' c' IN P; specialize (EQ r' p' c' IN P).
  eby eapply load_eq_preserved_by_alloc.
Qed.

Lemma mem_agrees_on_preserved_by_free_same_size:
  forall {m mx l p n k m' mx'}
    (EQ: mem_agrees_on m mx l)
    (RA: range_allocated (p, n) k m)
    (F: free_ptr p k m = Some m')
    (RAx: range_allocated (p, n) k mx)
    (Fx: free_ptr p k mx = Some mx'),
  mem_agrees_on m' mx' l.
Proof.
  intros; intros r' p' c' IN P; specialize (EQ r' p' c' IN P).
  eby eapply load_eq_preserved_by_free_same_size.
Qed.

Lemma mem_agrees_on_preserved_by_free_arange:
  forall {m mx l p k m' mx'}
    (EQ: mem_agrees_on m mx l)
    (REQ: arange_eq (fun _ => true) m mx)
    (F: free_ptr p k m = Some m')
    (Fx: free_ptr p k mx = Some mx'),
  mem_agrees_on m' mx' l.
Proof.
  intros; intros r' p' c' IN P; specialize (EQ r' p' c' IN P).
  eby eapply load_eq_preserved_by_free_arange.
Qed.

(*============================================================================*)
(** * Extensional equality on memories *)

Definition mem_eq m1 m2:=
   (forall chunk p, load_ptr chunk m1 p = load_ptr chunk m2 p)
/\ (forall r k, range_allocated r k m1 <-> range_allocated r k m2)
/\ (mrestr m1 = mrestr m2).

Lemma in_block1:
  forall lbnd hbnd l h k ba,
  alloclist_hbound lbnd (mkmobj l h k :: ba) = Some hbnd -> 0 < lbnd -> hbnd <= Int.modulus ->
  valid_access Mint8unsigned (l mod Int.modulus) (mkmobj l h k :: ba).
Proof.
  intros.
  constructor 1 with (k:=k); [|by apply Zone_divide].
  exists l; exists h.
  split; [by left|].
  exploit (@alloclist_hbound_impl_l_lt_h); [eassumption|by left|intro].  
  rewrite Zmod_small; simpl; omega.
Qed.

Lemma alloclist1:
  forall lbnd hbnd l h k a,
  alloclist_hbound lbnd (mkmobj l h k :: a) = Some hbnd ->
  lbnd <= l /\ l < h /\ h <= hbnd /\ (align_size (h - l) | l).
Proof.
  intros lbnd hbnd l h k a H.
  by destruct (alloclist_hbound_impl_l_lt_h H (in_eq _ _)) as (? & ? & ? & ?).
Qed.

Lemma range_allocated_al_cons:
  forall l h k l' h' k' ba',
  range_allocated_al l h k (mkmobj l' h' k' :: ba') ->
  l = l' /\ h = h' /\ k = k' \/ range_allocated_al l h k ba'.
Proof.
  unfold range_allocated_al.
  by inversion 1; clarify; [left|right].
Qed.


Lemma valid_access_bounded:
  forall c ofs al lbnd hbnd,
   alloclist_hbound lbnd al = Some hbnd ->
   valid_access c ofs al ->
   lbnd <= ofs < hbnd.
Proof.
  intros until 0; intros H [k [l [h [RA ?]]] AL].
  eapply @alloclist_hbound_impl_l_lt_h in H; try edone.
  destruct c; simpl in *; omega.
Qed.


Lemma Zabs_nat_of_nat: forall n, Zabs_nat (Z_of_nat n) = n.
Proof.
  by destruct n; simpl; auto using nat_of_P_o_P_of_succ_nat_eq_succ.
Qed.

Lemma contents_eq_ext:
  forall bc bc' ba, 
    block_valid (mkblock bc ba) ->
    block_valid (mkblock bc' ba) ->
    (forall c ofs,
      valid_access c ofs ba ->
      Val.load_result c (getN (pred_size_chunk c) (ofs mod Int.modulus) bc)
      = Val.load_result c (getN (pred_size_chunk c) (ofs mod Int.modulus) bc')) ->
  bc = bc'.
Proof.
  intros bc bc' ba (UU & OK & hbnd & B & M) (UU' & OK' & hbnd' & B' & M') LD.
  apply ZTree.ext; intros ofs.
  destruct (ZTree.get ofs bc) as [[]|] _eqn: G.

  Case "Datum".
    pose proof (proj1 (proj2 OK _ _ _ G)) as [c [SZ [VOK ACCOK]]].
    generalize (LD c ofs ACCOK).
    assert (ofsRNG: 0 <= ofs < Int.modulus) 
      by (pose proof (valid_access_bounded _ _ _ _ _ B ACCOK); omega).
    rewrite Zmod_small; try done.
    destruct ACCOK as [k ? ?]; simpl in *.

    unfold getN. 
    rewrite G, SZ, dec_eq_true, value_chunk_ok1; try done.
    destruct (ZTree.get ofs bc') as [[]|] _eqn: G'; try done; try destruct eq_nat_dec;
    try rewrite load_result_undef; intro X; clarify; try by revert VOK; clear; destruct c.

    pose proof (proj1 (proj2 OK' _ _ _ G')) as [c' [SZ' [VOK' ACCOK']]].
    rewrite value_chunk_ok1; try done.
    by revert VOK VOK' SZ'; clear; destruct c'; destruct c; destruct v0.

  Case "Cont".
    pose proof (proj1 OK _ _ G) as (l & v & Gm).
    pose proof (proj1 (proj2 OK _ _ _ Gm)) as [c [SZ [VOK ACCOK]]].
    generalize (LD _ _ ACCOK).
    assert (ofsRNG: 0 <= ofs - Z_of_nat n < Int.modulus) 
      by (pose proof (valid_access_bounded _ _ _ _ _ B ACCOK); omega).
    rewrite Zmod_small; try done.
    destruct ACCOK as [k ? ?]; simpl in *.
    unfold getN. 
    rewrite Gm, SZ, dec_eq_true, value_chunk_ok1; try done.
    destruct (ZTree.get (ofs - Z_of_nat n) bc') as [[]|] _eqn: G'; try done; try destruct eq_nat_dec;
    try rewrite load_result_undef; intro X; clarify; try by revert VOK; clear; destruct c.
    destruct n.
      by simpl in *; rewrite Zminus_0_r in *; rewrite G in Gm.

    pose proof (proj1 (proj2 OK' _ _ _ G')) as [c' [SZ' [VOK' ACCOK']]].
    exploit (check_cont_inside _ _ _ _ ofs (proj2 (proj2 OK' _ _ _ G'))); 
      unfold contents; rewrite inj_S.
    omega.
    intros ->; f_equal; f_equal.
    replace (ofs - (ofs - Zsucc (Z_of_nat n) + 1)) with (Z_of_nat n); [rewrite Zabs_nat_of_nat|]; omega.
    
  Case "None".
    destruct (ZTree.get ofs bc') as [[]|] _eqn: G'; try done.

    SCase "Datum".
      pose proof (proj1 (proj2 OK' _ _ _ G')) as [c [SZ [VOK ACCOK]]].
      generalize (LD c ofs ACCOK).
      assert (ofsRNG: 0 <= ofs < Int.modulus) 
        by (pose proof (valid_access_bounded _ _ _ _ _ B ACCOK); omega).
      rewrite Zmod_small; try done.
      destruct ACCOK as [k ? ?]; simpl in *.
      unfold getN. 
      rewrite G, G', SZ, dec_eq_true, load_result_undef, value_chunk_ok1; try done.
      by revert VOK; clear; destruct c; destruct v.

    SCase "Cont".
      pose proof (proj1 OK' _ _ G') as (l & v & Gm').
      pose proof (proj1 (proj2 OK' _ _ _ Gm')) as [c [SZ [VOK ACCOK]]].
      generalize (LD _ _ ACCOK).
      assert (ofsRNG: 0 <= ofs - Z_of_nat n < Int.modulus) 
        by (pose proof (valid_access_bounded _ _ _ _ _ B ACCOK); omega).
      rewrite Zmod_small; try done.
      destruct ACCOK as [k ? ?]; simpl in *.
      unfold getN. 
      rewrite Gm', SZ, dec_eq_true. 
      destruct (ZTree.get (ofs - Z_of_nat n) bc) as [[]|] _eqn: Gm; try done; try destruct eq_nat_dec;
      try rewrite load_result_undef; try (by revert VOK; destruct c; destruct v). 
      intro X; clarify. 
      destruct n.
        by simpl in *; rewrite Zminus_0_r in *; rewrite G in Gm.

      pose proof (proj1 (proj2 OK _ _ _ Gm)) as [c' [SZ' [VOK' ACCOK']]].
      exploit (check_cont_inside _ _ _ _ ofs (proj2 (proj2 OK _ _ _ Gm))); 
        unfold contents; rewrite inj_S.
      omega.
      by rewrite G. 
Qed.

Lemma range_allocated_implies_allocs_eq:
  forall m m' b bc bc',
  (forall (r : arange) (k : mobject_kind), range_allocated r k m  <-> range_allocated r k m') ->
  ZTree.get b (mcont m) = Some bc ->
  ZTree.get b (mcont m') = Some bc' ->
  allocs bc = allocs bc'.
Proof.
  intros [mc mr mv] [mc' mr' mv'] b [bc ba] [bc' ba'] RA EQ EQ'; simpl in *.
  pose proof (proj2 (proj2 (proj1 (proj2 (proj2 mv _ _ EQ))))) as [hbnd [B M]].
  pose proof (proj2 (proj2 (proj1 (proj2 (proj2 mv' _ _ EQ'))))) as [hbnd' [B' M']].
  unfold range_allocated in *; simpl in *. 

    assert (Y: forall ofs s k,
           range_allocated_al (Int.unsigned ofs)
              (Int.unsigned ofs + Int.unsigned s) k ba <->
            range_allocated_al (Int.unsigned ofs)
              (Int.unsigned ofs + Int.unsigned s) k ba').
      by intros; generalize (RA (Ptr b ofs, s) k); simpl; rewrite EQ, EQ'.
    clear RA; revert Y.
    simpl in *.
    clear EQ' EQ.
    revert B B' M'; cut (1 > 0); [|omega]; generalize 1 as lbnd; revert ba' hbnd'.

    induction ba as [|[l h k] ba IH]; destruct ba' as [|[l' h' k'] ba']; try done; intros hbnd' lbnd POS B B' M' Y.
    (*1*)  
      exploit (proj2 (Y (Int.repr l') (Int.repr (h' - l')) k')); try done.
      apply alloclist1 in B'.
      left; simpl; f_equal; rewrite ?Zmod_small; omega.
    (*2*)
      exploit (proj1 (Y (Int.repr l) (Int.repr (h - l)) k)); try done. 
      apply alloclist1 in B.
      left; simpl; f_equal; rewrite ?Zmod_small; omega.
    (* Main case *)
    assert (l = l' /\ h = h' /\ k = k') as [-> [-> ->]].
      pose proof (alloclist1 _ _ _ _ _ _ B).
      pose proof (alloclist1 _ _ _ _ _ _ B').
      exploit (proj1 (Y (Int.repr l) (Int.repr (h - l)) k)); simpl; 
        rewrite ?Zmod_small, Zplus_minus; try omega; [by left|].
      exploit (proj2 (Y (Int.repr l') (Int.repr (h' - l')) k')); simpl; 
        rewrite ?Zmod_small, Zplus_minus; try omega; [by left|].
      intros X' X.
      apply range_allocated_al_cons in X; destruct X as [X|X]; try done.
      apply range_allocated_al_cons in X'; destruct X' as [[-> [-> ->]]|X']; try done.
      simpl in B; destruct aligned_rng_dec; try done; destruct Z_le_dec; try done.
      simpl in B'; destruct aligned_rng_dec; try done; destruct Z_le_dec; try done.
      pose proof (alloclist_hbound_impl_l_lt_h B' X).
      pose proof (alloclist_hbound_impl_l_lt_h B X').
      omegaContradiction.
    f_equal.
    simpl in B, B'; destruct aligned_rng_dec; clarify; destruct Z_le_dec; clarify.
    apply IH with (hbnd' := hbnd') (lbnd := h'); try done. 
      omega.
    intros ofs s k.
    split; intro IN.
      destruct (proj1 (Y ofs s k) (or_intror _ IN)) as [|]; clarify.
      pose proof (alloclist_hbound_impl_l_lt_h B IN).
      omegaContradiction.
    destruct (proj2 (Y ofs s k) (or_intror _ IN)) as [|]; clarify.
    pose proof (alloclist_hbound_impl_l_lt_h B' IN).
    omegaContradiction.
Qed.

Lemma mem_eq_ext:
  forall m1 m2, mem_eq m1 m2 -> m1 = m2.
Proof.
  intros [mc mr mv] [mc' mr' mv'] [LD [RA MR]]; simpl in *; subst mr'.
  cut (mc = mc'); [by intro; subst mc'; rewrite (proof_irrelevance _ mv mv')|].
  apply ZTree.ext; intros b. 
  destruct (ZTree.get b mc) as [[bc ba]|] _eqn: EQ; 
  destruct (ZTree.get b mc') as [[bc' ba']|] _eqn: EQ'; try done.

  Case "SomeSome".
  generalize (range_allocated_implies_allocs_eq _ _ _ _ _ RA EQ EQ'); simpl; intros <-.
  f_equal; f_equal.
  pose proof (proj1 (proj2 (proj2 mv _ _ EQ))) as V.  
  pose proof (proj1 (proj2 (proj2 mv' _ _ EQ'))) as V'.
  apply (contents_eq_ext _ _ _ V V'); intros c ofs VA.
  generalize (LD c (Ptr b (Int.repr ofs))).
  simpl; unfold load; simpl; rewrite EQ, EQ'; simpl.
  rewrite Zmod_small, !in_block_true; try done.
    by intro; clarify.
  by destruct V as (? & ? & ? & B & ?);
     pose proof (valid_access_bounded _ _ _ _ _ B VA); omega.

  Case "SomeNone".
  case mv; intros _ V.
  pose proof (proj2 (V _ _ EQ)) as [[V1 [_ [hbnd [? ?]]]] M].
  destruct ba as [|[l h k] ?].
    assert (bc = ZTree.empty _); [|by elim M; subst].
    apply ZTree.ext; intro x; rewrite ZTree.gempty; apply V1; simpl.
    by intros k [? [? [RA' _]]]; inversion RA'.
  generalize (LD Mint8unsigned (Ptr b (Int.repr l))); unfold load_ptr, load; 
  simpl; rewrite EQ, EQ'; simpl.
  eby rewrite in_block_empty, in_block_true; [|eapply in_block1].

  Case "NoneSome".
  case mv'; intros _ V.
  pose proof (proj2 (V _ _ EQ')) as [[V1 [_ [hbnd [? ?]]]] M].
  destruct ba' as [|[l h k] ?].
    assert (bc' = ZTree.empty _); [|by elim M; subst].
    apply ZTree.ext; intro x; rewrite ZTree.gempty; apply V1; simpl.
    by intros k [? [? [RA' _]]]; inversion RA'.
  generalize (LD Mint8unsigned (Ptr b (Int.repr l))); unfold load_ptr, load; 
  simpl; rewrite EQ, EQ'; simpl.
  eby rewrite in_block_empty, in_block_true; [|eapply in_block1].
Qed.
