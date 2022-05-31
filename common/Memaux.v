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

(** This file contains additional properties about memories. *)

Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import Pointers.
Require Import Mem.
Require Import Ast.
Require Import Maps.
Require Import Libtactics.

Set Implicit Arguments.

(*----------------------------------------------------------------------------*)
(** * Basic lemmata *)
(*----------------------------------------------------------------------------*)

Lemma store_allocated:
  forall {p c v m m'} (A: store_ptr c m p v = Some m') r k,
  range_allocated r k m' <-> range_allocated r k m.
Proof.
  by intros; eapply iff_sym, (store_preserves_allocated_ranges A).
Qed.

Lemma alloc_allocated:
  forall {r' k' m m'} (A: alloc_ptr r' k' m = Some m') r k,
  range_allocated r k m' <-> range_allocated r k m \/ (r = r' /\ k = k').
Proof.
  split; intro; des; clarify.
  - eapply (alloc_preserves_allocated_back A) in H; tauto.
  - by apply (alloc_preserves_allocated A).
  - by destruct (alloc_someD A).
Qed.

Lemma free_allocated:
  forall {p k' m m' n}
    (F: free_ptr p k' m = Some m')
    (RA: range_allocated (p,n) k' m) r k,
  range_allocated r k m' <-> range_allocated r k m /\ fst r <> p.
Proof.
  split; intro; des.
    split; [eby eapply (free_preserves_allocated_back F)|].
    eby intro; clarify; destruct r; eapply free_not_allocated.
  eapply (free_preserves_allocated F) in H; des; clarify.
Qed.

Lemma load_alloc_inside2 :
  forall {r k m m' c' p'},
    alloc_ptr r k m = Some m' ->
    range_inside (range_of_chunk p' c') r ->
    load_ptr c' m' p' = 
      (if pointer_chunk_aligned_dec p' c' then Some Vundef else None).
Proof.
  intros; destruct (pointer_chunk_aligned_dec p' c').
  - eby eapply load_alloc_inside.
  destruct (load_ptr c' m' p') as [] _eqn: X; try done.
  by destruct (load_chunk_allocated_someD X).
Qed.

Lemma load_alloc_not_inside2 :
  forall {r k m m' c' p'},
    alloc_ptr r k m = Some m' ->
    load_ptr c' m p' = None ->
    ~ range_inside (range_of_chunk p' c') r ->
    load_ptr c' m' p' = None.
Proof.
  intros; destruct (ranges_disjoint_dec (range_of_chunk p' c') r).
    by rewrite (load_alloc_other H).
  by rewrite (load_alloc_overlap H). 
Qed.

Lemma load_free_none :
  forall {p k m m' c' p'},
    free_ptr p k m = Some m' ->
    load_ptr c' m p' = None ->
    load_ptr c' m' p' = None.
Proof.
  intros; destruct (free_someD H) as [n RA].
  destruct (ranges_disjoint_dec (range_of_chunk p' c') (p, n)).
    eby erewrite (load_free_other H).
  eby erewrite (load_free_overlap H). 
Qed.

Lemma load_store_none :
  forall {p c v m m' c' p'},
    store_ptr c m p v = Some m' ->
    load_ptr c' m p' = None ->
    load_ptr c' m' p' = None.
Proof.
  intros; destruct (load_ptr c' m' p') as [] _eqn: X; clarify.
  destruct (load_chunk_allocated_someD X) as [(? & ? & ? & RA) ?].
  eapply (store_allocated H) in RA.
  eby destruct (load_chunk_allocated_noneD H0); repeat eexists.
Qed.

(*----------------------------------------------------------------------------*)
(** * Extensional equality on memories *)
(*----------------------------------------------------------------------------*)

Definition mem_eq m1 m2:=
   (forall chunk p, load_ptr chunk m1 p = load_ptr chunk m2 p)
/\ (forall r k, range_allocated r k m1 <-> range_allocated r k m2)
/\ (mrestr m1 = mrestr m2).

Lemma in_block1:
  forall lbnd hbnd l h k ba,
  alloclist_hbound lbnd (mkmobj l h k :: ba) = Some hbnd ->
  0 < lbnd ->
  hbnd <= Int.modulus ->
  valid_access Mint8unsigned (l mod Int.modulus) (mkmobj l h k :: ba).
Proof.
  intros; constructor 1 with (k:=k); [|by apply Zone_divide].
  exists l; exists h; split; [by left|].
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
      by (pose proof (valid_access_bounded _ B ACCOK); omega).
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
      by (pose proof (valid_access_bounded _ B ACCOK); omega).
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
        by (pose proof (valid_access_bounded _ B ACCOK); omega).
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
        by (pose proof (valid_access_bounded _ B ACCOK); omega).
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

    induction ba as [|[l h k] ba IH]; destruct ba' as [|[l' h' k'] ba']; try done;
    intros hbnd' lbnd POS B B' M' Y.
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
      pose proof (alloclist1 _ _ _ _ _ B).
      pose proof (alloclist1 _ _ _ _ _ B').
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

Theorem mem_eq_ext:
  forall m1 m2, mem_eq m1 m2 -> m1 = m2.
Proof.
  intros [mc mr mv] [mc' mr' mv'] [LD [RA MR]]; simpl in *; subst mr'.
  cut (mc = mc'); [by intro; subst mc'; rewrite (proof_irrelevance _ mv mv')|].
  apply ZTree.ext; intros b. 
  destruct (ZTree.get b mc) as [[bc ba]|] _eqn: EQ; 
  destruct (ZTree.get b mc') as [[bc' ba']|] _eqn: EQ'; try done.

  Case "SomeSome".
  generalize (range_allocated_implies_allocs_eq _ _ _ RA EQ EQ'); simpl; intros <-.
  f_equal; f_equal.
  pose proof (proj1 (proj2 (proj2 mv _ _ EQ))) as V.  
  pose proof (proj1 (proj2 (proj2 mv' _ _ EQ'))) as V'.
  apply (contents_eq_ext V V'); intros c ofs VA.
  generalize (LD c (Ptr b (Int.repr ofs))).
  simpl; unfold load; simpl; rewrite EQ, EQ'; simpl.
  rewrite Zmod_small, !in_block_true; try done.
    by intro; clarify.
  by destruct V as (? & ? & ? & B & ?);
     pose proof (valid_access_bounded _ B VA); omega.

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

(*----------------------------------------------------------------------------*)
(** * Load equality on memories *)
(*----------------------------------------------------------------------------*)

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
    (DB: Ptr.block p <> Ptr.block p')
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

(*----------------------------------------------------------------------------*)
(** * Commutativity properties of memory operations *)
(*----------------------------------------------------------------------------*)

(** Allocation commutes over successful stores *)

Lemma alloc_comm_store:
  forall p c v r k m m1 m2 m'
    (A : alloc_ptr r k m = Some m1)
    (B1: store_ptr c m1 p v = Some m')
    (B2: store_ptr c m p v = Some m2),
  alloc_ptr r k m2 = Some m'.
Proof.
  intros.
  pose proof (alloc_someD A) as (? & ? & ? & HA). 
  destruct (ranges_disjoint_dec (range_of_chunk p c) r) as [DISJ|OVER].
  2: by destruct (store_chunk_allocated_someD B2) as [(? & ? & ? & RA) _];
        edestruct HA; try eapply RA; eapply ranges_overlap_comm;
        eby intro; destruct OVER; eapply disjoint_inside_disjoint.

  destruct (alloc_ptr r k m2) as [] _eqn: D; clarify.
  2: by destruct (alloc_noneD D) as [|[|(? & ? & RO & RA)]]; clarify;
        [by destruct r as [[]]; simpl in *; rewrite (restr_of_store B2) in *
        |eby eapply (store_allocated B2) in RA; edestruct HA].

  f_equal; eapply mem_eq_ext; red. 
  rewrite (restr_of_store B1), (restr_of_alloc D), 
          (restr_of_store B2), (restr_of_alloc A).
  split; [|split]; try done.
  Case "load_eq".
  intros c' p'.
  destruct (range_inside_dec (range_of_chunk p' c') r) as [RI | RNI].
    rewrite (load_alloc_inside2 D RI); try done. 
    rewrite <- (load_store_other B1); try done. 
    2: eby eapply disjoint_inside_disjoint_r.
    by rewrite (load_alloc_inside2 A RI).
  destruct (ranges_disjoint_dec (range_of_chunk p' c') r) as [DISJ'| OVER].
    rewrite (load_alloc_other D DISJ').
    eapply load_eq_preserved_by_store; try eassumption.
    by rewrite (load_alloc_other A DISJ').
  rewrite (load_alloc_overlap D RNI OVER); symmetry.
  rewrite (load_store_none B1); try edone.
  eby eapply (load_alloc_overlap A).
  Case "ralloc".
  intros.
  eapply iff_trans, iff_sym, (store_allocated B1).
  eapply iff_trans, iff_sym, (alloc_allocated A).
  eapply iff_trans; [eapply (alloc_allocated D)|].
  by eapply or_iff_compat_r, (store_allocated B2).  
Qed.

(** Allocation commutes over successful allocations *)

Lemma alloc_comm_alloc:
  forall r k r' k' m m1 m2 m'
    (A : alloc_ptr r k m = Some m1)
    (B1: alloc_ptr r' k' m1 = Some m')
    (B2: alloc_ptr r' k' m = Some m2),
  alloc_ptr r k m2 = Some m'.
Proof.
  intros.
  pose proof (alloc_someD A) as (? & ? & ? & HA). 
  pose proof (alloc_someD B1) as (? & ? & ? & HB1); des.
  pose proof (alloc_someD B2) as (? & ? & ? & HB2); des.
  destruct (alloc_ptr r k m2) as [] _eqn: D; clarify.
  Case "some".
  pose proof (alloc_someD D) as (? & _ & _ & HD); des.
  f_equal; eapply mem_eq_ext; red.
  rewrite (restr_of_alloc B1), (restr_of_alloc D), 
          (restr_of_alloc B2), (restr_of_alloc A).
  repeat split;
    try (by intro X; do 2 (
            eapply alloc_preserves_allocated_back in X; try edone;
            destruct X as [[? ?]|X]; clarify;
            eauto using @alloc_preserves_allocated)); [].
  destruct (ranges_disjoint_dec r r') as [DISJ|]; [|eby edestruct HD].
  intros c' p'.
  destruct (range_inside_dec (range_of_chunk p' c') r) as [RI | RNI].
    rewrite (load_alloc_inside2 D RI); try done. 
    rewrite (load_alloc_other B1); try done. 
    2: eby eapply disjoint_inside_disjoint.
    by rewrite (load_alloc_inside2 A RI).
  destruct (ranges_disjoint_dec (range_of_chunk p' c') r) as [DISJ'| OVER].
    rewrite (load_alloc_other D DISJ').
    eapply load_eq_preserved_by_alloc; try eassumption.
    by rewrite (load_alloc_other A DISJ').
  rewrite (load_alloc_overlap D RNI OVER); symmetry.

  destruct (load_ptr c' m' p') as [] _eqn: X; clarify.
  destruct (load_chunk_allocated_someD X) as [(? & ? & ? & ?) ?].
  destruct (load_chunk_allocated_noneD (load_alloc_overlap A RNI OVER)).
  eapply alloc_preserves_allocated_back in H10; try edone.
  des; split; vauto.
  eby destruct OVER; eapply ranges_disjoint_comm, disjoint_inside_disjoint_r.

  Case "none".
  pose proof (alloc_noneD D) as [|[|(r'' & k'' & RO & RA)]]; clarify.
  - by destruct r as [[]]; destruct r' as [[]]; simpl in *; 
       rewrite (restr_of_alloc B2) in *.
  destruct (alloc_preserves_allocated_back B2 _ _ RA); des; clarify.
  - eby edestruct HB1; try eapply ranges_overlap_comm.
  eby edestruct HA.
Qed.

(** Allocation commutes over successful frees *)

Lemma alloc_comm_free:
  forall r k p k' m m1 m2 m'
    (A : alloc_ptr r k m = Some m1)
    (B1: free_ptr p k' m1 = Some m')
    (B2: free_ptr p k' m = Some m2),
  alloc_ptr r k m2 = Some m'.
Proof.
  intros.
  pose proof (alloc_someD A) as (? & ? & ? & HA). 
  pose proof (free_someD B1) as (n1 & HB1); des.
  pose proof (free_someD B2) as (n2 & HB2); des.
  destruct (alloc_preserves_allocated_back A _ _ HB1) as [[]|]; clarify.
  - edestruct HA; try edone.
    by eapply non_empty_same_ptr_overlap;
       eauto using @valid_alloc_range_non_empty, @allocated_range_valid.
  destruct (alloc_ranges_same HB2 H2) as [? _]; clarify.
  destruct (ranges_disjoint_dec r (p, n1)) as [DISJ|]; [|eby edestruct HA].
  clear H2.
  destruct (alloc_ptr r k m2) as [] _eqn: D; clarify.

  Case "some".
  pose proof (alloc_someD D) as (? & _ & _ & HD); des.
  f_equal; eapply mem_eq_ext; red.
  rewrite (restr_of_free B1), (restr_of_alloc D), 
          (restr_of_free B2), (restr_of_alloc A).
  split; [|split]; try done.
  SCase "load_eq".
  intros c' p'.
  destruct (range_inside_dec (range_of_chunk p' c') r) as [RI | RNI].
    rewrite (load_alloc_inside2 D RI); try done. 
    erewrite (load_free_other B1); try edone. 
    2: eby eapply disjoint_inside_disjoint.
    by rewrite (load_alloc_inside2 A RI).
  destruct (ranges_disjoint_dec (range_of_chunk p' c') r) as [DISJ'| OVER].
    rewrite (load_alloc_other D DISJ').
    eapply load_eq_preserved_by_free_same_size; try eapply B1; try eapply B2; try eassumption.
    by rewrite (load_alloc_other A DISJ').
  rewrite (load_alloc_overlap D RNI OVER); symmetry.
  destruct (load_ptr c' m' p') as [] _eqn: X; clarify.
  destruct (load_chunk_allocated_someD X) as [(? & ? & ? & RA) ?].
  eapply free_preserves_allocated_back in RA; try edone.
  destruct (load_chunk_allocated_noneD (load_alloc_overlap A RNI OVER)).
  by split; vauto.
  SCase "ralloc".
  intros.
  eapply iff_trans, iff_sym, (free_allocated B1); try edone.
  eapply iff_trans, iff_sym, and_iff_compat_r, (alloc_allocated A).
  eapply iff_trans; [eapply (alloc_allocated D)|].
  eapply iff_trans; [eby eapply or_iff_compat_r; eapply (free_allocated B2)|].
  destruct r0; split; intro; des; clarify; vauto.
  split; vauto; simpl; intro; clarify.
  edestruct HA; try edone.
  by eapply non_empty_same_ptr_overlap;
     eauto using @valid_alloc_range_non_empty, @allocated_range_valid.
 
  Case "none".
  pose proof (alloc_noneD D) as [|[[]|(r'' & k'' & RO & RA)]]; clarify.
  - by destruct r as [[]]; destruct p; simpl; rewrite (restr_of_free B2).
  pose proof (free_preserves_allocated_back B2 _ _ RA); des; clarify.
  eby edestruct HA.
Qed.


(** Free commutes over successful stores *)

Lemma free_comm_store:
  forall p c v r k m m1 m2 m'
    (A : free_ptr r k m = Some m1)
    (B1: store_ptr c m1 p v = Some m')
    (B2: store_ptr c m p v = Some m2),
  free_ptr r k m2 = Some m'.
Proof.
  intros.
  pose proof (free_someD A) as (n & RA). 
  destruct (store_chunk_allocated_someD B1) as [(rr & k' & RI & RA1) _].
  destruct (free_ptr r k m2) as [m''|] _eqn: D; clarify.
  2: eby eapply (store_allocated B2) in RA; edestruct (free_noneD D).
  f_equal; eapply mem_eq_ext; red.
  rewrite (restr_of_store B1), (restr_of_free D), 
          (restr_of_store B2), (restr_of_free A).
  split; [|split]; try done.
  Case "load_eq".
  destruct (ranges_are_disjoint RA (free_preserves_allocated_back A _ _ RA1)) as [[]|DISJ].
  + eby clarify; edestruct (free_not_allocated A).
  intros c' p'.
  destruct (ranges_disjoint_dec (range_of_chunk p' c') 
                                       (r, n)) as [DISJ' | OVER].
    erewrite (load_free_other D); try edone; try eby eapply store_allocated. 
    eapply load_eq_preserved_by_store; try eassumption.
    eby erewrite (load_free_other A).
  erewrite (load_free_overlap D); try edone; try eby eapply store_allocated.
  rewrite (load_store_none B1); try edone.
  eby eapply (load_free_overlap A).
  Case "ralloc".
  intros.
  eapply iff_trans, iff_sym, (store_allocated B1).
  eapply iff_trans, iff_sym, (free_allocated A RA). 
  eapply iff_trans, and_iff_compat_r, (store_allocated B2).
  eby eapply (free_allocated D), (store_allocated B2).
Qed.

(** Free commutes over successful allocations *)

Lemma free_comm_alloc:
  forall p k r k' m m1 m2 m'
    (A : free_ptr p k m = Some m1)
    (B1: alloc_ptr r k' m1 = Some m')
    (B2: alloc_ptr r k' m = Some m2),
  free_ptr p k m2 = Some m'.
Proof.
  intros.
  pose proof (free_someD A) as (n & pRA). 
  pose proof (alloc_someD B1) as (RA' & _ & _ & HB1).
  pose proof (alloc_someD B2) as (RA2 & _ & _ & HB).
  destruct (free_ptr p k m2) as [m''|] _eqn: D; clarify.
  2: eby edestruct (free_noneD D); eapply alloc_preserves_allocated.
  f_equal; eapply mem_eq_ext; red.
  rewrite (restr_of_alloc B1), (restr_of_free D), 
          (restr_of_alloc B2), (restr_of_free A).
  split; [|split]; try done.
  Case "load_eq".
  intros c' p'.
  destruct (ranges_disjoint_dec (range_of_chunk p' c') (p, n)) as [DISJ' | OVER].
    erewrite (load_free_other D); try edone; try eby eapply alloc_preserves_allocated. 
    eapply load_eq_preserved_by_alloc; try eassumption.
    eby erewrite (load_free_other A).
  erewrite (load_free_overlap D); try edone; try eby eapply alloc_preserves_allocated.
  erewrite load_alloc_not_inside2; try edone.
    eby erewrite (load_free_overlap A). 
  intro.
  destruct OVER.
  eapply disjoint_inside_disjoint; try edone.
  edestruct (ranges_are_disjoint RA2 (alloc_preserves_allocated B2 _ _ pRA)) as [[]|];
    clarify.
  edestruct HB; try edone.
  by eapply non_empty_same_ptr_overlap;
     eauto using @valid_alloc_range_non_empty, @allocated_range_valid.
  Case "ralloc".
  intros.
  eapply iff_trans, iff_sym, (alloc_allocated B1); try done.
  eapply iff_trans, iff_sym, or_iff_compat_r, (free_allocated A pRA); try done.
  eapply iff_trans. 
    eapply (free_allocated D); try edone; try eby eapply alloc_preserves_allocated.
  eapply iff_trans; [eby eapply and_iff_compat_r; eapply (alloc_allocated B2)|].
  split; intro; des; clarify; vauto.
  split; vauto; intro; clarify.
  destruct r; edestruct HB; try edone.
  by eapply non_empty_same_ptr_overlap;
     eauto using @valid_alloc_range_non_empty, @allocated_range_valid.
Qed.

(** Free commutes over successful frees *)

Lemma free_comm_free:
  forall p k p' k' m m1 m2 m'
    (A : free_ptr p k m = Some m1)
    (B1: free_ptr p' k' m1 = Some m')
    (B2: free_ptr p' k' m = Some m2),
  free_ptr p k m2 = Some m'.
Proof.
  intros.
  pose proof (free_someD A) as (n & pRA). 
  pose proof (free_someD B1) as (n' & RA').
  assert (NEQ: p <> p') by (intro; clarify; apply (free_not_allocated A _ _ RA')).
  destruct (free_preserves_allocated B2 _ _ pRA); des; clarify.
  destruct (free_ptr p k m2) as [m''|] _eqn: D.
  2: eby edestruct (free_noneD D). 
  f_equal; eapply mem_eq_ext; red.
  rewrite (restr_of_free B1), (restr_of_free D), 
          (restr_of_free B2), (restr_of_free A).
  split; [|split]; try done.
  Case "load_eq".
  intros c' p''.
  destruct (ranges_disjoint_dec (range_of_chunk p'' c') (p, n)) as [DISJ' | OVER].
    erewrite (load_free_other D); try edone; try eby eapply alloc_preserves_allocated. 
    eapply (load_eq_preserved_by_free_same_size); try eapply B1; try eapply B2; try eassumption.
    - eby erewrite (load_free_other A).
    eby eapply free_preserves_allocated_back in RA'.
  erewrite (load_free_overlap D); try edone. 
  rewrite (load_free_none B1); try edone.
  eby erewrite (load_free_overlap A).
  Case "ralloc".
  intros.
  eapply iff_trans, iff_sym, (free_allocated B1); try edone.
  eapply iff_trans, iff_sym, and_iff_compat_r, (free_allocated A pRA); try done.
  eapply iff_trans; [eby eapply (free_allocated D)|]. 
  eapply iff_trans; [eby eapply and_iff_compat_r; eapply (free_allocated B2); 
                         eapply (free_preserves_allocated_back A _ _ RA')|].
  tauto.
Qed.

(*----------------------------------------------------------------------------*)
(** ** Simple corollaries *)
(*----------------------------------------------------------------------------*)

Lemma alloc_comm_alloc_none:
  forall r k r' k' m m1 m2
    (A : alloc_ptr r k m = Some m1)
    (B : alloc_ptr r' k' m1 = None)
    (C : alloc_ptr r' k' m = Some m2),
    alloc_ptr r k m2 = None.
Proof.
  intros; destruct (alloc_ptr r k m2) as [] _eqn: D; clarify.
  eby erewrite alloc_comm_alloc in B.
Qed.

Lemma store_comm_alloc:
  forall r k c p v m m1 m2
    (A : store_ptr c m p v = Some m1)
    (B : alloc_ptr r k m1 = Some m2),
    exists m', alloc_ptr r k m = Some m' /\ store_ptr c m' p v = Some m2.
Proof.
  intros; destruct (alloc_ptr r k m) as [m'|] _eqn: C; clarify.
  - repeat eexists; try edone.
    destruct (store_ptr c m' p v) as [] _eqn: D.
    + eby erewrite alloc_comm_store in B.
    destruct (store_chunk_allocated_someD A) as [(?&?&?&?)?].
    destruct (store_chunk_allocated_noneD D); repeat eexists; try edone.
    eby eapply alloc_preserves_allocated.
  destruct (alloc_someD B) as (? & ? & ? & BB).
  destruct (alloc_noneD C); des; clarify.
  - by destruct r as [[]]; simpl in *; rewrite (restr_of_store A) in *.
  eby edestruct BB; try edone; eapply (store_allocated A).
Qed.

Lemma free_comm_store2:
  forall r k c p v m m1 m2
    (A : free_ptr r k m = Some m1)
    (B : store_ptr c m1 p v = Some m2),
    exists m', store_ptr c m p v = Some m' /\ free_ptr r k m' = Some m2.
Proof.
  intros; destruct (store_ptr c m p v) as [m'|] _eqn: C; clarify.
  - eby repeat eexists; try edone; eapply free_comm_store.
  destruct (store_chunk_allocated_someD B) as [(?&?&?&?)?].
  destruct (store_chunk_allocated_noneD C); repeat eexists; try edone.
  eby eapply (free_preserves_allocated_back A).
Qed.
