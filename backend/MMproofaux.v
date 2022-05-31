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

(** Simulation between the two semantics for the Mach language. Part I. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Pointers.
Require Import Values.
Require Import Mem.
Require Import Memeq.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Asm.
(* Require Import Mach. *)
(* Require Import Machtyping. *)
(* Require Import Machconcr.*)
(* Require Import Machabstr. *)
Require Import Libtactics.

Notation chunk_of_type := Asm.chunk_of_ty.

(** * Helpful tactics *)

Ltac myremember EQ term Hyp :=
  cut (exists x, x = term); [|by eexists; apply refl_equal];
  intros [? EQ]; rewrite <- EQ in Hyp.

(** * Basic lemmas *)

Remark size_type_chunk:
  forall ty, size_chunk (chunk_of_type ty) = Ast.typesize ty.
Proof.
  by destruct ty.
Qed.

Lemma range_not_in_ext:
  forall r l l'
    (EQ: list_equiv l l')
    (NIN: range_not_in r l),
    range_not_in r l'.
Proof.
  by unfold range_not_in; intros; apply NIN, (proj2 (EQ _)).
Qed.

Lemma chunk_inside_range_list_ext:
  forall p c l l'
    (EQ: list_equiv l l')
    (IN: chunk_inside_range_list p c l),
    chunk_inside_range_list p c l'.
Proof.
  intros; destruct (chunk_inside_range_listD IN) as (k & IN1 & RI).
  eby eapply chunk_inside_range_listI; [eapply (proj1 (EQ _))|].
Qed.

Lemma pointer_in_range_list_ext:
  forall p l l'
    (EQ: list_equiv l l')
    (IN: pointer_in_range_list p l),
    pointer_in_range_list p l'.
Proof.
  intros; destruct (pointer_in_range_listD IN) as (k & IN1).
  eby eapply pointer_in_range_listI; eapply (proj1 (EQ _)).
Qed.

Lemma list_equiv_cons_cong:
  forall A l l' (x:A) (H: list_equiv l l'),
  list_equiv (x :: l) (x :: l').
Proof.
  split; simpl; (intros [IN|IN]; [by left; clarify|eby right; eapply (H _)]).
Qed.

Lemma list_equiv_range_remove_cong:
  forall p l l' (H: list_equiv l l'),
    list_equiv (range_remove p l) (range_remove p l').
Proof.
  by split; destruct x; simpl;
     intros IN; destruct (in_range_removeD IN);
     apply in_range_removeI; try done; apply (H _).
Qed.

Definition Punsigned (i: int) := 
  if zeq (Int.unsigned i) 0 then Int.modulus else Int.unsigned i.

Definition valid_erange r :=
  let '(Ptr b ofs, s) := r in 
    Int.unsigned s < Int.half_modulus /\
    Punsigned ofs + Int.unsigned s <= Int.modulus.

Definition range_top (r: arange) := Ptr.add (fst r) (snd r).

Definition range_sp (stkr: arange) (sp: pointer) :=
  (Ptr (Ptr.block (fst stkr)) (Ptr.offset sp), 
    Int.sub (Ptr.offset (range_top stkr)) (Ptr.offset sp)).

Lemma valid_erange_sub: forall n p
  (LT1: Int.unsigned n < Int.half_modulus)
  (LT2: Int.unsigned n < Punsigned (Ptr.offset p)),
  valid_erange (Ptr.sub_int p n, n).
Proof.
  unfold valid_erange, Punsigned; intros.
  destruct n as [n N]; destruct p as [b [p P]]; simpl in *.
  destruct (zeq n 0); subst.
    rewrite Zminus_0_r, Zmod_small; [destruct zeq|]; omega. 
  destruct (zeq p 0); subst.
    rewrite Zmod_neg_range; [destruct zeq|]; omega.
  rewrite Zmod_small; [destruct zeq|]; omega.
Qed.


Definition range_list_in_range (p : list arange) (r' : arange) : Prop := 
  forall r, In r p -> range_inside r r'.

Lemma range_list_in_range_ext:
 forall l1 l2 r
   (EQ : list_equiv l1 l2)
   (RA : range_list_in_range l1 r),
 range_list_in_range l2 r.
Proof. by intros; intros ? IN; apply RA, (EQ _). Qed.


Lemma range_sp_inside_stack:
  forall stkr p
    (V: valid_erange stkr)
    (INsp: range_inside (p, Int.zero) stkr),
    range_inside (range_sp stkr p) stkr.
Proof.
  unfold valid_erange, Punsigned, range_inside.
  intros [[? [r ?]] [sz ?]] [? [p ?]]; simpl; Zsimps.
  destruct (zeq p (r + sz)) as [EQ|NEQ]; subst.
  assert (r + sz - (r + sz) = 0) as ->; [|intros; Zsimps]; omega.  
  intros; destruct zeq; try omega.
  destruct INsp as [? [[? [? ?]]|[? ?]]]; subst.
    assert (r + sz = Int.modulus) as -> by omega; Zsimps; omega.
  rewrite Zmod_small; omega.
Qed.

Lemma range_inside_endpoints_sub:
  forall r p n
    (INp: range_inside (p, Int.zero) r)
    (INn: range_inside (Ptr.sub_int p n, Int.zero) r)
    (Vn: valid_erange (Ptr.sub_int p n, n))
    (Vr: valid_erange r),
  range_inside (Ptr.sub_int p n, n) r.
Proof.
  unfold valid_erange, Punsigned, range_inside in *.
  intros [[? [r R]] [s S]] [? [p P]] [n N]; simpl; Zsimps.
  destruct (zlt p n);
    [rewrite Zmod_too_small | rewrite Zmod_small];
    try omega; intros; repeat (destruct zeq; try omega).
Qed.

Lemma range_inside_endpoints_add:
  forall r p n
    (INp: range_inside (p, Int.zero) r)
    (INn: range_inside (Ptr.add p n, Int.zero) r)
    (Vn: valid_erange (p, n))
    (Vr: valid_erange r),
  range_inside (p, n) r.
Proof.
  intros.
  assert (EQ: p = Ptr.sub_int (Ptr.add p n) n).
    by rewrite Ptr.sub_add_l, Int.sub_idem, Ptr.add_zero_r.
  rewrite EQ in INp |- *.
  apply range_inside_endpoints_sub; try done.
  by rewrite <- EQ.
Qed.

Lemma range_inside_range_sp_sub:
  forall stkr p n
    (V: valid_erange stkr)
    (Vn: valid_erange (Ptr.sub_int p n, n))
    (INn: range_inside (Ptr.sub_int p n, Int.zero) stkr)
    (INsp: range_inside (p, Int.zero) stkr),
    range_inside (Ptr.sub_int p n, n) (range_sp stkr (Ptr.sub_int p n)).
Proof.
  unfold valid_erange, Punsigned, range_inside in *.
  intros [[? [r R]] [s S]] [? [p P]] [n N]; simpl; Zsimps.
  destruct (zlt p n); 
    [rewrite (Zmod_too_small (p - n)) | 
      rewrite (Zmod_small (p - n)) ]; Zsimps; intros; try omega.
  destruct (zeq (Int.modulus + (p - n)) 0); [by subst; omega|].
    destruct INn as [? [|]]; [omega|].
    assert (p = 0) by omega; subst; Zsimps.
    destruct zeq; subst; Zsimps; try omega.
    rewrite Zmod_too_big; omega.
  destruct (zeq (p - n) 0); subst; Zsimps.
    assert (n = 0) by omega; subst.
    assert (p = 0) by omega; subst; Zsimps.
    destruct zeq. subst; Zsimps.
      assert (s = 0) by omega; subst; Zsimps; omega.
    destruct INn as [? [|]]; [|omega]. 
    assert (r + s = Int.modulus) as ->; Zsimps; omega.
  rewrite Zmod_small; omega.
Qed.

Lemma range_inside_range_sp:
  forall stkr p n
    (V: valid_erange stkr)
    (Vn: valid_erange (p, n))
    (INn: range_inside (Ptr.add p n, Int.zero) stkr)
    (INsp: range_inside (p, Int.zero) stkr),
    range_inside (p, n) (range_sp stkr p).
Proof.
  intros.
  assert (EQ: p = Ptr.sub_int (Ptr.add p n) n).
    by rewrite Ptr.sub_add_l, Int.sub_idem, Ptr.add_zero_r.
  rewrite EQ in INsp |- *.
  apply range_inside_range_sp_sub; try done.
  by rewrite <- EQ.
Qed.

Lemma range_sp_inside_range_sp_sub:
  forall stkr p n
    (V: valid_erange stkr)
    (Vn: valid_erange (Ptr.sub_int p n, n))
    (INn: range_inside (Ptr.sub_int p n, Int.zero) stkr)
    (INsp: range_inside (p, Int.zero) stkr),
    range_inside (range_sp stkr p) (range_sp stkr (Ptr.sub_int p n)).
Proof.
  unfold valid_erange, Punsigned, range_inside in *.
  intros [[? [r R]] [s S]] [? [p P]] [n N]; simpl; Zsimps.
  destruct (zlt p n); 
    [rewrite (Zmod_too_small (p - n)) | 
      rewrite (Zmod_small (p - n)) ]; Zsimps; intros; try omega.
  destruct (zeq (Int.modulus + (p - n)) 0); [by subst; omega|].
    destruct INn as [? [|]]; [omega|].
    assert (p = 0) by omega; subst; Zsimps.
    destruct zeq; subst; Zsimps; try omega.
    rewrite !Zmod_too_big; try omega.
  destruct (zeq (p - n) 0); subst; Zsimps.
    assert (n = 0) by omega; subst.
    assert (p = 0) by omega; subst; Zsimps.
    destruct zeq. subst; Zsimps.
      assert (s = 0) by omega; subst; Zsimps; omega.
    destruct INn as [? [|]]; [|omega]. 
    assert (r + s = Int.modulus) as ->; Zsimps; omega.
  rewrite !Zmod_small; try omega.
Qed.

Lemma range_sp_inside_range_sp_add:
  forall stkr p n
    (V: valid_erange stkr)
    (Vn: valid_erange (p, n))
    (INn: range_inside (Ptr.add p n, Int.zero) stkr)
    (INsp: range_inside (p, Int.zero) stkr),
    range_inside (range_sp stkr (Ptr.add p n)) (range_sp stkr p).
Proof.
  intros.
  assert (EQ: p = Ptr.sub_int (Ptr.add p n) n).
    by rewrite Ptr.sub_add_l, Int.sub_idem, Ptr.add_zero_r.
  rewrite EQ in INsp; rewrite EQ at 2.  
  apply range_sp_inside_range_sp_sub; try done.
  by rewrite <- EQ.
Qed.

Lemma ranges_disjoint_range_sp_sub:
  forall stkr p n
    (V: valid_erange stkr)
    (Vn: valid_erange (Ptr.sub_int p n, n))
    (INn: range_inside (Ptr.sub_int p n, Int.zero) stkr)
    (INsp: range_inside (p, Int.zero) stkr),
    ranges_disjoint (Ptr.sub_int p n, n) (range_sp stkr p).
Proof.
  unfold valid_erange, Punsigned, range_inside, ranges_disjoint in *.
  intros [[? [r R]] [s S]] [? [p P]] [n N]; simpl; Zsimps.
  destruct (zlt p n); 
    [rewrite (Zmod_too_small (p - n)) | 
      rewrite (Zmod_small (p - n)) ]; Zsimps; intros; try omega.
  destruct (zeq (Int.modulus + (p - n)) 0); [by subst; omega|].
  destruct INn as [? [|]]; [omega|].
  assert (p = 0) by omega; subst; Zsimps.
  destruct zeq; subst; Zsimps; try omega.
  rewrite !Zmod_too_big; omega.
Qed.

Lemma ranges_disjoint_range_sp_add:
  forall stkr p n
    (V: valid_erange stkr)
    (Vn: valid_erange (p, n))
    (INn: range_inside (Ptr.add p n, Int.zero) stkr)
    (INsp: range_inside (p, Int.zero) stkr),
    ranges_disjoint (p, n) (range_sp stkr (Ptr.add p n)).
Proof.
  intros.
  assert (EQ: p = Ptr.sub_int (Ptr.add p n) n).
    by rewrite Ptr.sub_add_l, Int.sub_idem, Ptr.add_zero_r.
  rewrite EQ in INsp; rewrite EQ at 1.  
  apply ranges_disjoint_range_sp_sub; try done.
  by rewrite <- EQ.
Qed.

Lemma valid_erange_add1: forall n p r
  (INn: range_inside (Ptr.add p n, Int.zero) r)
  (INp: range_inside (p, Int.zero) r)
  (SZn: Int.unsigned n < Int.half_modulus)
  (V : valid_erange r),
   valid_erange (p, n).
Proof.
  unfold range_inside, valid_erange, Punsigned.
  intros [n N] [b [p P]] [[? [r R]] [s S]]; simpl; Zsimps.
  destruct (zlt (p + n) Int.modulus);
    [rewrite Zmod_small | rewrite Zmod_too_big]; try omega;
     repeat destruct zeq; intros; try omega;
      destruct INn as [? [|]]; try omega; 
      destruct INp as [? [|]]; try omega. 
  - assert (Y: Int.modulus - Int.half_modulus < n) by omega.
    change (Int.modulus - Int.half_modulus) with Int.half_modulus in Y; omega.
  assert (X: s >= Int.modulus - Int.half_modulus) by omega.
  change (Int.modulus - Int.half_modulus) with Int.half_modulus in X; omega.
Qed.

Lemma valid_erange_sub1: forall n p r
  (INn: range_inside (Ptr.sub_int p n, Int.zero) r)
  (INp: range_inside (p, Int.zero) r)
  (SZn: Int.unsigned n < Int.half_modulus)
  (V : valid_erange r),
   valid_erange (Ptr.sub_int p n, n).
Proof.
  unfold range_inside, valid_erange, Punsigned.
  intros [n N] [b [p P]] [[? [r R]] [s S]]; simpl. Zsimps.
  destruct (zlt p n); 
    [rewrite Zmod_too_small | rewrite Zmod_small]; try omega;
     repeat destruct zeq; intros; try omega;
      destruct INn as [? [|]]; try omega; 
      destruct INp as [? [|]]; try omega. 
  - assert (Y: Int.modulus - Int.half_modulus < n) by omega.
    change (Int.modulus - Int.half_modulus) with Int.half_modulus in Y; omega.
  assert (X: p >= Int.modulus - Int.half_modulus) by omega.
  change (Int.modulus - Int.half_modulus) with Int.half_modulus in X; omega.
Qed.

Lemma range_inside_interm_sub: forall n1 n2 p r
  (INn: range_inside (Ptr.sub_int p (Int.add n1 n2), Int.zero) r)
  (INp: range_inside (p, Int.zero) r)
  (SZn: Int.unsigned n1 + Int.unsigned n2 < Int.half_modulus)
  (V : valid_erange r),
  range_inside (Ptr.sub_int p n1, Int.zero) r.
Proof.
  unfold range_inside, valid_erange, Punsigned.
  intros [n1 N1] [n2 N2] [b [p P]] [[b' [r R]] [s S]]; simpl; Zsimps.
  intros.
  assert (- Int.half_modulus <= p - n1 - n2) by omega.
  assert (Int.half_modulus < Int.modulus) by done.
  destruct (zlt p (n1 + n2)); 
    [rewrite Zmod_too_small in INn | rewrite Zmod_small in INn]; try omega;
  (destruct (zlt p n1); [rewrite Zmod_too_small|rewrite Zmod_small]; try omega);
  destruct zeq; subst; try omega;
  destruct INn as [? [|]]; try omega;
  destruct INp as [? [|]]; try omega.
      assert (X: Int.modulus - Int.half_modulus < n1 + n2) by omega.
      change (Int.modulus - Int.half_modulus) with Int.half_modulus in X; omega.
    assert (X: Int.modulus - Int.half_modulus < n1 + n2) by omega.
    change (Int.modulus - Int.half_modulus) with Int.half_modulus in X; omega.
  assert (X: p >= Int.modulus - Int.half_modulus) by omega.
  change (Int.modulus - Int.half_modulus) with Int.half_modulus in X; omega.
Qed.

Lemma range_inside_interm_add: forall n1 n2 p r
  (INn: range_inside (Ptr.add p (Int.add n1 n2), Int.zero) r)
  (INp: range_inside (p, Int.zero) r)
  (SZn: Int.unsigned n1 + Int.unsigned n2 < Int.half_modulus)
  (V : valid_erange r),
  range_inside (Ptr.add p n1, Int.zero) r.
Proof.
  intros.
  replace (Ptr.add p n1) with (Ptr.sub_int (Ptr.add p (Int.add n1 n2)) n2).
    apply range_inside_interm_sub with (n2 := n1); try done.
      by rewrite Ptr.sub_add_l, Int.add_commut, Int.sub_idem, Ptr.add_zero_r.
    by rewrite Zplus_comm.
  by rewrite Ptr.sub_add_l, Int.add_commut, Int.sub_add_l, 
             Int.sub_idem, Int.add_commut, Int.add_zero.
Qed.

Lemma range_inside_sub_add_r:
  forall p n1 n2
    (SZ_OK : Int.unsigned n1 + Int.unsigned n2 < Int.half_modulus)
    (Vn1 : valid_erange (p, n1))
    (Vn2 : valid_erange (Ptr.sub_int p n2, Int.add n1 n2)),
   range_inside (p, n1) (Ptr.sub_int p n2, Int.add n1 n2).
Proof.
  unfold range_inside, valid_erange, Punsigned.
  intros [b [p P]] [n1 N1] [n2 N2] SZ_OK; simpl in *; Zsimps.
  assert (Int.half_modulus < Int.modulus) by done.
  rewrite (Zmod_small (n1 + n2)); [|omega].
  destruct (zlt p n2); 
    [rewrite Zmod_too_small|rewrite Zmod_small]; try omega;
  intros; do 2 destruct zeq; try omega.
Qed.


Remark Zmod_size_chunk:
  forall chunk, size_chunk chunk mod Int.modulus = size_chunk chunk.
Proof.
  by destruct chunk; rewrite Zmod_small.
Qed.

Lemma range_inside_bottom:
  forall p n stkr (RI: range_inside (p, n) stkr),
    range_inside (p, Int.zero) stkr.
Proof.
  intros.
  destruct p. destruct stkr as [[bstkr ostkr] nstkr].
  unfold range_inside.
  destruct RI as [-> [(-> & E & ABOVE) | (LB & UB)]]. tauto.
  split. done. right. split. tauto.
  replace (Int.unsigned Int.zero) with 0 by done.
  pose proof (Int.unsigned_range n). omega.
Qed.

Lemma unsigned_zero: Int.unsigned Int.zero = 0. 
Proof. done. Qed.

Lemma range_inside_top:
  forall p n stkr 
    (RI: range_inside (p, n) stkr) 
    (VE: valid_erange (p, n)),
    range_inside (Ptr.add p n, Int.zero) stkr.
Proof.
  intros.
  destruct p. destruct stkr as [[bstkr ostkr] nstkr].
  unfold range_inside.
  destruct RI as [-> [(Ei & En & ABOVE) | (LB & UB)]].
    split. done. left. split.
      by rewrite Int.add_unsigned, En, Zplus_0_r, Int.repr_unsigned.
    tauto.
  split. done. 
  pose proof (Int.unsigned_range n).
  pose proof (Int.unsigned_range i).
  destruct VE as [_ LE].
  destruct (Z_le_lt_eq_dec _ _ LE).
  right.
    assert (E: Int.unsigned (Int.add i n) = Int.unsigned i + Int.unsigned n).
      rewrite Int.add_unsigned, Int.unsigned_repr. omega.
      unfold valid_erange, Int.max_unsigned in *. 
      unfold Punsigned in *; destruct zeq; omega. 
    rewrite E, unsigned_zero; split; omega.
  unfold Punsigned in *; destruct zeq.
    right.
    split. rewrite Int.add_unsigned, Int.unsigned_repr. omega.
    replace (Int.unsigned i + Int.unsigned n) with 0 by omega. by compute.
    rewrite Int.add_unsigned, Int.unsigned_repr, unsigned_zero. omega.
    replace (Int.unsigned i + Int.unsigned n) with 0 by omega. by compute.
  left.
  split. rewrite Int.add_unsigned, e. by compute.
  split. done.
  omega.
Qed.

Lemma range_inside_valide:
  forall r r'
    (RI: range_inside r r')
    (VE: valid_erange r'),
    valid_erange r.
Proof.
  intros [[b ofs] n] [[b' ofs'] n'] ? ?.
  unfold valid_erange, range_inside in *.
  destruct RI as [Eb [(Eofs & En & ABOVE) | (LT1 & LT2)]].
    rewrite En. split. by compute. 
    unfold Punsigned. destruct zeq. by compute.
    by rewrite Eofs; compute.
  split. omega. 
  unfold Punsigned in *.
  pose proof (Int.unsigned_range ofs').
  repeat destruct zeq; omega. 
Qed.

Lemma range_sp_inside_range_sp_add2:
  forall (stkr : pointer * int) (p : pointer) (n : int),
     valid_erange stkr ->
     range_inside (p, n) stkr ->
     range_inside (range_sp stkr (p + n)) (range_sp stkr p).
Proof.
  intros.
  apply range_sp_inside_range_sp_add. done.
  eapply range_inside_valide; edone. 
  eapply range_inside_top, range_inside_valide; edone. 
  eby eapply range_inside_bottom.
Qed.

Lemma valid_erange_modulus:
  forall {b ofs n},
  valid_erange (Ptr b ofs, n) ->
  Int.unsigned ofs + Int.unsigned n <= Int.modulus.
Proof.
  intros ? ? ? []. unfold Punsigned.
  pose proof (Int.unsigned_range n).
  destruct zeq; intros; omega.
Qed.

Lemma range_inside_range_sp2: 
  forall stkr p n,
       valid_erange stkr ->
       range_inside (p, n) stkr ->
       range_inside (p, n) (range_sp stkr p).
Proof.
  intros.
  apply range_inside_range_sp. edone.
  eby eapply range_inside_valide. apply range_inside_top. done.
  eby eapply range_inside_valide.
  eby eapply range_inside_bottom.
Qed.

Lemma ranges_disjoint_range_sp_add2:
  forall stkr p n
    (V: valid_erange stkr)
    (INn: range_inside (p, n) stkr),
    ranges_disjoint (p, n) (range_sp stkr (Ptr.add p n)).
Proof.
  intros.
  eapply ranges_disjoint_range_sp_add. edone.
  eby eapply range_inside_valide.
  apply range_inside_top. done.
  eby eapply range_inside_valide.
  eby eapply range_inside_bottom.
Qed.  

Lemma range_inside_subrange:
  forall p n a b,
    valid_erange (p, n) ->
    Int.unsigned a + Int.unsigned b <= Int.unsigned n ->
    range_inside (Ptr.add p a, b) (p, n).
Proof.
  intros [b ofs] n a n' VE En.
  split. done.
  pose proof (Int.unsigned_range a).
  pose proof (Int.unsigned_range n').
  pose proof (Int.unsigned_range ofs).
  pose proof (Int.unsigned_range n).
  pose proof (valid_erange_modulus VE).
  assert (X : Int.unsigned ofs + Int.unsigned a <= Int.modulus) by omega.
  destruct (Z_le_lt_eq_dec _ _ X).
    right. 
    assert (Eadd: Int.unsigned (Int.add ofs a) = Int.unsigned ofs + Int.unsigned a).
      rewrite Int.add_unsigned, Int.unsigned_repr. omega. 
      unfold Int.max_unsigned. omega.
    rewrite Eadd.    
    split; omega. 
  left. 
  split. rewrite Int.add_unsigned, e. by compute.
  split; omega.
Qed.

Lemma range_inside_smaller:
  forall p n n',
    valid_erange (p, n) ->
    Int.unsigned n' <= Int.unsigned n ->
    range_inside (p, n') (p, n).
Proof.
  intros.
  rewrite <- (Ptr.add_zero_r p) at 1.
  eapply range_inside_subrange. done.
  rewrite unsigned_zero. omega.
Qed.

Lemma range_inside_endpoints_sub2:
  forall r p n
    (INp: range_inside (p, Int.zero) r)
    (INn: range_inside (Ptr.sub_int p n, Int.zero) r)
    (Nsmall: Int.unsigned n < Int.half_modulus)
    (Vr: valid_erange r),
  range_inside (Ptr.sub_int p n, n) r.
Proof.
  unfold valid_erange, Punsigned, range_inside in *.

  unfold valid_erange, Punsigned, range_inside in *.
  intros [[? [r R]] [s S]] [? [p P]] [n N]; simpl; Zsimps.
  assert (Int.modulus = Int.half_modulus + Int.half_modulus). by compute.
  destruct (zlt p n);
    [rewrite Zmod_too_small | rewrite Zmod_small];
    try omega; intros; repeat (destruct zeq; try omega).
Qed.


Lemma range_inside_sub_add2:
  forall p n1 n2 r
    (SZ_OK : Int.unsigned n1 + Int.unsigned n2 < Int.half_modulus)
    (RI1 : range_inside (p, n1) r)
    (RI2 : range_inside (Ptr.sub_int p n2, n2) r),
   range_inside (Ptr.sub_int p n2, Int.add n1 n2) r.
Proof.
  unfold range_inside, valid_erange, Punsigned.
  intros [b [p P]] [n1 N1] [n2 N2] [[b' [p' P']] [n' N']] SZ_OK; simpl in *; Zsimps.
  assert (Int.half_modulus + Int.half_modulus = Int.modulus) by done.
  rewrite (Zmod_small (n1 + n2)); [|omega].
  destruct (zlt p n2); 
    [rewrite Zmod_too_small|rewrite Zmod_small]; try omega;
  intros; try omega.
Qed.

Lemma ranges_disjoint_add:
  forall p n n'
    (VE: valid_erange (p, n))
    (LTn': Int.unsigned n' < Int.half_modulus),
    ranges_disjoint (p, n) (Ptr.add p n, n').
Proof.
  intros [b ofs] ? ? [LT LE] ?.
  right.
  unfold Punsigned in LE. destruct zeq.
    left.
    rewrite Int.add_unsigned, e.
    replace (0 + Int.unsigned n) with (Int.unsigned n) by omega.
    rewrite Int.repr_unsigned; omega.
  destruct (Z_le_lt_eq_dec _ _ LE).
    rewrite Int.add_unsigned, Int.unsigned_repr.
    left. omega. 
    pose proof (Int.unsigned_range ofs).
    pose proof (Int.unsigned_range n). 
    unfold Int.max_unsigned; omega.
  right. unfold Int.add; rewrite e.
  replace (Int.unsigned (Int.repr Int.modulus)) with 0 by (by compute).
  replace Int.modulus with (Int.half_modulus + Int.half_modulus) in e by (by compute).
  omega.
Qed.

