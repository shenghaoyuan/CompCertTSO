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

(** * Merge sort over lists *)

Require Import List.
Require Import Permutation.
Require Program.Wf.
Require Omega.

Section SORT.

(** A type equipped with a total, decidable preorder. *)

Variable A: Type.
Variable le: A -> A -> Prop.
Hypothesis le_trans: forall x y z, le x y -> le y z -> le x z.
Hypothesis le_total: forall x y, le x y \/ le y x.
Variable le_dec: forall (x y: A), {le x y} + {~le x y}.

Lemma le_refl: forall x, le x x.
Proof.
  intros. destruct (le_total x x); auto. 
Qed.

Lemma le_not: forall x y, ~le x y -> le y x.
Proof.
  intros. destruct (le_total x y). contradiction. auto.
Qed.

(** What it means for a list to be sorted in increasing order. *)

Inductive Sorted: list A -> Prop :=
  | Sorted_nil:
      Sorted nil
  | Sorted_cons: forall hd tl,
      (forall x, In x tl -> le hd x) ->
      Sorted tl ->
      Sorted (hd :: tl).

(** Lists of 1 element are sorted. *)

Remark Sorted_1:
  forall x, Sorted (x :: nil).
Proof.
  intros. constructor. intros. elim H. constructor. 
Qed.

(** Lists of 2 ordered elements are sorted. *)

Remark Sorted_2:
  forall x y, le x y -> Sorted (x :: y :: nil).
Proof.
  intros. constructor. 
  intros. simpl in H0. destruct H0. subst x0. auto. contradiction.
  apply Sorted_1.
Qed.

(** Two elements are equivalent if they compare [le] in both directions. *)

Definition eqv (x y: A) : bool :=
  if le_dec x y then if le_dec y x then true else false
                else false.

Lemma eqv_spec: forall x y, eqv x y = true <-> le x y /\ le y x.
Proof.
  intros. unfold eqv. 
  destruct (le_dec x y). 
  destruct (le_dec y x). tauto. intuition congruence. 
  intuition congruence.
Qed.

(** Stable permutations.  Two lists are in the [Stable] relation if
  equivalent elements appear in the same order in both lists.
  That is, if the first list is of the form [ ... x ... y ... ]
  with [x] and [y] being equivalent, the other list is also of
  the form [ ... x ... y ... ].  *)

Definition Stable (l l': list A) : Prop :=
  forall x, filter (eqv x) l = filter (eqv x) l'.

Lemma Stable_refl:
  forall l, Stable l l.
Proof.
  intros; red; intros; auto.
Qed.

Lemma Stable_trans:
  forall l1 l2 l3, Stable l1 l2 -> Stable l2 l3 -> Stable l1 l3.
Proof.
  intros; red; intros. transitivity (filter (eqv x) l2); auto.
Qed.

Remark filter_app:
  forall (A: Type) (f: A -> bool) (l l': list A),
  filter f (l ++ l') = filter f l ++ filter f l'.
Proof.
  induction l; intros; simpl. auto. 
  destruct (f a); simpl. f_equal; auto. auto.
Qed. 

Lemma Stable_app:
  forall l l' m m', Stable l l' -> Stable m m' -> Stable (l ++ m) (l' ++ m').
Proof.
  intros; red; intros. repeat rewrite filter_app. f_equal; auto.
Qed.

Lemma Stable_skip:
  forall a l l', Stable l l' -> Stable (a::l) (a::l').
Proof.
  intros; red; intros. simpl. 
  destruct (eqv x a). f_equal; auto. auto.
Qed.

Lemma Stable_swap:
  forall a b l, ~le b a -> Stable (a::b::l) (b::a::l).
Proof.
  intros; red; intros. simpl. 
  case_eq (eqv x a); intro; auto.
  case_eq (eqv x b); intro; auto. 
  rewrite eqv_spec in H0. rewrite eqv_spec in H1. destruct H0; destruct H1.
  elim H. eauto. 
Qed.

Remark filter_empty:
  forall (A: Type) (f: A -> bool) (l: list A),
  (forall x, In x l -> f x = false) ->
  filter f l = nil.
Proof.
  induction l; simpl; intros. 
  auto.
  replace (f a) with false. apply IHl. auto. symmetry. auto. 
Qed.

Lemma Stable_cons_app:
  forall a l l1 l2,
  Stable l (l1 ++ l2) ->
  (forall b, In b l1 -> ~(le a b /\ le b a)) ->
  Stable (a :: l) (l1 ++ a :: l2).
Proof.
  intros; red; intros. rewrite filter_app. simpl.
  generalize (H x). rewrite filter_app.
  case_eq (eqv x a); intro; auto.
  rewrite (filter_empty _ (eqv x) l1). simpl. intro. congruence.
  intros. case_eq (eqv x x0); intro; auto.
  elim (H0 x0); auto.
  rewrite eqv_spec in H1. destruct H1. 
  rewrite eqv_spec in H3. destruct H3. 
  split; eapply le_trans; eauto.
Qed.

Lemma Stable_cons_app':
  forall a b l l1 l2,
  Stable l (b :: l1 ++ l2) ->
  Sorted (b :: l1) -> ~le b a ->
  Stable (a :: l) (b :: l1 ++ a :: l2).
Proof.
  intros. change (Stable (a :: l) ((b :: l1) ++ a :: l2)). 
  apply Stable_cons_app. simpl; auto. 
  intros. simpl in H2. destruct H2. subst b0. tauto. 
  inversion H0; subst. red; intros [P Q]. elim H1. apply le_trans with b0; auto. 
Qed.

Remark filter_sublist:
  forall (A: Type) (f: A -> bool) (x: A) (l l1' l2': list A),
  filter f l = l1' ++ x :: l2' ->
  exists l1, exists l2, l = l1 ++ x :: l2 /\ filter f l1 = l1' /\ filter f l2 = l2'.
Proof.
  induction l; intros until l2'; simpl.
  intro. destruct l1'; simpl in H; discriminate.
  case_eq (f a); intros.
  destruct l1'; simpl in H0; injection H0; clear H0; intros.
  subst x. exists (@nil A0); exists l. auto. 
  subst a0. destruct (IHl _ _ H0) as [l1 [l2 [P [Q R]]]]. subst l. 
  exists (a :: l1); exists l2. 
  split. auto. split. simpl. rewrite H. congruence. auto.
  destruct (IHl _ _ H0) as [l1 [l2 [P [Q R]]]]. subst l. 
  exists (a :: l1); exists l2.
  split. auto. split. simpl. rewrite H. auto. auto.
Qed.

Lemma Stable_decomp:
  forall l l',
  Stable l l' ->
  forall l1 x l2 y l3,
  l = l1 ++ x :: l2 ++ y :: l3 ->
  le x y -> le y x ->
  exists l1', exists l2', exists l3',
  l' = l1' ++ x :: l2' ++ y :: l3'.
Proof.
  intros. 
  generalize (H x). subst l. rewrite filter_app. simpl. 
  rewrite filter_app. simpl.
  assert (eqv x x = true). 
    unfold eqv. 
    destruct (le_dec x x). auto. elim n. apply le_refl.  
  rewrite H0; clear H0.
  assert (eqv x y = true).
    unfold eqv. destruct (le_dec x y); try contradiction. 
    destruct (le_dec y x); try contradiction. auto. 
  rewrite H0; clear H0.
  intro.
  destruct (filter_sublist _ _ _ _ _ _ (sym_equal H0)) as [m1 [m2 [P [Q R]]]].
  destruct (filter_sublist _ _ _ _ _ _ R) as [m3 [m4 [S [T U]]]].
  exists m1; exists m3; exists m4. congruence.
Qed.

(** Merging two sorted lists. *)

Fixpoint merge (l1: list A) : list A -> list A :=
  match l1 with
  | nil => (fun l2 => l2)
  | h1 :: t1 =>
      let fix merge_aux (l2: list A) : list A :=
        match l2 with
        | nil => l1
        | h2 :: t2 =>
           if le_dec h1 h2
           then h1 :: merge t1 l2
           else h2 :: merge_aux t2
        end
      in merge_aux
  end.

Lemma merge_spec:
  forall l1, Sorted l1 ->
  forall l2, Sorted l2 ->
  Sorted (merge l1 l2) /\ Permutation (merge l1 l2) (l1 ++ l2) /\ Stable (merge l1 l2) (l1 ++ l2).
Proof.
  induction 1. 
  intros; simpl. split. auto. split. apply Permutation_refl. apply Stable_refl.
  induction 1; intros; simpl.
  rewrite <- app_nil_end.
  split. constructor; auto. split. apply Permutation_refl. apply Stable_refl.
  destruct (le_dec hd hd0).
(* le hd hd0 *)
  destruct (IHSorted (hd0 :: tl0)) as [P [Q R]]. constructor; auto. 
  split.
  constructor. intros. 
  assert (In x (tl ++ hd0 :: tl0)). eapply Permutation_in; eauto.
  destruct (in_app_or _ _ _ H4). auto. 
  simpl in H5; destruct H5. congruence. apply le_trans with hd0; auto. 
  auto.
  split.
  apply perm_skip; auto.
  apply Stable_skip; auto.
(* ~le hd hd0 *)
  destruct IHSorted0 as [P [Q R]].
  split.
  change (Sorted (hd0 :: merge (hd :: tl) tl0)).
  constructor. intros. 
  assert (In x ((hd :: tl) ++ tl0)). eapply Permutation_in; eauto.
  simpl in H4; destruct H4. subst x. apply le_not; auto. 
  destruct (in_app_or _ _ _ H4). apply le_trans with hd; auto. apply le_not; auto. auto.
  auto. 
  split.
  change (Permutation (hd0 :: merge (hd :: tl) tl0) ((hd :: tl) ++ hd0 :: tl0)).
  apply Permutation_cons_app. auto.
  change (Stable (hd0 :: merge (hd :: tl) tl0) ((hd :: tl) ++ hd0 :: tl0)).
  apply Stable_cons_app'. auto. constructor; auto. auto.
Qed.

(** Flattening a list of lists. *)

Fixpoint flatten (ll: list (list A)): list A :=
  match ll with
  | nil => nil
  | hd :: tl => hd ++ flatten tl
  end.

(** Merging adjacent pairs of lists in a list of sorted lists. *)

Program Fixpoint merge_pairs
    (ll: list (list A))
    (SORTED: forall l, In l ll -> Sorted l)
    {struct ll}:
    { ll' : list(list A) |
      (forall l, In l ll' -> Sorted l)
      /\ Permutation (flatten ll') (flatten ll)
      /\ Stable (flatten ll') (flatten ll)
      /\ length ll' <= length ll
      /\ (length ll >= 2 -> length ll' < length ll) } :=
  match ll with
  | l1 :: l2 :: tl => merge l1 l2 :: merge_pairs tl _
  | _ => ll
  end.
Next Obligation.
  apply SORTED. simpl. auto.
Qed.
Next Obligation.
  assert (Sorted l1). apply SORTED. simpl; auto.
  assert (Sorted l2). apply SORTED. simpl; auto.
  destruct (merge_spec l1 H l2 H0). destruct H2.
  split. intros. destruct H4. congruence. auto. 
  split. rewrite <- app_ass. apply Permutation_app; auto.
  split. rewrite <- app_ass. apply Stable_app; auto.
  split. simpl. omega.
  intros. simpl. omega. 
Defined.
Next Obligation.
  split. auto. split. apply Permutation_refl. split. apply Stable_refl. 
  split. omega.
  intro. 
  destruct ll; simpl in H0. elimtype False; omega. 
  destruct ll; simpl in H0. elimtype False; omega. 
  elim (H l l0 ll). auto.
Qed.

(** Iterating [merge_pairs] until all sorted lists have been merged in one. *)

Program Fixpoint merge_iter (ll: list (list A))
                            (SRT: forall l, In l ll -> Sorted l)
                            {measure (length ll)} : 
                 { l : list A 
                   | Sorted l /\ Permutation l (flatten ll) /\ Stable l (flatten ll) } :=
  match ll with
  | nil => nil
  | l :: nil => l
  | _ => merge_iter (merge_pairs ll _) _
  end.
Next Obligation.
  split. constructor. split. apply perm_nil. apply Stable_refl. 
Qed.
Next Obligation.
  split. simpl in SRT. auto. 
  rewrite <- app_nil_end. split. apply Permutation_refl. apply Stable_refl.
Qed.
Next Obligation.
  destruct (merge_pairs ll (merge_iter_func_obligation_3 ll SRT merge_iter ll (conj n n0) (eq_refl ll)))
  as [mll [P [Q [R [S T]]]]]. auto. 
Qed.
Next Obligation.
  destruct (merge_pairs ll (merge_iter_func_obligation_3 ll SRT merge_iter ll (conj n n0) (eq_refl ll)))
  as [mll [P [Q [R [S T]]]]]. simpl.
  apply T. destruct ll. congruence.
  destruct ll. elim (n l). auto.
  simpl; omega.
Qed.
Next Obligation.
  destruct (merge_iter
           (proj1_sig
              (merge_pairs ll
                 (merge_iter_func_obligation_3 ll SRT merge_iter ll
                    (conj n n0) (eq_refl ll))))
           (merge_iter_func_obligation_4 ll SRT merge_iter ll 
              (conj n n0) (eq_refl ll))
           (merge_iter_func_obligation_5 ll SRT merge_iter ll 
              (conj n n0) (eq_refl ll))) as [mll (S & P & ST)].
  simpl in *.   
  split. auto.
  destruct (merge_pairs ll (merge_iter_func_obligation_3 ll SRT merge_iter ll (conj n n0) (eq_refl ll)))
    as [mll' [P' [Q' [R' [S' T']]]]]. simpl in *.
  split. eapply Permutation_trans; eauto.  
  eapply Stable_trans; eauto.
Qed.
Next Obligation.
  split; intros. congruence. congruence.
Qed.

(** Cutting a list into a list of sorted lists. *)

Program Fixpoint presort (l: list A) :
   { l': list (list A) | 
       (forall x, In x l' -> Sorted x) /\ Permutation (flatten l') l /\ Stable (flatten l') l} :=
  match l with
  | nil => nil
  | x :: nil => (x :: nil) :: nil
  | x :: y :: tl =>
      (if le_dec x y then x :: y :: nil else y :: x :: nil)
      :: presort tl
  end.
Next Obligation.
  split. tauto. split. constructor. apply Stable_refl.
Qed.
Next Obligation.
  split. intros. destruct H. subst x0. constructor. intros. elim H. constructor.
  contradiction.
  split. apply Permutation_refl. apply Stable_refl.
Qed.
Next Obligation.
  split.
  intros. destruct H. 
  destruct (le_dec x y); subst; apply Sorted_2; auto.
  apply le_not; auto. auto.
  destruct (le_dec x y); simpl.
  split.
  apply perm_skip. apply perm_skip. auto.
  apply Stable_skip. apply Stable_skip. auto. 
  split.
  eapply perm_trans. apply perm_swap.  apply perm_skip. apply perm_skip. auto.
  eapply Stable_trans. apply Stable_swap. auto.  apply Stable_skip. apply Stable_skip. auto. 
Defined.

(** The sorting function. *)

Program Definition mergesort (l: list A):
    { l' : list A | Sorted l' /\ Permutation l' l /\ Stable l' l } :=
  merge_iter (presort l) _.
Next Obligation.
  destruct (presort l) as [l' [P Q]]. simpl in H. auto.
Qed.
Next Obligation.
  case ((merge_iter (proj1_sig (presort l)) (mergesort_obligation_1 l))).
  intros res. simpl. 
  case (presort l). simpl.
  intros l' [P [Q R]] [S [T U]]. 
  split. auto. split. eapply Permutation_trans; eauto. eapply Stable_trans; eauto. 
Qed.

(** A property of permutations that is missing from the List library:
  a permutation of a list without duplicates is a list without duplicates. *)

Lemma Permutation_NoDup:
  forall (l l': list A), Permutation l l' -> NoDup l -> NoDup l'.
Proof.
  induction 1; intros.
  constructor.

  inversion H0; subst. constructor; auto.
  red; intro; elim H3. apply Permutation_in with l'; auto. apply Permutation_sym; auto.

  inversion H; subst. inversion H3; subst. 
  constructor. simpl. simpl in H2. intuition.
  constructor. simpl in H2. intuition. auto.

  auto.
Qed.

End SORT.
