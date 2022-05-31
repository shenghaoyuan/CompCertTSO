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

(** This file collects a number of definitions and theorems that are
    used throughout the development.  It complements the Coq standard
    library. *)

Require Export ZArith.
Require Export Znumtheory.
Require Export List.
Require Export Bool.
Require Import Wf_nat.
Require Export Vlib.

(* moved from Floats.v to avoid a circular build - maybe move elsewhere *)

Inductive float_cmp_result := FCunordered | FCless | FCequal | FCgreater.

(** * Logical axioms *)

(** We use two logical axioms that are not provable in Coq but consistent
  with the logic: function extensionality and proof irrelevance.
  These are used in the memory model to show that two memory states
  that have identical contents are equal. *)

Axiom extensionality:
  forall (A B: Type) (f g : A -> B),
  (forall x, f x = g x) -> f = g.

Axiom proof_irrelevance:
  forall (P: Prop) (p1 p2: P), p1 = p2.

(** * Useful tactics *)

Ltac inv H := inversion H; clear H; subst.

Ltac predSpec pred predspec x y :=
  generalize (predspec x y); case (pred x y); intro.

Ltac caseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

Ltac destructEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; 
  destruct name; intro.

Ltac decEq :=
  match goal with
  | [ |- _ = _ ] => f_equal
  | [ |- (?X ?A <> ?X ?B) ] =>
      cut (A <> B); [intro; congruence | try discriminate]
  end.

Ltac byContradiction :=
  cut False; [contradiction|idtac].

Ltac omegaContradiction :=
  cut False; [contradiction|omega].

Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. auto. Qed.

Ltac exploit x :=
    refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _) _)
 || refine (modusponens _ _ (x _ _) _)
 || refine (modusponens _ _ (x _) _).

(** * Definitions and theorems over the type [positive] *)

Lemma Zplus_minus_l: forall a b, a - b + b = a.
Proof. by intros; rewrite Zplus_comm, Zplus_minus. Qed.

Lemma Zplus_minus_zero: forall a b, a + (0 - b) = a - b.
Proof. intros; omega. Qed.

Lemma Zminus_minus_zero: forall a b, a - (0 - b) = a + b.
Proof. intros; omega. Qed.


Definition peq (x y: positive): {x = y} + {x <> y}.
Proof.
  intros; caseEq (Pcompare x y Eq).
  by left; apply Pcompare_Eq_eq. 
  by right; intro; subst y; rewrite (Pcompare_refl x) in *. 
  by right; intro; subst y; rewrite (Pcompare_refl x) in *.
Qed.

Lemma peq_true:
  forall (A: Type) (x: positive) (a b: A), (if peq x x then a else b) = a.
Proof.
  by intros; case (peq x x).
Qed.

Lemma peq_false:
  forall (A: Type) (x y: positive) (a b: A), x <> y -> (if peq x y then a else b) = b.
Proof.
  by intros; case (peq x y).
Qed.

Definition Plt (x y: positive): Prop := Zlt (Zpos x) (Zpos y).

Lemma Plt_ne:
  forall (x y: positive), Plt x y -> x <> y.
Proof.
  unfold Plt; intros; intro; subst y; omega.
Qed.
Hint Resolve Plt_ne: coqlib.

Lemma Plt_trans:
  forall (x y z: positive), Plt x y -> Plt y z -> Plt x z.
Proof.
  unfold Plt; intros; omega.
Qed.


Remark Psucc_Zsucc:
  forall (x: positive), Zpos (Psucc x) = Zsucc (Zpos x).
Proof.
  by intros; rewrite Pplus_one_succ_r. 
Qed.

Lemma Plt_succ:
  forall (x: positive), Plt x (Psucc x).
Proof.
  intros; unfold Plt; rewrite Psucc_Zsucc; omega.
Qed.
Hint Resolve Plt_succ: coqlib.

Lemma Plt_trans_succ:
  forall (x y: positive), Plt x y -> Plt x (Psucc y).
Proof.
  by intros; eapply Plt_trans, Plt_succ.
Qed.
Hint Resolve Plt_succ: coqlib.

Lemma Plt_succ_inv:
  forall (x y: positive), Plt x (Psucc y) -> Plt x y \/ x = y.
Proof.
  unfold Plt; intros; rewrite Psucc_Zsucc in *.
  assert (A: (Zpos x < Zpos y)%Z \/ Zpos x = Zpos y) by omega.
  elim A; [left | right]; clarify.
Qed.

Definition plt (x y: positive) : {Plt x y} + {~ Plt x y}.
Proof.
 by intros; apply Z_lt_dec.
Qed.

Definition Ple (p q: positive) := Zle (Zpos p) (Zpos q).

Lemma Ple_refl: forall (p: positive), Ple p p.
Proof.
  unfold Ple; intros; omega.
Qed.

Lemma Ple_trans: forall (p q r: positive), Ple p q -> Ple q r -> Ple p r.
Proof.
  unfold Ple; intros; omega.
Qed.

Lemma Ple_total: forall (p q : positive), Ple p q \/ Ple q p.
Proof.
  unfold Ple; intros; omega.
Qed.

Lemma Plt_Ple: forall (p q: positive), Plt p q -> Ple p q.
Proof.
  unfold Plt, Ple; intros; omega.
Qed.

Definition ple (x y: positive) : {Ple x y} + {~ Ple x y}.
Proof.
 intros; apply Z_le_dec.
Qed.

Lemma Ple_succ: forall (p: positive), Ple p (Psucc p).
Proof.
  intros; apply Plt_Ple, Plt_succ.
Qed.

Lemma Plt_Ple_trans:
  forall (p q r: positive), Plt p q -> Ple q r -> Plt p r.
Proof.
  unfold Plt, Ple; intros; omega.
Qed.

Lemma Plt_strict: forall p, ~ Plt p p.
Proof.
  unfold Plt; intros; omega.
Qed.

Hint Resolve Ple_refl Plt_Ple Ple_succ Plt_strict: coqlib.

(** Peano recursion over positive numbers. *)

Section POSITIVE_ITERATION.

Lemma Plt_wf: well_founded Plt.
Proof.
  apply well_founded_lt_compat with nat_of_P.
  by intros; apply nat_of_P_lt_Lt_compare_morphism.
Qed.

Variable A: Type.
Variable v1: A.
Variable f: positive -> A -> A.

Lemma Ppred_Plt:
  forall x, x <> xH -> Plt (Ppred x) x.
Proof.
  intros; elim (Psucc_pred x); intro X; try done.
  set (y := Ppred x) in *; rewrite <- X; apply Plt_succ.
Qed.

Let iter (x: positive) (P: forall y, Plt y x -> A) : A :=
  match peq x xH with
  | left EQ => v1
  | right NOTEQ => f (Ppred x) (P (Ppred x) (Ppred_Plt x NOTEQ))
  end.

Definition positive_rec : positive -> A :=
  Fix Plt_wf (fun _ => A) iter.

Lemma unroll_positive_rec:
  forall x,
  positive_rec x = iter x (fun y _ => positive_rec y).
Proof.
  unfold positive_rec. apply (Fix_eq Plt_wf (fun _ => A) iter).
  intros. unfold iter. case (peq x 1); intro. auto. decEq. apply H.
Qed.

Lemma positive_rec_base:
  positive_rec 1%positive = v1.
Proof.
  rewrite unroll_positive_rec. unfold iter. case (peq 1 1); intro.
  auto. elim n; auto.
Qed.

Lemma positive_rec_succ:
  forall x, positive_rec (Psucc x) = f x (positive_rec x).
Proof.
  intro. rewrite unroll_positive_rec. unfold iter.
  case (peq (Psucc x) 1); intro.
  destruct x; simpl in e; discriminate.
  rewrite Ppred_succ. auto.
Qed.

Lemma positive_Peano_ind:
  forall (P: positive -> Prop),
  P xH ->
  (forall x, P x -> P (Psucc x)) ->
  forall x, P x.
Proof.
  intros.
  apply (well_founded_ind Plt_wf P).
  intros. 
  case (peq x0 xH); intro.
  subst x0; auto.
  elim (Psucc_pred x0); intro. contradiction. rewrite <- H2.
  apply H0. apply H1. apply Ppred_Plt. auto. 
Qed.

End POSITIVE_ITERATION.

(** * Definitions and theorems over the type [Z] *)

Definition zeq: forall (x y: Z), {x = y} + {x <> y} := Z_eq_dec.

Lemma zeq_true:
  forall (A: Type) (x: Z) (a b: A), (if zeq x x then a else b) = a.
Proof. by intros; case zeq. Qed.

Lemma zeq_false:
  forall (A: Type) (x y: Z) (a b: A), x <> y -> (if zeq x y then a else b) = b.
Proof. by intros; case zeq. Qed.

Open Scope Z_scope.

Definition zlt: forall (x y: Z), {x < y} + {x >= y} := Z_lt_ge_dec.

Lemma zlt_true:
  forall (A: Type) (x y: Z) (a b: A), 
  x < y -> (if zlt x y then a else b) = a.
Proof. by intros; case zlt. Qed.

Lemma zlt_false:
  forall (A: Type) (x y: Z) (a b: A), 
  x >= y -> (if zlt x y then a else b) = b.
Proof. by intros; case zlt. Qed.

Definition zle: forall (x y: Z), {x <= y} + {x > y} := Z_le_gt_dec.

Lemma zle_true:
  forall (A: Type) (x y: Z) (a b: A), 
  x <= y -> (if zle x y then a else b) = a.
Proof. by intros; case zle. Qed.

Lemma zle_false:
  forall (A: Type) (x y: Z) (a b: A), 
  x > y -> (if zle x y then a else b) = b.
Proof. by intros; case zle. Qed.

(** Properties of powers of two. *)

Lemma two_power_nat_O : two_power_nat O = 1.
Proof. done. Qed.

Lemma two_power_nat_pos : forall n : nat, two_power_nat n > 0.
Proof.
  induction n; rewrite ?two_power_nat_O, ?two_power_nat_S; omega.
Qed.

Lemma two_p_monotone:
  forall x y, 0 <= x <= y -> two_p x <= two_p y.
Proof.
  intros.
  replace (two_p x) with (two_p x * 1) by omega. 
  replace y with (x + (y - x)) by omega.
  rewrite two_p_is_exp; try omega.
  apply Zmult_le_compat_l.
  assert (two_p (y - x) > 0); [apply two_p_gt_ZERO|]; omega.
  assert (two_p x > 0); [apply two_p_gt_ZERO|]; omega.
Qed.

Lemma two_power_nat_two_p:
  forall x, two_power_nat x = two_p (Z_of_nat x).
Proof.
  induction x; try done. 
  rewrite two_power_nat_S, inj_S, two_p_S; omega.
Qed.

Lemma two_p_monotone_strict:
  forall x y, 0 <= x < y -> two_p x < two_p y.
Proof.
  intros. assert (two_p x <= two_p (y - 1)). apply two_p_monotone; omega.
  assert (two_p (y - 1) > 0). apply two_p_gt_ZERO. omega.
  replace y with (Zsucc (y - 1)) by omega. rewrite two_p_S. omega. omega.
Qed.

Lemma two_p_strict:
  forall x, x >= 0 -> x < two_p x.
Proof.
  intros x0 GT. pattern x0. apply natlike_ind.
  simpl. omega.
  intros. rewrite two_p_S; auto. generalize (two_p_gt_ZERO x H). omega. 
  omega.
Qed.

Lemma two_p_strict_2:
  forall x, x >= 0 -> 2 * x - 1 < two_p x.
Proof.
  intros. assert (x = 0 \/ x - 1 >= 0) by omega. destruct H0.
  subst. vm_compute. auto.
  replace (two_p x) with (2 * two_p (x - 1)).
  generalize (two_p_strict _ H0). omega. 
  rewrite <- two_p_S. decEq. omega. omega.
Qed.

(** Properties of [Zmin] and [Zmax] *)

Lemma Zmin_spec:
  forall x y, Zmin x y = if zlt x y then x else y.
Proof.
  intros; unfold Zlt, Zge, Zmin; destruct zlt.
    by rewrite z.
  caseEq (x ?= y); try done. 
  by apply Zcompare_Eq_eq.
Qed.

Lemma Zmax_spec:
  forall x y, Zmax x y = if zlt y x then x else y.
Proof.
  intros; unfold Zlt, Zge, Zmax; intros.
  rewrite <- (Zcompare_antisym y x).
  destruct zlt; caseEq (y ?= x); rewrite ?z; try done.
  by symmetry; apply Zcompare_Eq_eq.  
Qed.

Lemma Zmax_bound_l:
  forall x y z, x <= y -> x <= Zmax y z.
Proof.
  intros; generalize (Zmax1 y z); omega.
Qed.

Lemma Zmax_bound_r:
  forall x y z, x <= z -> x <= Zmax y z.
Proof.
  intros; generalize (Zmax2 y z); omega.
Qed.

(** Properties of Euclidean division and modulus. *)

Lemma Zdiv_small:
  forall x y, 0 <= x < y -> x / y = 0.
Proof.
  intros. assert (y > 0) by omega. 
  assert (X: forall a b,
    0 <= a < y ->
    0 <= y * b + a < y ->
    b = 0).
    intros. 
    (assert (b = 0 \/ b > 0 \/ -b > 0) as [|[|]] by omega); try done.
      assert (y * b >= y * 1); [apply Zmult_ge_compat_l|]; omega. 
    assert (y * (-b) >= y * 1) by (apply Zmult_ge_compat_l; omega). 
    by rewrite <- Zopp_mult_distr_r in *; omegaContradiction.
  by eapply X; [apply Z_mod_lt | rewrite <- Z_div_mod_eq]. 
Qed.

Lemma Zmod_small:
  forall x y, 0 <= x < y -> x mod y = x.
Proof.
  intros; generalize (Z_div_mod_eq x y); 
    rewrite (Zdiv_small x y); omega.
Qed.

Lemma Zmod_neg_range: 
  forall n m (H: 0 < n <= m), ((0 - n) mod m) = m - n.
Proof. 
  intros; rewrite <- (Z_mod_same m), Zminus_mod_idemp_l, Zmod_small; omega.
Qed.

Lemma Zplus_mod_same: forall a n : Z, (a + n) mod n = a mod n.
Proof.
  by intros; rewrite Zplus_mod, Z_mod_same_full, Zplus_0_r, Zmod_mod.
Qed.

Lemma Zmod_too_small:
  forall a n, -n <= a < 0 -> a mod n = n + a.
Proof.
  intros; rewrite <- Zplus_mod_same, Zmod_small; omega.
Qed.

Lemma Zmod_too_big:
  forall a n, n <= a < n + n -> a mod n = a - n.
Proof.
  intros; rewrite <- (Zminus_0_r a) at 1;
  rewrite <- (Z_mod_same_full n), Zminus_mod_idemp_r, Zmod_small; omega.
Qed.

Lemma Zmod_unique:
  forall x y a b,
  x = a * y + b -> 0 <= b < y -> x mod y = b.
Proof.
  intros; clarify; rewrite Zplus_comm, Z_mod_plus; [|omega].
  by apply Zmod_small.
Qed.

Lemma Zdiv_unique:
  forall x y a b,
  x = a * y + b -> 0 <= b < y -> x / y = a.
Proof.
  intros; clarify.
  rewrite Zplus_comm, Z_div_plus, (Zdiv_small b y); omega.
Qed.

Lemma Zdiv_Zdiv:
  forall a b c (bPOS: b > 0) (cPOS: c > 0),
  (a / b) / c = a / (b * c).
Proof.
  intros.
  generalize (Z_div_mod_eq a b bPOS), (Z_mod_lt a b bPOS).
  generalize (a / b), (a mod b); intros q1 r1 -> ?.
  generalize (Z_div_mod_eq q1 c cPOS), (Z_mod_lt q1 c cPOS).
  generalize (q1 / c), (q1 mod c); intros q2 r2 -> ?.
  symmetry; apply Zdiv_unique with (r2 * b + r1); [ring|].
  split.
    assert (0 <= r2 * b); [apply Zmult_le_0_compat|]; omega.
  assert (X: (r2 + 1) * b <= c * b) by (apply Zmult_le_compat_r; omega). 
  replace ((r2 + 1) * b) with (r2 * b + b) in X by ring.
  replace (c * b) with (b * c) in X by ring.
  omega.
Qed.

Lemma Zmult_le_compat_l_neg :
  forall n m p:Z, n >= m -> p <= 0 -> p * n <= p * m.
Proof.
  intros.
  assert ((-p) * n >= (-p) * m). apply Zmult_ge_compat_l. auto. omega.
  replace (p * n) with (- ((-p) * n)) by ring.
  replace (p * m) with (- ((-p) * m)) by ring.
  omega.
Qed.

Lemma Zdiv_interval_1:
  forall lo hi a b,
  lo <= 0 -> hi > 0 -> b > 0 ->
  lo * b <= a < hi * b ->
  lo <= a/b < hi.
Proof.
  intros. 
  generalize (Z_div_mod_eq a b H1). generalize (Z_mod_lt a b H1). intros.
  set (q := a/b) in *. set (r := a mod b) in *.
  split.
  assert (lo < (q + 1)).
  apply Zmult_lt_reg_r with b. omega.  
  apply Zle_lt_trans with a. omega. 
  replace ((q + 1) * b) with (b * q + b) by ring.
  omega.
  omega.
  apply Zmult_lt_reg_r with b. omega. 
  replace (q * b) with (b * q) by ring.
  omega.
Qed.

Lemma Zdiv_interval_2:
  forall lo hi a b,
  lo <= a <= hi -> lo <= 0 -> hi >= 0 -> b > 0 ->
  lo <= a/b <= hi.
Proof.
  intros.
  assert (lo <= a / b < hi+1).
  apply Zdiv_interval_1. omega. omega. auto.
  assert (lo * b <= lo * 1). apply Zmult_le_compat_l_neg. omega. omega. 
  replace (lo * 1) with lo in H3 by ring.
  assert ((hi + 1) * 1 <= (hi + 1) * b). apply Zmult_le_compat_l. omega. omega.
  replace ((hi + 1) * 1) with (hi + 1) in H4 by ring.
  omega.
  omega.
Qed.

(** Simplification tactic for operations on Z. *)

Ltac Zsimps := 
  repeat rewrite ?Zplus_minus, ?Zplus_minus_l, ?Zplus_0_l, ?Zplus_0_r, ?Zminus_0_r, 
    ?Zplus_minus_zero, ?Zminus_minus_zero, ?Zminus_diag,
    ?Z_mod_same_full, ?Zmod_0_l, ?Zmod_mod, ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r,
    ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r in *.

(** Properties of divisibility. *)

Lemma Zdivides_trans:
  forall x y z, (x | y) -> (y | z) -> (x | z).
Proof.
  intros. inv H. inv H0. exists (q0 * q). ring.
Qed.

Definition Zdivide_dec:
  forall (p q: Z), p > 0 -> { (p|q) } + { ~(p|q) }.
Proof.
  intros. destruct (zeq (Zmod q p) 0).
  left. exists (q / p). 
  transitivity (p * (q / p) + (q mod p)). apply Z_div_mod_eq; auto.
  transitivity (p * (q / p)). omega. ring.
  right; red; intros. elim n. apply Z_div_exact_1; auto. 
  inv H0. rewrite Z_div_mult; auto. ring.
Qed.

(** Conversion from [Z] to [nat]. *)

Definition nat_of_Z (z: Z) : nat :=
  match z with
  | Z0 => O
  | Zpos p => nat_of_P p
  | Zneg p => O
  end.

Lemma nat_of_Z_max:
  forall z, Z_of_nat (nat_of_Z z) = Zmax z 0.
Proof.
  intros. unfold Zmax. destruct z; simpl; auto.
  symmetry. apply Zpos_eq_Z_of_nat_o_nat_of_P.
Qed.

Lemma nat_of_Z_eq:
  forall z, z >= 0 -> Z_of_nat (nat_of_Z z) = z.
Proof.
  intros. rewrite nat_of_Z_max. apply Zmax_left. auto.
Qed.

Lemma nat_of_Z_neg:
  forall n, n <= 0 -> nat_of_Z n = O.
Proof.
  destruct n; unfold Zle; simpl; auto. congruence.
Qed.

Lemma nat_of_Z_plus:
  forall p q,
  p >= 0 -> q >= 0 ->
  nat_of_Z (p + q) = (nat_of_Z p + nat_of_Z q)%nat.
Proof.
  intros. 
  apply inj_eq_rev. rewrite inj_plus.
  repeat rewrite nat_of_Z_eq; auto. omega.
Qed.

(** Alignment: [align n amount] returns the smallest multiple of [amount]
  greater than or equal to [n]. *)

Definition align (n: Z) (amount: Z) :=
  ((n + amount - 1) / amount) * amount.

Lemma align_le: forall x y, y > 0 -> x <= align x y.
Proof.
  intros. unfold align. 
  generalize (Z_div_mod_eq (x + y - 1) y H). intro.
  replace ((x + y - 1) / y * y) 
     with ((x + y - 1) - (x + y - 1) mod y).
  generalize (Z_mod_lt (x + y - 1) y H). omega.
  rewrite Zmult_comm. omega.
Qed.

Lemma align_divides: forall x y, y > 0 -> (y | align x y).
Proof.
  intros. unfold align. apply Zdivide_factor_l. 
Qed.

(** * Definitions and theorems on the data types [option], [sum] and [list] *)

Set Implicit Arguments.

(** Mapping a function over an option type. *)

Definition option_map (A B: Type) (f: A -> B) (x: option A) : option B :=
  match x with
  | None => None
  | Some y => Some (f y)
  end.

Definition optbind (A B : Type) (g : A -> option B) (f : option A) : option B :=
  match f with
    | None => None
    | Some v => g v
  end.

Lemma optbind_someD:
  forall {A B} {f: A -> option B} {x v} (H: optbind f x = Some v),
  exists v', x = Some v' /\ f v' = Some v.
Proof.
  by intros; destruct x; [eexists|].
Qed.

(** Mapping a function over a sum type. *)

Definition sum_left_map (A B C: Type) (f: A -> B) (x: A + C) : B + C :=
  match x with
  | inl y => inl C (f y)
  | inr z => inr B z
  end.

(** Properties of [List.nth] (n-th element of a list). *)

Hint Resolve in_eq in_cons: coqlib.

Lemma nth_error_in:
  forall (A: Type) (n: nat) (l: list A) (x: A),
  List.nth_error l n = Some x -> In x l.
Proof.
  induction n; simpl.
   destruct l; intros.
    discriminate.
    injection H; intro; subst a. apply in_eq.
   destruct l; intros.
    discriminate.
    apply in_cons. auto.
Qed.
Hint Resolve nth_error_in: coqlib.

Lemma nth_error_nil:
  forall (A: Type) (idx: nat), nth_error (@nil A) idx = None.
Proof.
  induction idx; simpl; intros; reflexivity.
Qed.
Hint Resolve nth_error_nil: coqlib.

(** Properties of [List.incl] (list inclusion). *)

Lemma incl_cons_inv:
  forall (A: Type) (a: A) (b c: list A),
  incl (a :: b) c -> incl b c.
Proof.
  unfold incl; intros. apply H. apply in_cons. auto.
Qed.
Hint Resolve incl_cons_inv: coqlib.

Lemma incl_app_inv_l:
  forall (A: Type) (l1 l2 m: list A),
  incl (l1 ++ l2) m -> incl l1 m.
Proof.
  unfold incl; intros. apply H. apply in_or_app. left; assumption.
Qed.

Lemma incl_app_inv_r:
  forall (A: Type) (l1 l2 m: list A),
  incl (l1 ++ l2) m -> incl l2 m.
Proof.
  unfold incl; intros. apply H. apply in_or_app. right; assumption.
Qed.

Hint Resolve  incl_tl incl_refl incl_app_inv_l incl_app_inv_r: coqlib.

Lemma incl_same_head:
  forall (A: Type) (x: A) (l1 l2: list A),
  incl l1 l2 -> incl (x::l1) (x::l2).
Proof.
  intros; red; simpl; intros. intuition. 
Qed.

(** Properties of [List.map] (mapping a function over a list). *)

Lemma list_map_exten:
  forall (A B: Type) (f f': A -> B) (l: list A),
  (forall x, In x l -> f x = f' x) ->
  List.map f' l = List.map f l.
Proof.
  induction l; simpl; intros; try done.
  rewrite <- H, IHl; auto. 
Qed.

Lemma list_map_compose:
  forall (A B C: Type) (f: A -> B) (g: B -> C) (l: list A),
  List.map g (List.map f l) = List.map (fun x => g(f x)) l.
Proof.
  by induction l; simpl; [|rewrite IHl].
Qed.

Lemma list_map_identity:
  forall (A: Type) (l: list A),
  List.map (fun (x:A) => x) l = l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma list_map_nth:
  forall (A B: Type) (f: A -> B) (l: list A) (n: nat),
  nth_error (List.map f l) n = option_map f (nth_error l n).
Proof.
  induction l; simpl; intros.
  repeat rewrite nth_error_nil. reflexivity.
  destruct n; simpl. reflexivity. auto.
Qed.

Lemma list_length_map:
  forall (A B: Type) (f: A -> B) (l: list A),
  List.length (List.map f l) = List.length l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma list_in_map_inv:
  forall (A B: Type) (f: A -> B) (l: list A) (y: B),
  In y (List.map f l) -> exists x:A, y = f x /\ In x l.
Proof.
  induction l; simpl; intros.
  contradiction.
  elim H; intro. 
  exists a; intuition auto.
  generalize (IHl y H0). intros [x [EQ IN]]. 
  exists x; tauto.
Qed.

Lemma list_append_map:
  forall (A B: Type) (f: A -> B) (l1 l2: list A),
  List.map f (l1 ++ l2) = List.map f l1 ++ List.map f l2.
Proof.
  by induction l1; simpl; intros; [|rewrite IHl1].
Qed.

(** Properties of list membership. *)

Lemma in_cns:
  forall (A: Type) (x y: A) (l: list A), 
    In x (y :: l) <-> y = x \/ In x l.
Proof.
  intros; simpl; tauto.
Qed.

Lemma in_app:
  forall (A: Type) (x: A) (l1 l2: list A), 
    In x (l1 ++ l2) <-> In x l1 \/ In x l2.
Proof.
  intros. split; intro. apply in_app_or. auto. apply in_or_app. auto.
Qed.

Lemma list_in_insert:
  forall (A: Type) (x: A) (l1 l2: list A) (y: A),
  In x (l1 ++ l2) -> In x (l1 ++ y :: l2).
Proof.
  intros. apply in_or_app; simpl. elim (in_app_or _ _ _ H); intro; auto.
Qed.

(** [list_disjoint l1 l2] holds iff [l1] and [l2] have no elements 
  in common. *)

Definition list_disjoint (A: Type) (l1 l2: list A) : Prop :=
  forall (x y: A), In x l1 -> In y l2 -> x <> y.

Lemma list_disjoint_cons_left:
  forall (A: Type) (a: A) (l1 l2: list A),
  list_disjoint (a :: l1) l2 -> list_disjoint l1 l2.
Proof.
  unfold list_disjoint; simpl; intros. apply H; tauto. 
Qed.

Lemma list_disjoint_cons_right:
  forall (A: Type) (a: A) (l1 l2: list A),
  list_disjoint l1 (a :: l2) -> list_disjoint l1 l2.
Proof.
  unfold list_disjoint; simpl; intros. apply H; tauto. 
Qed.

Lemma list_disjoint_notin:
  forall (A: Type) (l1 l2: list A) (a: A),
  list_disjoint l1 l2 -> In a l1 -> ~(In a l2).
Proof.
  unfold list_disjoint; intros; red; intros. 
  apply H with a a; auto.
Qed.

Lemma list_disjoint_sym:
  forall (A: Type) (l1 l2: list A),
  list_disjoint l1 l2 -> list_disjoint l2 l1.
Proof.
  unfold list_disjoint; intros. 
  apply sym_not_equal. apply H; auto.
Qed.

Lemma list_disjoint_dec:
  forall (A: Type) (eqA_dec: forall (x y: A), {x=y} + {x<>y}) (l1 l2: list A),
  {list_disjoint l1 l2} + {~list_disjoint l1 l2}.
Proof.
  induction l1; intros.
  left; red; intros. elim H.
  case (In_dec eqA_dec a l2); intro.
  right; red; intro. apply (H a a); auto with coqlib. 
  case (IHl1 l2); intro.
  left; red; intros. elim H; intro. 
    red; intro; subst a y. contradiction.
    apply l; auto.
  right; red; intros. elim n0. eapply list_disjoint_cons_left; eauto.
Qed.

(** [list_equiv l1 l2] holds iff the lists [l1] and [l2] contain the same
    elements. *)

Definition list_equiv (A : Type) (l1 l2: list A) : Prop :=
  forall x, In x l1 <-> In x l2.

Lemma list_equiv_refl:
  forall {A} (l: list A), list_equiv l l.
Proof. done. Qed.

Lemma list_equiv_sym:
  forall {A} {l1 l2: list A} (H: list_equiv l1 l2), list_equiv l2 l1.
Proof. by intros; intro; apply iff_sym, H. Qed.

Lemma list_equiv_trans:
  forall {A} {x y z: list A} (X: list_equiv x y) (Y: list_equiv y z),
    list_equiv x z.
Proof. by intros; intro; eapply iff_trans; [apply X| apply Y]. Qed.

Lemma nodup_dec:
  forall (A: Type) (eqA_dec: forall (x y: A), {x=y} + {x<>y}) (l: list A),
  {NoDup l} + {~NoDup l}.
Proof.
  induction l.
  left; constructor.
  destruct IHl. 
  case (In_dec eqA_dec a l); intro.
  right. red; intro. inversion H. contradiction. 
  left. constructor; auto.
  right. red; intro. inversion H. contradiction.
Qed.

Lemma list_map_norepet:
  forall (A B: Type) (f: A -> B) (l: list A),
  NoDup l ->
  (forall x y, In x l -> In y l -> x <> y -> f x <> f y) ->
  NoDup (List.map f l).
Proof.
  induction 1; simpl; intros.
  constructor.
  constructor.
  red; intro. generalize (list_in_map_inv f _ _ H2).
  intros [z [EQ IN]]. generalize EQ. change (f x <> f z).
  apply H1. tauto. tauto. 
  red; intro; subst x. contradiction.
  apply IHNoDup. intros. apply H1. tauto. tauto. auto.
Qed.

Remark nodup_append_commut:
  forall (A: Type) (a b: list A),
  NoDup (a ++ b) -> NoDup (b ++ a).
Proof.
  intro A.
  assert (forall (x: A) (b: list A) (a: list A), 
           NoDup (a ++ b) -> ~(In x a) -> ~(In x b) -> 
           NoDup (a ++ x :: b)).
    induction a; simpl; intros.
    constructor; auto.
    inversion H. constructor. red; intro.
    elim (in_app_or _ _ _ H6); intro.
    elim H4. apply in_or_app. tauto.
    elim H7; intro. subst a. elim H0. left. auto. 
    elim H4. apply in_or_app. tauto.
    auto.
  induction a; simpl; intros.
  rewrite <- app_nil_end. auto.
  inversion H0. apply H. auto. 
  red; intro; elim H3. apply in_or_app. tauto.
  red; intro; elim H3. apply in_or_app. tauto.
Qed.

Lemma nodup_app:
  forall (A: Type) (l1 l2: list A),
  NoDup (l1 ++ l2) <->
  NoDup l1 /\ NoDup l2 /\ list_disjoint l1 l2.
Proof.
  induction l1; simpl; intros; split; intros.
  intuition. constructor. red;simpl;auto.
  tauto.
  inversion H; subst. rewrite IHl1 in H3. rewrite in_app in H2.
  intuition.
  constructor; auto. red; intros. elim H2; intro. congruence. auto. 
  destruct H as [B [C D]]. inversion B; subst. 
  constructor. rewrite in_app. intuition. elim (D a a); auto. apply in_eq. 
  rewrite IHl1. intuition. red; intros. apply D; auto. apply in_cons; auto. 
Qed.

Lemma nodup_append:
  forall (A: Type) (l1 l2: list A),
  NoDup l1 -> NoDup l2 -> list_disjoint l1 l2 ->
  NoDup (l1 ++ l2).
Proof.
  generalize nodup_app; firstorder.
Qed.

Lemma nodup_append_right:
  forall (A: Type) (l1 l2: list A),
  NoDup (l1 ++ l2) -> NoDup l2.
Proof.
  generalize nodup_app; firstorder.
Qed.

Lemma nodup_append_left:
  forall (A: Type) (l1 l2: list A),
  NoDup (l1 ++ l2) -> NoDup l1.
Proof.
  generalize nodup_app; firstorder.
Qed.

(** [is_tail l1 l2] holds iff [l2] is of the form [l ++ l1] for some [l]. *)

Inductive is_tail (A: Type): list A -> list A -> Prop :=
  | is_tail_refl:
      forall c, is_tail c c
  | is_tail_cons:
      forall i c1 c2, is_tail c1 c2 -> is_tail c1 (i :: c2).

Lemma is_tail_in:
  forall (A: Type) (i: A) c1 c2, is_tail (i :: c1) c2 -> In i c2.
Proof.
  induction c2; simpl; intros.
  inversion H.
  inversion H. tauto. right; auto.
Qed.

Lemma is_tail_cons_left:
  forall (A: Type) (i: A) c1 c2, is_tail (i :: c1) c2 -> is_tail c1 c2.
Proof.
  induction c2; intros; inversion H.
  constructor. constructor. constructor. auto. 
Qed.

Hint Resolve is_tail_refl is_tail_cons is_tail_in is_tail_cons_left: coqlib.

Lemma is_tail_incl:
  forall (A: Type) (l1 l2: list A), is_tail l1 l2 -> incl l1 l2.
Proof.
  induction 1; eauto with coqlib.
Qed.

Lemma is_tail_trans:
  forall (A: Type) (l1 l2: list A),
  is_tail l1 l2 -> forall (l3: list A), is_tail l2 l3 -> is_tail l1 l3.
Proof.
  induction 1; intros. auto. apply IHis_tail. eapply is_tail_cons_left; eauto.
Qed.

(** [list_forall2 P [x1 ... xN] [y1 ... yM]] holds iff [N = M] and
  [P xi yi] holds for all [i]. *)

Section FORALL2.

Variable A: Type.
Variable B: Type.
Variable P: A -> B -> Prop.

Inductive list_forall2: list A -> list B -> Prop :=
  | list_forall2_nil:
      list_forall2 nil nil
  | list_forall2_cons:
      forall a1 al b1 bl,
      P a1 b1 ->
      list_forall2 al bl ->
      list_forall2 (a1 :: al) (b1 :: bl).

End FORALL2.

Lemma list_forall2_imply:
  forall (A B: Type) (P1: A -> B -> Prop) (l1: list A) (l2: list B),
  list_forall2 P1 l1 l2 ->
  forall (P2: A -> B -> Prop),
  (forall v1 v2, In v1 l1 -> In v2 l2 -> P1 v1 v2 -> P2 v1 v2) ->
  list_forall2 P2 l1 l2.
Proof.
  induction 1; intros.
  constructor.
  constructor. auto with coqlib. apply IHlist_forall2; auto. 
  intros. auto with coqlib.
Qed.

(** Dropping the first or first two elements of a list. *)

Definition list_drop1 (A: Type) (x: list A) :=
  match x with nil => nil | hd :: tl => tl end.
Definition list_drop2 (A: Type) (x: list A) :=
  match x with nil => nil | hd :: nil => nil | hd1 :: hd2 :: tl => tl end.

Lemma list_drop1_incl:
  forall (A: Type) (x: A) (l: list A), In x (list_drop1 l) -> In x l.
Proof.
  intros. destruct l. elim H. simpl in H. auto with coqlib.
Qed.

Lemma list_drop2_incl:
  forall (A: Type) (x: A) (l: list A), In x (list_drop2 l) -> In x l.
Proof.
  intros. destruct l. elim H. destruct l. elim H.
  simpl in H. auto with coqlib.
Qed.

Lemma list_drop1_norepet:
  forall (A: Type) (l: list A), NoDup l -> NoDup (list_drop1 l).
Proof.
  intros. destruct l; simpl. constructor. inversion H. auto.
Qed.

Lemma list_drop2_norepet:
  forall (A: Type) (l: list A), NoDup l -> NoDup (list_drop2 l).
Proof.
  intros. destruct l; simpl. constructor.
  destruct l; simpl. constructor. inversion H. inversion H3. auto.
Qed.

Lemma list_map_drop1:
  forall (A B: Type) (f: A -> B) (l: list A), 
    list_drop1 (map f l) = map f (list_drop1 l).
Proof.
  intros; destruct l; reflexivity.
Qed.

Lemma list_map_drop2:
  forall (A B: Type) (f: A -> B) (l: list A), 
    list_drop2 (map f l) = map f (list_drop2 l).
Proof.
  intros; destruct l. reflexivity. destruct l; reflexivity.
Qed.

(** Dropping the first N elements of a list. *)

Fixpoint list_drop (A: Type) (n: nat) (x: list A) {struct n} : list A :=
  match n with
  | O => x
  | S n' => match x with nil => nil | hd :: tl => list_drop n' tl end
  end.

Lemma list_drop_incl:
  forall (A: Type) (x: A) n (l: list A), In x (list_drop n l) -> In x l.
Proof.
  induction n; simpl; intros. auto. 
  destruct l; auto with coqlib.
Qed.

Lemma list_drop_norepet:
  forall (A: Type) n (l: list A), NoDup l -> NoDup (list_drop n l).
Proof.
  induction n; simpl; intros. auto.
  inv H. constructor. auto.
Qed.

Lemma list_map_drop:
  forall (A B: Type) (f: A -> B) n (l: list A),
  list_drop n (map f l) = map f (list_drop n l).
Proof.
  induction n; simpl; intros. auto. 
  destruct l; simpl; auto.
Qed.

(** * Definitions and theorems over boolean types *)

Definition proj_sumbool (P Q: Prop) (a: {P} + {Q}) : bool :=
  if a then true else false.

Implicit Arguments proj_sumbool [P Q].

Coercion proj_sumbool: sumbool >-> bool.

Lemma proj_sumbool_true:
  forall (P Q: Prop) (a: {P}+{Q}), proj_sumbool a = true -> P.
Proof.
  intros P Q a. destruct a; simpl. auto. congruence.
Qed.

Section DECIDABLE_EQUALITY.

Variable A: Type.
Variable dec_eq: forall (x y: A), {x=y} + {x<>y}.
Variable B: Type.

Lemma dec_eq_true:
  forall (x: A) (ifso ifnot: B),
  (if dec_eq x x then ifso else ifnot) = ifso.
Proof.
  intros. destruct (dec_eq x x). auto. congruence.
Qed.

Lemma dec_eq_false:
  forall (x y: A) (ifso ifnot: B),
  x <> y -> (if dec_eq x y then ifso else ifnot) = ifnot.
Proof.
  intros. destruct (dec_eq x y). congruence. auto.
Qed.

Lemma dec_eq_sym:
  forall (x y: A) (ifso ifnot: B),
  (if dec_eq x y then ifso else ifnot) =
  (if dec_eq y x then ifso else ifnot).
Proof.
  intros. destruct (dec_eq x y). 
  subst y. rewrite dec_eq_true. auto.
  rewrite dec_eq_false; auto.
Qed.

End DECIDABLE_EQUALITY.

(** * Strong decidability results for list membership *)

Lemma strong_in_dec:
  forall {A : Type} (P Q : A -> Prop)
    (dP: forall i:A, {P i} + {Q i})
    (l : list A),
      {e | In e l /\ P e} + {forall e, In e l -> Q e}.
Proof.
  intros; induction l as [|h t [(e & IH & inP)|IH]].
  - by right.
  - by left; exists e; simpl; tauto. 
  destruct (dP h) as [hdP | nhdP]. 
  - by left; exists h; simpl; tauto.
  - by right; intros e [H|H]; clarify; apply (IH e). 
Qed.

Lemma strong_in_dec_prop:
  forall {A : Type} (P : A -> Prop)
    (dP: forall i:A, P i \/ ~ P i)
    (l : list A),
      (exists e, In e l /\ P e) \/ (forall e, ~ (In e l /\ P e)).
Proof.
  intros; induction l as [|h t [(e & IH & inP)|IH]].
  - by right; intros e [H _]. 
  - by left; exists e; simpl; tauto. 
  destruct (dP h) as [hdP | nhdP]. 
  - by left; exists h; simpl; tauto.
  by right; intros e [[] Pe]; clarify; elim (IH e).
Qed.

Lemma strong_in_dec_neg:
  forall {A : Type} (P : A -> Prop)
    (dP: forall i:A, {P i} + {~ P i})
    (l : list A),
      {e | In e l /\ ~ P e} + {forall e, In e l -> P e}.
Proof.
  intros; induction l as [|h t [(e & IH & inP)|IH]].
  - by right.
  - by left; exists e; simpl; tauto. 
  destruct (dP h) as [hdP | nhdP]. 
  - by right; intros e [H|H]; clarify; apply IH. 
  by left; exists h; simpl; tauto.
Qed.

(** * Further additions to Coq's List library *)

Lemma filter_app {A: Type}:
  forall f (l1: list A) l2, filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  by induction l1; intros; simpl; try done; case f; simpl; rewrite IHl1.
Qed.

Lemma rev_app {A: Type}:
  forall (l1: list A) l2, rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  by induction l1; intros; simpl; 
   [by rewrite <- app_nil_end|rewrite IHl1, app_ass].
Qed.

Lemma rev_last_eq:
  forall {A : Type} {l : list A} {h} {t}
    (EQ: rev l = h :: t),
    l = (rev t) ++ h :: nil.
Proof.
  by intros; rewrite <- (rev_involutive (h :: nil)), <- (rev_involutive l),
                     <- distr_rev, EQ.
Qed.

Lemma last_list_eq:
  forall {A:Type} {bl:list A} {bl' l l'}
    (EQ: bl ++ l :: nil = bl' ++ l' :: nil),
    l = l' /\ bl = bl'.
Proof.
  induction bl as [|i bl IH]; intros; destruct bl'; simpl in *; clarify.
      by elim (app_cons_not_nil bl' nil l'). 
    by elim (app_cons_not_nil bl nil l). 
  by exploit IH; [edone|]; intros [-> ->]. 
Qed.

(** [flatten] *)

Definition flatten {A} (l: list (list A)) := fold_right (@app _) nil l.

Lemma in_flatten:
  forall {A} (x: A) l,  In x (flatten l) <-> (exists y, In x y /\ In y l).
Proof.
  induction l; simpl.
    split; try done.
    by intros (? & ? & ?).
  split.
    intros X; apply -> in_app in X; destruct X as [X|X]; [by eauto|].
    pose proof (proj1 IHl X) as (? & ? & ?).
    eby eexists; split; [|right]. 
  intros (? & ? & [? | ?]); clarify; apply <- in_app; [by left|right]. 
  eby apply <- IHl; eexists. 
Qed.

Lemma flatten_app:
  forall {A} (l1: list (list A)) l2, 
    flatten (l1 ++ l2) = flatten l1 ++ flatten l2.
Proof. 
  induction l1; simpl; intros; try done.
  by rewrite IHl1, app_ass.
Qed.

(** Lemmas about [fold_left] *)

Lemma fold_left_map:
  forall {A B C} (f: A -> B) (g: C -> B -> C) xs a,
    fold_left g (map f xs) a = fold_left (fun a x => g a (f x)) xs a.
Proof. by induction xs; simpl. Qed.

Lemma fold_left_cons:
  forall A B x acc (f: A -> B),
    List.fold_left (fun r a => f a :: r) x acc =
    List.map f (rev x) ++ acc.
Proof.
  intros; revert acc.
  induction x; simpl; intros; try done.
  by rewrite IHx, map_app, app_ass.
Qed.

Lemma fold_left_app_red:
  forall A B x acc (f: A -> list B),
    fold_left (fun r a => f a ++ r) x acc =
    flatten (map f (rev x)) ++ acc. 
Proof.
  intros; revert acc.
  induction x; simpl; intros; try done.
  by rewrite IHx, map_app, flatten_app, app_ass; simpl; rewrite <- app_nil_end.
Qed.

(** [fold_left_opt] *)

Fixpoint fold_left_opt {A} {B} (f : B -> A -> option A)
                               (l : list B) (x : A) : option A :=
  match l with
    | nil => Some x
    | h :: t => optbind (fold_left_opt f t) (f h x)
  end.

Lemma fold_left_opt_app:
  forall {A} {B} f (l1 l2 : list B) (x : A),
    fold_left_opt f (l1 ++ l2) x =
    optbind (fun x => fold_left_opt f l2 x) (fold_left_opt f l1 x).
Proof.
  induction l1 as [|h l1 IH]; simpl; intros; [done|].
  by destruct (f h x); [apply IH|].
Qed.

Lemma fold_left_opt_consD:
  forall {A B f} {h:A} {t} {v:B} {v'}
    (FLO: fold_left_opt f (h :: t) v = Some v'),
  exists v'', f h v = Some v'' /\ fold_left_opt f t v'' = Some v'.
Proof.
  by intros; apply (optbind_someD FLO).
Qed.

Lemma fold_left_opt_appD:
  forall {A B f} {l1 : list A} {l2} {v:B} {v'}
    (FLO: fold_left_opt f (l1 ++ l2) v = Some v'),
  exists v'',
    fold_left_opt f l1 v = Some v'' /\
    fold_left_opt f l2 v'' = Some v'.
Proof.
  intros; rewrite fold_left_opt_app in FLO.
  by destruct (fold_left_opt f l1 v) as [v''|] _eqn : E; [eexists|].
Qed.

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
