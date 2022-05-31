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

(** pointers are block-id--offset pairs. *)
Inductive pointer : Type :=
  | Ptr : Z -> int -> pointer.

Definition nullptr := Ptr 0 Int.zero.

Module MPtr.

Definition block (p : pointer) : Z :=
  match p with
  | Ptr b off => b
  end. 

Definition offset (p : pointer) : int :=
  match p with
  | Ptr b off => off
  end. 

Definition add (p : pointer) (i : int) : pointer :=
  match p with
  | Ptr b off => Ptr b (Int.add off i)
  end.

Definition sub_int (p : pointer) (i : int) : pointer :=
  match p with
  | Ptr b off => Ptr b (Int.sub off i)
  end.

Definition sub_ptr (p1 p2 : pointer) : option int :=
  match p1, p2 with
  | Ptr b1 off1, Ptr b2 off2 => 
    if zeq b1 b2
      then Some(Int.sub off1 off2)
      else None
  end.

Definition eq_dec (p q : pointer) : { p = q } + {p <> q}.
Proof.
  decide equality. apply Int.eq_dec. apply Z_eq_dec.
Defined.

Definition eq (p q : pointer) : bool :=
  if (eq_dec p q) then true else false.

Lemma eq_true:
  forall (A: Type) (x: pointer) (a b: A), (if eq x x then a else b) = a.
Proof.
  by intros; unfold eq; case eq_dec.
Qed.

Lemma eq_false:
  forall (A: Type) (x y: pointer) (a b: A), 
    x <> y -> (if eq x y then a else b) = b.
Proof.
  by intros; unfold eq; case eq_dec.
Qed.

Lemma eq_sym:
  forall x y, eq x y = eq y x.
Proof.
  intros; unfold eq. 
  case (eq_dec x y); case (eq_dec y x); auto.
  intros H1 H2. elim H1. auto.
Qed.

(** Signed comparison *)

Definition lt_bool (p1 p2 : pointer) : bool :=
  match p1, p2 with
  | Ptr b1 off1, Ptr b2 off2 => 
    if zlt b1 b2 
    then true 
    else if zeq b1 b2 
         then Int.lt off1 off2
         else false
  end.

Definition lt (p1 p2 : pointer) : bool3 :=
  match p1, p2 with
  | Ptr b1 off1, Ptr b2 off2 => 
    if zeq b1 b2 then bool2bool3 (Int.lt off1 off2)
                 else b3_unknown
  end.

Definition cmp (c: comparison) (x y : pointer) : bool3 :=
  match c with
  | Ceq => bool2bool3 (eq x y)
  | Cne => bool2bool3 (negb (eq x y))
  | Clt => lt x y
  | Cle => negb3 (lt y x)
  | Cgt => lt y x
  | Cge => negb3 (lt x y)
  end.

Lemma negate_cmp:
  forall c x y, cmp (negate_comparison c) x y = negb3 (cmp c x y).
Proof.
  by intros; destruct c; simpl; b3_simps.
Qed.

Lemma swap_cmp:
  forall c x y, cmp (swap_comparison c) x y = cmp c y x.
Proof.
  by intros; destruct c; simpl; auto; rewrite eq_sym. 
Qed.


(** Unsigned comparison *)

Definition ltu_bool (p1 p2 : pointer) : bool :=
  match p1, p2 with
  | Ptr b1 off1, Ptr b2 off2 => 
    if zlt b1 b2 
    then true 
    else if zeq b1 b2 
         then Int.ltu off1 off2
         else false
  end.

Definition ltu (p1 p2 : pointer) : bool3 :=
  match p1, p2 with
  | Ptr b1 off1, Ptr b2 off2 => 
    if zeq b1 b2 then bool2bool3 (Int.ltu off1 off2)
                 else b3_unknown
  end.

Definition cmpu (c: comparison) (x y : pointer) : bool3 :=
  match c with
  | Ceq => bool2bool3 (eq x y)
  | Cne => bool2bool3 (negb (eq x y))
  | Clt => ltu x y
  | Cle => negb3 (ltu y x)
  | Cgt => ltu y x
  | Cge => negb3 (ltu x y)
  end.

Lemma negate_cmpu:
  forall c x y, cmpu (negate_comparison c) x y = negb3 (cmpu c x y).
Proof.
  by intros; destruct c; simpl; b3_simps.
Qed.

Lemma swap_cmpu:
  forall c x y, cmpu (swap_comparison c) x y = cmpu c y x.
Proof.
  by intros; destruct c; simpl; auto; rewrite eq_sym. 
Qed.

Lemma add_zero_r: forall p,
  MPtr.add p Int.zero = p.
Proof.
  by intros; destruct p; simpl; rewrite Int.add_zero.
Qed.

Lemma add_add_r: forall p n1 n2,
  MPtr.add p (Int.add n1 n2) = MPtr.add (MPtr.add p n1) n2.
Proof.
  by intros; destruct p; simpl; rewrite Int.add_assoc.
Qed.

Lemma add_sub_r: forall p n1 n2,
  MPtr.add p (Int.sub n1 n2) = MPtr.add (MPtr.sub_int p n2) n1.
Proof.
  intros; destruct p; simpl.
  by rewrite <- Int.sub_add_l, (Int.add_commut _ n1), 
            Int.sub_add_l, Int.add_commut.
Qed.

Lemma add_add_l: forall p n1 n2,
  MPtr.add (MPtr.add p n1) n2 = MPtr.add p (Int.add n1 n2). 
Proof.
  by symmetry; apply add_add_r.
Qed.

Lemma add_sub_l: forall p n1 n2,
  MPtr.add (MPtr.sub_int p n2) n1 = MPtr.add p (Int.sub n1 n2). 
Proof.
  by symmetry; apply add_sub_r.
Qed.

Lemma sub_zero_r: forall p,
  MPtr.sub_int p Int.zero = p.
Proof.
  by intros; destruct p; simpl; rewrite Int.sub_zero_r.
Qed.

Lemma sub_add_r: forall p n1 n2,
  MPtr.sub_int p (Int.add n1 n2) = MPtr.sub_int (MPtr.sub_int p n1) n2.
Proof.
  intros; destruct p; simpl.
  by rewrite !Int.sub_add_opp, !Int.neg_add_distr, Int.add_assoc.
Qed.

Lemma sub_sub_r: forall p n1 n2,
  MPtr.sub_int p (Int.sub n1 n2) = MPtr.add (MPtr.sub_int p n1) n2.
Proof.
  intros; destruct p; simpl. 
  by rewrite !Int.sub_add_opp, !Int.neg_add_distr, !Int.neg_involutive, Int.add_assoc.
Qed.

Lemma sub_add_l: forall p n1 n2,
  MPtr.sub_int (MPtr.add p n1) n2 = MPtr.add p (Int.sub n1 n2).
Proof.
  by intros; destruct p; simpl; rewrite !Int.sub_add_opp, Int.add_assoc.
Qed.

Lemma sub_sub_l: forall p n1 n2,
  MPtr.sub_int (MPtr.sub_int p n1) n2 = MPtr.sub_int p (Int.add n1 n2).
Proof.
  by symmetry; apply sub_add_r.
Qed.

End MPtr.

Bind Scope pointer_scope with pointer.

Notation "p + i" := (MPtr.add p i) : pointer_scope.

Delimit Scope pointer_scope with pointer.
