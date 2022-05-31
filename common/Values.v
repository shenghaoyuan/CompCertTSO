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

(** This module defines the type of values that is used in the dynamic
  semantics of all our intermediate languages. *)

Require Import Coqlib.
Require Import Ast.
Require Import Integers.
Require Import Floats.
Require Import Pointers.
Require Import Vlib.

(** A value is either:
- a machine integer;
- a floating-point number;
- a pointer: a pair of a memory address and an integer offset with respect
  to this address;
- the [Vundef] value denoting an arbitrary bit pattern, such as the
  value of an uninitialized variable.
*)


Inductive val: Type :=
  | Vundef: val
  | Vint: int -> val
  | Vfloat: float -> val
  | Vptr: pointer -> val.

Definition Vzero: val := Vint Int.zero.
Definition Vone: val := Vint Int.one.
Definition Vmone: val := Vint Int.mone.

Definition Vtrue: val := Vint Int.one.
Definition Vfalse: val := Vint Int.zero.

(** The module [Val] defines a number of arithmetic and logical operations
  over type [val].  Most of these operations are straightforward extensions
  of the corresponding integer or floating-point operations. *)

Module Val.

Lemma eq_dec: forall (x y: val), {x=y} + {x<>y}.
Proof. decide equality; [apply Int.eq_dec | apply Float.eq_dec | apply MPtr.eq_dec]. Qed.

Definition of_bool (b: bool): val := if b then Vtrue else Vfalse.

Definition of_bool3 (b: bool3): val := 
  match b with
    | b3_true    => Vtrue 
    | b3_false   => Vfalse
    | b3_unknown => Vundef
  end.

Definition option_bool_of_bool3 (b: bool3): option bool :=
  match b with
    | b3_true    => Some true
    | b3_false   => Some false
    | b3_unknown => None
  end.

Definition option_val_of_bool3 (b: bool3): option val :=
  match b with
    | b3_true    => Some Vtrue
    | b3_false   => Some Vfalse
    | b3_unknown => None
  end.

Definition has_type (v: val) (t: typ) : bool :=
  match v, t with
  | Vundef, _ => true
  | Vint _, Tint => true
  | Vfloat _, Tfloat => true
  | Vptr _, Tint => true
  | _, _ => false
  end.

Fixpoint has_type_list (vl: list val) (tl: list typ) {struct vl} : bool :=
  match vl, tl with
  | nil, nil => true
  | v1 :: vs, t1 :: ts => has_type v1 t1 && has_type_list vs ts
  | _, _ => false
  end.

(** Force a value to have a given type (by returning [Vundef] if it does not
    have the right type). This is used for ensuring that the values on 
    [MEwrite] and [Ecall] edges have the right types. *)
Definition conv (v: val) (t: typ) : val :=
  match v, t with
  | Vint _, Tint => v
  | Vfloat _, Tfloat => v
  | Vptr _, Tint => v
  | _, _ => Vundef
  end.

Fixpoint conv_list (vl: list val) (tl: list typ) {struct tl} : list val :=
  match tl with
  | nil => nil
  | t1 :: ts => 
     match vl with 
       | nil => Vundef :: conv_list nil ts
       | v1 :: vs => conv v1 t1 :: conv_list vs ts
     end
  end.

(** Truth values.  Pointers and non-zero integers are treated as [True].
  The integer 0 (also used to represent the null pointer) is [False].
  [Vundef] and floats are neither true nor false. *)

Definition is_true (v: val) : Prop :=
  match v with
  | Vint n => n <> Int.zero
  | Vptr _ => True
  | _ => False
  end.

Definition is_false (v: val) : Prop :=
  match v with
  | Vint n => n = Int.zero
  | _ => False
  end.

(* TODO maybe null pointer should be false? *)
Inductive bool_of_val: val -> bool -> Prop :=
  | bool_of_val_int_true:
      forall n, n <> Int.zero -> bool_of_val (Vint n) true
  | bool_of_val_int_false:
      bool_of_val (Vint Int.zero) false
  | bool_of_val_ptr_true:
      forall p, bool_of_val (Vptr p) true.

Definition neg (v: val) : val :=
  match v with
  | Vint n => Vint (Int.neg n)
  | _ => Vundef
  end.

Definition negf (v: val) : val :=
  match v with
  | Vfloat f => Vfloat (Float.neg f)
  | _ => Vundef
  end.

Definition absf (v: val) : val :=
  match v with
  | Vfloat f => Vfloat (Float.abs f)
  | _ => Vundef
  end.

Definition intoffloat (v: val) : val :=
  match v with
  | Vfloat f => Vint (Float.intoffloat f)
  | _ => Vundef
  end.

Definition intuoffloat (v: val) : val :=
  match v with
  | Vfloat f => Vint (Float.intuoffloat f)
  | _ => Vundef
  end.

Definition floatofint (v: val) : val :=
  match v with
  | Vint n => Vfloat (Float.floatofint n)
  | _ => Vundef
  end.

Definition floatofintu (v: val) : val :=
  match v with
  | Vint n => Vfloat (Float.floatofintu n)
  | _ => Vundef
  end.

Definition notint (v: val) : val :=
  match v with
  | Vint n => Vint (Int.xor n Int.mone)
  | _ => Vundef
  end.

(* This might cause problem with treating null as false *)
Definition notbool (v: val) : val :=
  match v with
  | Vint n => of_bool (Int.eq n Int.zero)
  | Vptr _ => Vfalse
  | _ => Vundef
  end.

(** [sign v = -1] if [v < 0]; [sign v = 0] if [v >= 0] *)
Definition sign (v: val) : val :=
  match v with
  | Vint n => if zlt (Int.signed n) 0 then Vmone else Vzero
  | _ => Vundef
  end.

Definition zero_ext (nbits: Z) (v: val) : val :=
  match v with
  | Vint n => Vint(Int.zero_ext nbits n)
  | _ => Vundef
  end.

Definition sign_ext (nbits: Z) (v: val) : val :=
  match v with
  | Vint n => Vint(Int.sign_ext nbits n)
  | _ => Vundef
  end.

Definition singleoffloat (v: val) : val :=
  match v with
  | Vfloat f => Vfloat(Float.singleoffloat f)
  | _ => Vundef
  end.
  
Definition add (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.add n1 n2)
  | Vptr p1, Vint n2 => Vptr (MPtr.add p1 n2)
  | Vint n1, Vptr p2 => Vptr (MPtr.add p2 n1)
  | _, _ => Vundef
  end.


Definition sub (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.sub n1 n2)
  | Vptr p1, Vint n2 => Vptr(MPtr.sub_int p1 n2)
  | Vptr p1, Vptr p2 =>
    match MPtr.sub_ptr p1 p2 with
    | Some i => Vint i 
    | None => Vundef
    end
  | _, _ => Vundef
  end.

Definition mul (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.mul n1 n2)
  | _, _ => Vundef
  end.

Definition divs (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then Vundef else Vint(Int.divs n1 n2)
  | _, _ => Vundef
  end.

Definition mods (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then Vundef else Vint(Int.mods n1 n2)
  | _, _ => Vundef

  end.

Definition divu (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then Vundef else Vint(Int.divu n1 n2)
  | _, _ => Vundef
  end.

Definition modu (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then Vundef else Vint(Int.modu n1 n2)
  | _, _ => Vundef
  end.

Definition and (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.and n1 n2)
  | _, _ => Vundef
  end.

Definition or (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.or n1 n2)
  | _, _ => Vundef
  end.

Definition xor (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.xor n1 n2)
  | _, _ => Vundef
  end.

Definition shl (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 32)
     then Vint(Int.shl n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shr (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 32)
     then Vint(Int.shr n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shr_carry (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 32)
     then Vint(Int.shr_carry n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shrx (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 32)
     then Vint(Int.shrx n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shru (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 32)
     then Vint(Int.shru n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition rolm (v: val) (amount mask: int): val :=
  match v with
  | Vint n => Vint(Int.rolm n amount mask)
  | _ => Vundef
  end.

Definition ror (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 32)
     then Vint(Int.ror n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition rol (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 32)
     then Vint(Int.rol n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition addf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.add f1 f2)
  | _, _ => Vundef
  end.

Definition subf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.sub f1 f2)
  | _, _ => Vundef
  end.

Definition mulf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.mul f1 f2)
  | _, _ => Vundef
  end.

Definition divf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.div f1 f2)
  | _, _ => Vundef
  end.

Definition cmp_mismatch (c: comparison): val :=
  match c with
  | Ceq => Vfalse
  | Cne => Vtrue
  | _   => Vundef
  end.

(* HACK: not a proper handling of NULL! note that 0 != p for any p *)
Definition cmp (c: comparison) (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => of_bool (Int.cmp c n1 n2)
  | Vint n1, Vptr _ =>
      if Int.eq n1 Int.zero then cmp_mismatch c else Vundef
  | Vptr p1, Vptr p2 => of_bool3 (MPtr.cmp c p1 p2)
  | Vptr _, Vint n2 =>
      if Int.eq n2 Int.zero then cmp_mismatch c else Vundef
  | _, _ => Vundef
  end.

Definition cmpu (c: comparison) (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      of_bool (Int.cmpu c n1 n2)
  | Vint n1, Vptr _ =>
      if Int.eq n1 Int.zero then cmp_mismatch c else Vundef
  | Vptr p1, Vptr p2 => of_bool3 (MPtr.cmpu c p1 p2)
  | Vptr _, Vint n2 =>
      if Int.eq n2 Int.zero then cmp_mismatch c else Vundef
  | _, _ => Vundef
  end.

Definition cmpf (c: comparison) (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => of_bool (Float.cmp c f1 f2)
  | _, _ => Vundef
  end.


(** [load_result] is used in the memory model (library [Mem])
  to post-process the results of a memory read.  For instance,
  consider storing the integer value [0xFFF] on 1 byte at a
  given address, and reading it back.  If it is read back with
  chunk [Mint8unsigned], zero-extension must be performed, resulting
  in [0xFF].  If it is read back as a [Mint8signed], sign-extension
  is performed and [0xFFFFFFFF] is returned.   Type mismatches
  (e.g. reading back a float as a [Mint32]) read back as [Vundef]. *)

Definition load_result (chunk: memory_chunk) (v: val) :=
  match chunk, v with
  | Mint8signed, Vint n => Vint (Int.sign_ext 8 n)
  | Mint8unsigned, Vint n => Vint (Int.zero_ext 8 n)
  | Mint16signed, Vint n => Vint (Int.sign_ext 16 n)
  | Mint16unsigned, Vint n => Vint (Int.zero_ext 16 n)
  | Mint32, Vint n => Vint n
  | Mint32, Vptr p => Vptr p
  | Mfloat32, Vfloat f => Vfloat(Float.singleoffloat f)
  | Mfloat64, Vfloat f => Vfloat f
  | _, _ => Vundef
  end.



(** Theorems on arithmetic operations. *)

Theorem cast8unsigned_and:
  forall x, zero_ext 8 x = and x (Vint(Int.repr 255)).
Proof.
  destruct x; simpl; auto. decEq. 
  change 255 with (two_p 8 - 1). apply Int.zero_ext_and. vm_compute; auto.
Qed.

Theorem cast16unsigned_and:
  forall x, zero_ext 16 x = and x (Vint(Int.repr 65535)).
Proof.
  destruct x; simpl; auto. decEq. 
  change 65535 with (two_p 16 - 1). apply Int.zero_ext_and. vm_compute; auto.
Qed.

Theorem istrue_not_isfalse:
  forall v, is_false v -> is_true (notbool v).
Proof.
  destruct v; simpl. try contradiction.
  intros. subst i. simpl. discriminate. auto. auto.
Qed.

Theorem isfalse_not_istrue:
  forall v, is_true v -> is_false (notbool v).
Proof.
  destruct v; simpl; try contradiction.
  intros. generalize (Int.eq_spec i Int.zero).
  case (Int.eq i Int.zero); intro.
  contradiction. simpl. auto.
  auto.
Qed.

Theorem bool_of_true_val:
  forall v, is_true v -> bool_of_val v true.
Proof.
  intro. destruct v; simpl; intros; try contradiction.
  constructor; auto. constructor.
Qed.

Theorem bool_of_true_val2:
  forall v, bool_of_val v true -> is_true v.
Proof.
  intros. inversion H; simpl; auto.
Qed.

Theorem bool_of_true_val_inv:
  forall v b, is_true v -> bool_of_val v b -> b = true.
Proof.
  intros. inversion H0; subst v b; simpl in H; auto. 
Qed.

Theorem bool_of_false_val:
  forall v, is_false v -> bool_of_val v false.
Proof.
  intro. destruct v; simpl; intros; try contradiction.
  subst i;  constructor.
Qed.

Theorem bool_of_false_val2:
  forall v, bool_of_val v false -> is_false v.
Proof.
  intros. inversion H; simpl; auto.
Qed.

Theorem bool_of_false_val_inv:
  forall v b, is_false v -> bool_of_val v b -> b = false.
Proof.
  intros. inversion H0; subst v b; simpl in H.
  congruence. auto. contradiction.
Qed.

Theorem notbool_negb_1:
  forall b, of_bool (negb b) = notbool (of_bool b).
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_negb_2:
  forall b, of_bool b = notbool (of_bool (negb b)).
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_idem2:
  forall b, notbool(notbool(of_bool b)) = of_bool b.
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_idem3:
  forall x, notbool(notbool(notbool x)) = notbool x.
Proof.
  destruct x; simpl; auto. 
  case (Int.eq i Int.zero); reflexivity.
Qed.

Theorem add_commut: forall x y, add x y = add y x.
Proof.
  destruct x; destruct y; simpl; auto.
  decEq. apply Int.add_commut.
Qed.

Theorem add_assoc: forall x y z, add (add x y) z = add x (add y z).
Proof. 
  intros x y z. destruct x; destruct y; destruct z; simpl; auto.
  (* All ints. *)
  rewrite Int.add_assoc; auto. 
  (* ptr, int, int *)
  destruct p. unfold MPtr.add. rewrite Int.add_assoc. 
    pattern i1 at 1. rewrite Int.add_commut. reflexivity. 
  (* int, ptr, int *)
  destruct p. unfold MPtr.add. rewrite Int.add_assoc. 
  pattern i1 at 1. rewrite Int.add_commut. rewrite Int.add_assoc. reflexivity. 
  (* int, int, ptr *)
  destruct p. unfold MPtr.add. rewrite Int.add_assoc. reflexivity. 
Qed.

Theorem add_permut: 
  forall x y z, add x (add y z) = add y (add x z).
Proof.
  intros. rewrite (add_commut y z). rewrite <- add_assoc; try apply add_commut; auto.
Qed.

Theorem add_permut_4:
  forall x y z t, add (add x y) (add z t) = add (add x z) (add y t).
Proof.
  intros. rewrite add_permut; try apply add_not_scratch; auto. 
  rewrite add_assoc; auto. 
  rewrite add_permut; try apply add_not_scratch; auto. 
  symmetry. apply add_assoc; try apply add_not_scratch; auto. 
Qed.

Theorem neg_zero: neg Vzero = Vzero.
Proof.
  reflexivity.
Qed.

Theorem neg_add_distr: forall x y, neg(add x y) = add (neg x) (neg y).
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.neg_add_distr.
Qed.

Theorem sub_zero_r: forall x, sub Vzero x = neg x.
Proof.
  destruct x; simpl; auto. 
Qed.

Theorem sub_add_opp: forall x y, sub x (Vint y) = add x (Vint (Int.neg y)).
Proof.
  destruct x; intro y; try destruct p; simpl; try rewrite Int.sub_add_opp; auto.
Qed.

Theorem sub_opp_add: forall x y, sub x (Vint (Int.neg y)) = add x (Vint y).
Proof.
  intros. unfold sub, add.
  destruct x; auto. rewrite Int.sub_add_opp; rewrite Int.neg_involutive; auto.
  destruct p. simpl; rewrite Int.sub_add_opp; rewrite Int.neg_involutive; auto.
Qed.

Theorem sub_add_l:
  forall v1 v2 i, sub (add v1 (Vint i)) v2 = add (sub v1 v2) (Vint i).
Proof.
  destruct v1; destruct v2; intros; simpl; auto.
  rewrite Int.sub_add_l. auto.
  destruct p.  simpl; rewrite Int.sub_add_l; auto.
  destruct p; destruct p0; simpl; try rewrite Int.sub_add_l;
    destruct (zeq z z0); auto. 
Qed.

Theorem sub_add_r:
    forall v1 v2 i, sub v1 (add v2 (Vint i)) = add (sub v1 v2) (Vint (Int.neg i)).
Proof.
  destruct v1; destruct v2; intros; simpl; auto.
  rewrite Int.sub_add_r. auto.
  repeat rewrite Int.sub_add_opp. decEq. 
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  destruct p. simpl; repeat rewrite Int.sub_add_opp. 
  decEq. decEq. rewrite Int.add_assoc. decEq. apply Int.neg_add_distr.
  destruct p; destruct p0; simpl; auto.   
  decEq. repeat rewrite Int.sub_add_opp. 
  destruct (zeq z z0). simpl.
  rewrite Int.add_assoc. repeat f_equal. apply Int.neg_add_distr.
  simpl; reflexivity.
Qed.

Theorem mul_commut: forall x y, mul x y = mul y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.mul_commut.
Qed.

Theorem mul_assoc: forall x y z, mul (mul x y) z = mul x (mul y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.mul_assoc.
Qed.

Theorem mul_add_distr_l:
  forall x y z, mul (add x y) z = add (mul x z) (mul y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.mul_add_distr_l.
Qed.


Theorem mul_add_distr_r:
  forall x y z, mul x (add y z) = add (mul x y) (mul x z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.mul_add_distr_r.
Qed.

Theorem mul_pow2:
  forall x n logn,
  Int.is_power2 n = Some logn ->
  mul x (Vint n) = shl x (Vint logn).
Proof.
  intros; destruct x; simpl; auto.
  change (Int.repr 32) with Int.iwordsize.
  rewrite (Int.is_power2_range _ _ H). decEq. apply Int.mul_pow2. auto.
Qed.  

Theorem mods_divs:
  forall x y, mods x y = sub x (mul (divs x y) y).
Proof.
  destruct x; destruct y; simpl; auto.
  case (Int.eq i0 Int.zero); simpl. auto. decEq. apply Int.mods_divs.
Qed.

Theorem modu_divu:
  forall x y, modu x y = sub x (mul (divu x y) y).
Proof.
  destruct x; destruct y; simpl; auto.
  generalize (Int.eq_spec i0 Int.zero);
  case (Int.eq i0 Int.zero); simpl. auto. 
  intro. decEq. apply Int.modu_divu. auto.
Qed.

Theorem divs_pow2:
  forall x n logn,
  Int.is_power2 n = Some logn ->
  divs x (Vint n) = shrx x (Vint logn).
Proof.
  intros; destruct x; simpl; auto.
  change (Int.repr 32) with Int.iwordsize.
  rewrite (Int.is_power2_range _ _ H). 
  generalize (Int.eq_spec n Int.zero);
  case (Int.eq n Int.zero); intro.
  subst n. compute in H. discriminate.
  decEq. apply Int.divs_pow2. auto.
Qed.

Theorem divu_pow2:
  forall x n logn,
  Int.is_power2 n = Some logn ->
  divu x (Vint n) = shru x (Vint logn).
Proof.
  intros; destruct x; simpl; auto.
  change (Int.repr 32) with Int.iwordsize.
  rewrite (Int.is_power2_range _ _ H). 
  generalize (Int.eq_spec n Int.zero);
  case (Int.eq n Int.zero); intro.
  subst n. compute in H. discriminate.
  decEq. apply Int.divu_pow2. auto.
Qed.

Theorem modu_pow2:
  forall x n logn,
  Int.is_power2 n = Some logn ->
  modu x (Vint n) = and x (Vint (Int.sub n Int.one)).
Proof.
  intros; destruct x; simpl; auto.
  generalize (Int.eq_spec n Int.zero);
  case (Int.eq n Int.zero); intro.
  subst n. compute in H. discriminate.
  decEq. eapply Int.modu_and; eauto.
Qed.

Theorem and_commut: forall x y, and x y = and y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.and_commut.
Qed.

Theorem and_assoc: forall x y z, and (and x y) z = and x (and y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.and_assoc.
Qed.

Theorem or_commut: forall x y, or x y = or y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.or_commut.
Qed.

Theorem or_assoc: forall x y z, or (or x y) z = or x (or y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.or_assoc.
Qed.

Theorem xor_commut: forall x y, xor x y = xor y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.xor_commut.
Qed.

Theorem xor_assoc: forall x y z, xor (xor x y) z = xor x (xor y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.xor_assoc.
Qed.

Theorem shl_mul: forall x y, Val.mul x (Val.shl Vone y) = Val.shl x y.
Proof.
  destruct x; destruct y; simpl; auto. 
  case (Int.ltu i0 (Int.repr 32)); auto.
  decEq. symmetry. apply Int.shl_mul.
Qed.

Theorem shl_rolm:
  forall x n,
  Int.ltu n (Int.repr 32) = true ->
  shl x (Vint n) = rolm x n (Int.shl Int.mone n).
Proof.
  intros; destruct x; simpl; auto.
  rewrite H. decEq. apply Int.shl_rolm. exact H.
Qed.

Theorem shru_rolm:
  forall x n,
  Int.ltu n (Int.repr 32) = true ->
  shru x (Vint n) = rolm x (Int.sub (Int.repr 32) n) (Int.shru Int.mone n).
Proof.
  intros; destruct x; simpl; auto.
  rewrite H. decEq. apply Int.shru_rolm. exact H.
Qed.

Theorem shrx_carry:
  forall x y,
  add (shr x y) (shr_carry x y) = shrx x y.
Proof.
  destruct x; destruct y; simpl; auto.
  case (Int.ltu i0 (Int.repr 32)); auto.
  simpl. decEq. apply Int.shrx_carry.
Qed.

Theorem or_rolm:
  forall x n m1 m2,
  or (rolm x n m1) (rolm x n m2) = rolm x n (Int.or m1 m2).
Proof.
  intros; destruct x; simpl; auto.
  decEq. apply Int.or_rolm.
Qed.

Theorem rolm_rolm:
  forall x n1 m1 n2 m2,
  rolm (rolm x n1 m1) n2 m2 =
    rolm x (Int.and (Int.add n1 n2) (Int.repr 31))
           (Int.and (Int.rol m1 n2) m2).
Proof.
  intros; destruct x; simpl; auto.
  decEq. 
  replace (Int.and (Int.add n1 n2) (Int.repr 31))
     with (Int.modu (Int.add n1 n2) (Int.repr 32)).
  by apply Int.rolm_rolm; eexists (2 ^ 27).
  change (Int.repr 31) with (Int.sub (Int.repr 32) Int.one).
  by apply Int.modu_and with (Int.repr 5).
Qed.

Theorem rolm_zero:
  forall x m,
  rolm x Int.zero m = and x (Vint m).
Proof.
  intros; destruct x; simpl; auto. decEq. apply Int.rolm_zero.
Qed.

Theorem addf_commut: forall x y, addf x y = addf y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Float.addf_commut.
Qed.

Lemma negate_cmp_mismatch:
  forall c,
  cmp_mismatch (negate_comparison c) = notbool(cmp_mismatch c).
Proof.
  destruct c; reflexivity.
Qed.

Theorem negate_cmp:
  forall c x y,
  cmp (negate_comparison c) x y = notbool (cmp c x y).
Proof.
  destruct x; destruct y; simpl; auto.
  rewrite Int.negate_cmp. apply notbool_negb_1.
  case (Int.eq i Int.zero). apply negate_cmp_mismatch. reflexivity.
  case (Int.eq i Int.zero). apply negate_cmp_mismatch. reflexivity.
  rewrite MPtr.negate_cmp. by destruct MPtr.cmp. 
Qed.

Theorem negate_cmpu:
  forall c x y,
  cmpu (negate_comparison c) x y = notbool (cmpu c x y).
Proof.
  destruct x; destruct y; simpl; auto.
  rewrite Int.negate_cmpu. apply notbool_negb_1.
  case (Int.eq i Int.zero). apply negate_cmp_mismatch. reflexivity.
  case (Int.eq i Int.zero). apply negate_cmp_mismatch. reflexivity.
  rewrite MPtr.negate_cmpu. by destruct MPtr.cmpu.
Qed.

Lemma swap_cmp_mismatch:
  forall c, cmp_mismatch (swap_comparison c) = cmp_mismatch c.
Proof.
  destruct c; reflexivity.
Qed.

Require Import NZAxioms.


Theorem swap_cmp:
  forall c x y,
  cmp (swap_comparison c) x y = cmp c y x.
Proof.
  destruct x; destruct y; simpl; auto.
  rewrite Int.swap_cmp. auto.
  case (Int.eq i Int.zero). apply swap_cmp_mismatch. auto.
  case (Int.eq i Int.zero). apply swap_cmp_mismatch. auto.
  rewrite MPtr.swap_cmp. auto.
Qed.

Theorem swap_cmpu:
  forall c x y,
  cmpu (swap_comparison c) x y = cmpu c y x.
Proof.
  destruct x; destruct y; simpl; auto.
  rewrite Int.swap_cmpu. auto.
  case (Int.eq i Int.zero). apply swap_cmp_mismatch. auto.
  case (Int.eq i Int.zero). apply swap_cmp_mismatch. auto.
  rewrite MPtr.swap_cmpu. auto.
Qed.

Theorem negate_cmpf_eq:
  forall v1 v2, notbool (cmpf Cne v1 v2) = cmpf Ceq v1 v2.
Proof.
  destruct v1; destruct v2; simpl; auto.
  rewrite Float.cmp_ne_eq. rewrite notbool_negb_1. 
  apply notbool_idem2.
Qed.

Theorem negate_cmpf_ne:
  forall v1 v2, notbool (cmpf Ceq v1 v2) = cmpf Cne v1 v2.
Proof.
  destruct v1; destruct v2; simpl; auto.
  rewrite Float.cmp_ne_eq. rewrite notbool_negb_1. auto. 
Qed.

Lemma or_of_bool:
  forall b1 b2, or (of_bool b1) (of_bool b2) = of_bool (b1 || b2).
Proof.
  destruct b1; destruct b2; reflexivity.
Qed.

Theorem cmpf_le:
  forall v1 v2, cmpf Cle v1 v2 = or (cmpf Clt v1 v2) (cmpf Ceq v1 v2).
Proof.
  destruct v1; destruct v2; simpl; auto.
  rewrite or_of_bool. decEq. apply Float.cmp_le_lt_eq.
Qed.

Theorem cmpf_ge:
  forall v1 v2, cmpf Cge v1 v2 = or (cmpf Cgt v1 v2) (cmpf Ceq v1 v2).
Proof.
  destruct v1; destruct v2; simpl; auto.
  rewrite or_of_bool. decEq. apply Float.cmp_ge_gt_eq.
Qed.

Definition is_bool (v: val) :=
  v = Vundef \/ v = Vtrue \/ v = Vfalse.

Lemma of_bool_is_bool:
  forall b, is_bool (of_bool b).
Proof.
  destruct b; unfold is_bool; simpl; tauto.
Qed.

Lemma undef_is_bool: is_bool Vundef.
Proof.
  unfold is_bool; tauto.
Qed.

Lemma cmp_mismatch_is_bool:
  forall c, is_bool (cmp_mismatch c).
Proof.
  destruct c; simpl; unfold is_bool; tauto.
Qed.

Lemma cmp_is_bool:
  forall c v1 v2, is_bool (cmp c v1 v2).
Proof.
  destruct v1; destruct v2; simpl; try apply undef_is_bool.
  apply of_bool_is_bool.
  case (Int.eq i Int.zero). apply cmp_mismatch_is_bool. apply undef_is_bool.
  case (Int.eq i Int.zero). apply cmp_mismatch_is_bool. apply undef_is_bool.
  case (MPtr.cmp c p p0); vauto.
Qed.

Lemma cmpu_is_bool:
  forall c v1 v2, is_bool (cmpu c v1 v2).
Proof.
  destruct v1; destruct v2; simpl; try apply undef_is_bool.
  apply of_bool_is_bool.
  case (Int.eq i Int.zero). apply cmp_mismatch_is_bool. apply undef_is_bool.
  case (Int.eq i Int.zero). apply cmp_mismatch_is_bool. apply undef_is_bool.
  case (MPtr.cmpu c p p0); vauto. 
Qed.

Lemma cmpf_is_bool:  forall c v1 v2, is_bool (cmpf c v1 v2).
Proof.
  destruct v1; destruct v2; simpl;
  apply undef_is_bool || apply of_bool_is_bool.
Qed.

Lemma notbool_is_bool:
  forall v, is_bool (notbool v).
Proof.
  destruct v; simpl.
  apply undef_is_bool. apply of_bool_is_bool. 
  apply undef_is_bool. unfold is_bool; tauto.
Qed.

Lemma notbool_xor:
  forall v, is_bool v -> v = xor (notbool v) Vone.
Proof.
  intros. elim H; intro.  
  subst v. reflexivity.
  elim H0; intro; subst v; reflexivity.
Qed.

Lemma rolm_lt_zero:
  forall v, rolm v Int.one Int.one = cmp Clt v (Vint Int.zero).
Proof.
  intros. destruct v; simpl; auto.
  transitivity (Vint (Int.shru i (Int.repr (Z_of_nat Int.wordsize - 1)))).
  decEq. symmetry. rewrite Int.shru_rolm. auto. auto. 
  rewrite Int.shru_lt_zero. destruct (Int.lt i Int.zero); auto. 
Qed.

Lemma rolm_ge_zero:
  forall v,
  xor (rolm v Int.one Int.one) (Vint Int.one) = cmp Cge v (Vint Int.zero).
Proof.
  intros. rewrite rolm_lt_zero. destruct v; simpl; auto.
  destruct (Int.lt i Int.zero); auto.
Qed.

(** The ``is less defined'' relation between values. 
    A value is less defined than itself, and [Vundef] is
    less defined than any value. *)

Inductive lessdef: val -> val -> Prop :=
  | lessdef_refl: forall v, lessdef v v
  | lessdef_undef: forall v, lessdef Vundef v.

Inductive lessdef_list: list val -> list val -> Prop :=
  | lessdef_list_nil:
      lessdef_list nil nil
  | lessdef_list_cons:
      forall v1 v2 vl1 vl2,
      lessdef v1 v2 -> lessdef_list vl1 vl2 ->
      lessdef_list (v1 :: vl1) (v2 :: vl2).

Hint Resolve lessdef_refl lessdef_undef lessdef_list_nil lessdef_list_cons.

Lemma lessdef_list_inv:
  forall vl1 vl2, lessdef_list vl1 vl2 -> vl1 = vl2 \/ In Vundef vl1.
Proof.
  induction 1; simpl.
  tauto.
  inv H. destruct IHlessdef_list. 
  left; congruence. tauto. tauto.
Qed.

Lemma lessdef_list_refl:
  forall vl, lessdef_list vl vl.
Proof.
  by intro vl; induction vl; constructor.
Qed.

Lemma load_result_lessdef:
  forall chunk v1 v2,
  lessdef v1 v2 -> lessdef (load_result chunk v1) (load_result chunk v2).
Proof.
  intros. inv H. auto. destruct chunk; simpl; auto.
Qed.

Lemma zero_ext_lessdef:
  forall n v1 v2, lessdef v1 v2 -> lessdef (zero_ext n v1) (zero_ext n v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

Lemma sign_ext_lessdef:
  forall n v1 v2, lessdef v1 v2 -> lessdef (sign_ext n v1) (sign_ext n v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

Lemma singleoffloat_lessdef:
  forall v1 v2, lessdef v1 v2 -> lessdef (singleoffloat v1) (singleoffloat v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

Lemma load_result_wt:
  forall chunk v,
  has_type (load_result chunk v) (type_of_chunk chunk).
Proof.
  by intros; case chunk; case v.
Qed.

Lemma has_type_lessdef:
  forall v1 t v2, lessdef v1 v2 -> has_type v2 t -> has_type v1 t.
Proof.
   by destruct 1.
Qed.

Lemma lessdef_list_length:
  forall {l l'} (LD : Val.lessdef_list l l'),
  length l = length l'.
Proof.
  induction l; intros. by inv LD.
  inv LD. simpl; f_equal. eauto.
Qed.

Lemma conv_wt: forall v typ, has_type (conv v typ) typ.
Proof. by intros; case v; case typ. Qed.

Lemma conv_wt2: forall v t, Val.has_type v t -> Val.conv v t = v.
Proof. by destruct v; destruct t. Qed.

Lemma conv_list_wt:
  forall vl tl, has_type_list (conv_list vl tl) tl.
Proof.
  intros; revert vl.
  elim tl; intros; simpl; try done.
  by case vl; intros; simpl; [|rewrite conv_wt; simpl].
Qed.

Lemma conv_list_wt2:
  forall vl tl, Val.has_type_list vl tl -> Val.conv_list vl tl = vl.
Proof.
  induction vl; destruct tl; simpl; try done.
  by intros X; destruct (andP X); rewrite conv_wt2, IHvl.
Qed.

Lemma conv_lessdef:
  forall typ v1 v2, lessdef v1 v2 -> lessdef (conv v1 typ) (conv v2 typ).
Proof.
  by destruct 1; constructor.
Qed.

Lemma conv_list_lessdef:
  forall tl v1 v2, lessdef_list v1 v2 -> lessdef_list (conv_list v1 tl) (conv_list v2 tl).
Proof.
  intro tl; elim tl; simpl; try done.
  intros a l IH v1 v2.
  by destruct v1; destruct v2; simpl; intro H; inv H; constructor;
     auto using lessdef_list_refl, conv_lessdef.
Qed.

Definition lessdef_sum {A} (vs1 vs2 : A + val) :=
  match vs1, vs2 with
    | inl a1, inl a2 => a1 = a2
    | inr v1, inr v2 => Val.lessdef v1 v2
    | _, _ => False
  end.

Definition lessdef_listsum {A} (l1 l2 : list (A + val)) :=
  list_forall2 lessdef_sum l1 l2.

End Val.
