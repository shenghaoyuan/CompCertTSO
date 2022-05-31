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
Require Import Floats.
Require Import Pointers.
Require Import Values.
Require Import Libtactics.
Require Import Ast.


Inductive unary_operation : Type :=
  | Ocast8unsigned: unary_operation        (**r 8-bit zero extension  *)
  | Ocast8signed: unary_operation          (**r 8-bit sign extension  *)
  | Ocast16unsigned: unary_operation       (**r 16-bit zero extension  *)
  | Ocast16signed: unary_operation         (**r 16-bit sign extension *)
  | Onegint: unary_operation               (**r integer opposite *)
  | Onotbool: unary_operation              (**r boolean negation  *)
  | Onotint: unary_operation               (**r bitwise complement  *)
  | Onegf: unary_operation                 (**r float opposite *)
  | Osingleoffloat: unary_operation        (**r float truncation *)
  | Ointoffloat: unary_operation           (**r signed integer to float *)
  | Ointuoffloat: unary_operation          (**r unsigned integer to float *)
  | Ofloatofint: unary_operation           (**r float to signed integer *)
  | Ofloatofintu: unary_operation.         (**r float to unsigned integer *)

Inductive binary_operation : Type :=
  | Oadd: binary_operation                 (**r integer addition *)
  | Osub: binary_operation                 (**r integer subtraction *)
  | Omul: binary_operation                 (**r integer multiplication *)
  | Odiv: binary_operation                 (**r integer signed division *)
  | Odivu: binary_operation                (**r integer unsigned division *)
  | Omod: binary_operation                 (**r integer signed modulus *)
  | Omodu: binary_operation                (**r integer unsigned modulus *)
  | Oand: binary_operation                 (**r bitwise ``and'' *)
  | Oor: binary_operation                  (**r bitwise ``or'' *)
  | Oxor: binary_operation                 (**r bitwise ``xor'' *)
  | Oshl: binary_operation                 (**r left shift *)
  | Oshr: binary_operation                 (**r right signed shift *)
  | Oshru: binary_operation                (**r right unsigned shift *)
  | Oaddf: binary_operation                (**r float addition *)
  | Osubf: binary_operation                (**r float subtraction *)
  | Omulf: binary_operation                (**r float multiplication *)
  | Odivf: binary_operation                (**r float division *)
  | Ocmp: comparison -> binary_operation   (**r integer signed comparison *)
  | Ocmpu: comparison -> binary_operation  (**r integer unsigned comparison *)
  | Ocmpf: comparison -> binary_operation. (**r float comparison *)

Inductive atomic_statement : Type :=
  | AScas: atomic_statement                (**r compare and swap *)
  | ASlkinc: atomic_statement.             (**r lock inc *)

Definition eval_unop (op: unary_operation) (arg: val) : option val :=
  match op, arg with
  | Ocast8unsigned, _ => Some (Val.zero_ext 8 arg)
  | Ocast8signed, _ => Some (Val.sign_ext 8 arg)
  | Ocast16unsigned, _ => Some (Val.zero_ext 16 arg)
  | Ocast16signed, _ => Some (Val.sign_ext 16 arg)
  | Onegint, Vint n1 => Some (Vint (Int.neg n1))
  | Onotbool, Vint n1 => Some (Val.of_bool (Int.eq n1 Int.zero))
  | Onotbool, Vptr p => Some Vfalse
  | Onotint, Vint n1 => Some (Vint (Int.not n1))
  | Onegf, Vfloat f1 => Some (Vfloat (Float.neg f1))
  | Osingleoffloat, _ => Some (Val.singleoffloat arg)
  | Ointoffloat, Vfloat f1 => Some (Vint (Float.intoffloat f1))
  | Ointuoffloat, Vfloat f1 => Some (Vint (Float.intuoffloat f1))
  | Ofloatofint, Vint n1 => Some (Vfloat (Float.floatofint n1))
  | Ofloatofintu, Vint n1 => Some (Vfloat (Float.floatofintu n1))
  | _, _ => None
  end.

Definition eval_compare_mismatch (c: comparison) : option val :=
  match c with Ceq => Some Vfalse | Cne => Some Vtrue | _ => None end.

Definition eval_compare_null (c: comparison) (n: int) : option val :=
  if Int.eq n Int.zero then eval_compare_mismatch c else None.

Definition eval_binop
            (op: binary_operation) (arg1 arg2: val): option val :=
  match op, arg1, arg2 with
  | Oadd, Vint n1, Vint n2 => Some (Vint (Int.add n1 n2))
  | Oadd, Vint n1, Vptr p2 => Some (Vptr (Ptr.add p2 n1))
  | Oadd, Vptr p1, Vint n2 => Some (Vptr (Ptr.add p1 n2))
  | Osub, Vint n1, Vint n2 => Some (Vint (Int.sub n1 n2))
  | Osub, Vptr p1, Vint n2 => Some (Vptr (Ptr.sub_int p1 n2))
  | Osub, Vptr p1, Vptr p2 => option_map Vint (Ptr.sub_ptr p1 p2)
(*      if eq_block b1 b2 then Some (Vint (Int.sub n1 n2)) else None *)
  | Omul, Vint n1, Vint n2 => Some (Vint (Int.mul n1 n2))
  | Odiv, Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.divs n1 n2))
  | Odivu, Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.divu n1 n2))
  | Omod, Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.mods n1 n2))
  | Omodu, Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.modu n1 n2))
  | Oand, Vint n1, Vint n2 => Some (Vint (Int.and n1 n2))
  | Oor, Vint n1, Vint n2 => Some (Vint (Int.or n1 n2))
  | Oxor, Vint n1, Vint n2 => Some (Vint (Int.xor n1 n2))
  | Oshl, Vint n1, Vint n2 =>
      if Int.ltu n2 (Int.repr 32) then Some (Vint (Int.shl n1 n2)) else None
  | Oshr, Vint n1, Vint n2 =>
      if Int.ltu n2 (Int.repr 32) then Some (Vint (Int.shr n1 n2)) else None
  | Oshru, Vint n1, Vint n2 =>
      if Int.ltu n2 (Int.repr 32) then Some (Vint (Int.shru n1 n2)) else None
   | Oaddf, Vfloat f1, Vfloat f2 => Some (Vfloat (Float.add f1 f2))
  | Osubf, Vfloat f1, Vfloat f2 => Some (Vfloat (Float.sub f1 f2))
  | Omulf, Vfloat f1, Vfloat f2 => Some (Vfloat (Float.mul f1 f2))
  | Odivf, Vfloat f1, Vfloat f2 => Some (Vfloat (Float.div f1 f2))
  | Ocmp c, Vint n1, Vint n2 => Some (Val.of_bool(Int.cmp c n1 n2))
  | Ocmp c, Vptr p1, Vptr p2 => Val.option_val_of_bool3 (Ptr.cmp c p1 p2)  (* was Some (Val.of_bool(Ptr.cmp c p1 p2)) *)
  | Ocmp c, Vptr p1, Vint n2 =>
      eval_compare_null c n2 (* note that pointer is always different from int! *)
                             (* (null is 'Vint 0') *)
  | Ocmp c, Vint n1, Vptr p2 =>
      eval_compare_null c n1
  | Ocmpu c, Vint n1, Vint n2 =>
      Some (Val.of_bool(Int.cmpu c n1 n2))
  | Ocmpf c, Vfloat f1, Vfloat f2 =>
      Some (Val.of_bool (Float.cmp c f1 f2))
  | _, _, _ => None
  end.

Require Import Events.

Definition sem_atomic_statement 
  (astmt : atomic_statement) (args : list val) : option (pointer * rmw_instr) := 
  match astmt, args with
    | AScas, Vptr p :: n :: o :: nil =>
        if (Val.eq_dec o Vundef)
          then None
            else if (Val.has_type o Tint)
              then if (Val.eq_dec n Vundef)
                then None
                else if (Val.has_type n Tint)
                  then Some (p, rmw_CAS o n)
                  else None
              else None
    | ASlkinc, Vptr p :: nil => Some (p, rmw_ADD (Vint Int.one))
    | _, _ => None
  end.

