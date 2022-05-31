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
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.

(** ** Machine registers *)

(** for integers, we use only two temporaries for spilling and
      reloading, plus eax for the calling conventions;
    for floats, we use SSE2 registers 
      - will have to think about the top of the float stack 
        for the calling conventions 

  Following compcert, the type [mreg] does not include special-purpose 
  or reserved machine registers such as the stack pointer and the 
  condition codes. *)

(* Ignoring floats for now *)

Inductive mreg: Type :=
  (** Allocatable integer regs *)
  | rEBX | rESI | rEDI | rEBP
  (** Allocatable float regs *)
  | rXMM0 | rXMM1 | rXMM2 | rXMM3 | rXMM4 | rXMM5
  (** Integer temporaries *)
  | IT1 (* EDX *) | IT2 (* ECX *) | rEAX
  (** Float temporaries *)
  | FT1 (* XMM6 *) | FT2 (* XMM7 *) | FP0 (* top of the fp stack *).

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Qed.

Definition mreg_type (r: mreg): typ :=
  match r with
  | rEBX => Tint | rESI => Tint | rEDI => Tint | rEBP => Tint 
  | rXMM0 => Tfloat | rXMM1 => Tfloat | rXMM2 => Tfloat 
  | rXMM3 => Tfloat | rXMM4 => Tfloat | rXMM5 => Tfloat  
  | IT1 => Tint   | IT2 => Tint | rEAX => Tint 
  | FT1 => Tfloat | FT2 => Tfloat | FP0 => Tfloat  
  end.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | rEBX => 1 | rESI => 2 | rEDI => 3 | rEBP => 4
    | rXMM0 => 5 | rXMM1 => 6 | rXMM2 => 7 | rXMM3 => 8 | rXMM4 => 9 | rXMM5 => 10
    | IT1 => 11 | IT2 => 12 | rEAX => 13
    | FT1 => 14 | FT2 => 15 | FP0 => 16  
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    by destruct r1; destruct r2.
  Qed.
End IndexedMreg.

