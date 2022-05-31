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

(** Typing rules for Linear. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Op.
Require Import Locations.
Require Import Linear.
Require Import Conventions.

(** The typing rules for Linear are similar to those for LTLin: we check
  that instructions receive the right number of arguments,
  and that the types of the argument and result registers agree
  with what the instruction expects.  Moreover, we  also
  enforces some correctness conditions on the offsets of stack slots
  accessed through [Lgetstack] and [Lsetstack] Linear instructions. *)

Section WT_INSTR.

Variable funct: function.

Definition slot_valid (s: slot) :=
  match s with
  | Local ofs ty => 0 <= ofs
  | Outgoing ofs ty => 0 <= ofs
  | Incoming ofs ty => In (S s) (loc_parameters funct.(fn_sig))
  end.

Definition slot_writable (s: slot) :=
  match s with
  | Local ofs ty => True
  | Outgoing ofs ty => True
  | Incoming ofs ty => False
  end.

Inductive wt_instr : instruction -> Prop :=
  | wt_Lgetstack:
      forall s r,
      slot_type s = mreg_type r ->
      slot_valid s ->
      wt_instr (Lgetstack s r)
  | wt_Lsetstack:
      forall s r,
      slot_type s = mreg_type r ->
      slot_valid s -> slot_writable s ->
      wt_instr (Lsetstack r s)
  | wt_Lopmove:
      forall r1 r,
      mreg_type r1 = mreg_type r ->
      wt_instr (Lop Omove (r1 :: nil) r)
  | wt_Lop:
      forall op args res,
      op <> Omove ->
      (List.map mreg_type args, mreg_type res) = type_of_operation op ->
      wt_instr (Lop op args res)
  | wt_Lload:
      forall chunk addr args dst,
      List.map mreg_type args = type_of_addressing addr ->
      mreg_type dst = type_of_chunk chunk ->
      wt_instr (Lload chunk addr args dst)
  | wt_Lstore:
      forall chunk addr args src,
      List.map mreg_type args = type_of_addressing addr ->
      mreg_type src = type_of_chunk chunk ->
      wt_instr (Lstore chunk addr args src)
  | wt_Lcall:
      forall sig ros,
      match ros with inl r => mreg_type r = Tint | _ => True end ->
      wt_instr (Lcall sig ros)
  | wt_Llabel:
      forall lbl,
      wt_instr (Llabel lbl)
  | wt_Lgoto:
      forall lbl,
      wt_instr (Lgoto lbl)
  | wt_Lcond:
      forall cond args lbl,
      List.map mreg_type args = type_of_condition cond ->
      wt_instr (Lcond cond args lbl)
  | wt_Lreturn: 
      wt_instr (Lreturn)
  | wt_Latomic:
      forall op args res,
      (List.map mreg_type args, mreg_type res) = type_of_atomic_statement op ->
      wt_instr (Latomic op args res)
  | wt_Lfence:
      wt_instr (Lfence)
  | wt_Lthreadcreate:
      wt_instr (Lthreadcreate).

End WT_INSTR.

Definition wt_code (f: function) (c: code) : Prop :=
  forall instr, In instr c -> wt_instr f instr.

Definition wt_function (f: function) : Prop :=
  wt_code f f.(fn_code).

Inductive wt_fundef: fundef -> Prop :=
  | wt_fundef_external: forall ef,
      wt_fundef (External ef)
  | wt_function_internal: forall f,
      wt_function f ->
      wt_fundef (Internal f).

Definition wt_program (p: program) : Prop :=
  forall i f, In (i, f) (prog_funct p) -> wt_fundef f.

