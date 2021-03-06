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

(** Pseudo-registers and register states.

  This library defines the type of pseudo-registers (also known as
  "temporaries" in compiler literature) used in the RTL
  intermediate language.  We also define finite sets and finite maps
  over pseudo-registers. *)

Require Import Coqlib.
Require Import Ast.
Require Import Maps.
Require Import Ordered.
Require Import FSets.
Require FSetAVL.

Definition reg: Type := positive.

Module Reg.

Definition eq := peq.

Definition typenv := PMap.t typ.

End Reg.

(** Mappings from registers to some type. *)

Module Regmap := PMap.

Set Implicit Arguments.

Definition regmap_optget
    (A: Type) (or: option reg) (dfl: A) (rs: Regmap.t A) : A :=
  match or with
  | None => dfl
  | Some r => Regmap.get r rs
  end.

Definition regmap_optset
    (A: Type) (or: option reg) (v: A) (rs: Regmap.t A) : Regmap.t A :=
  match or with
  | None => rs
  | Some r => Regmap.set r v rs
  end.

Notation "a # b" := (Regmap.get b a) (at level 1).
Notation "a ## b" := (List.map (fun r => Regmap.get r a) b) (at level 1).
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level).

(** Sets of registers *)

Module Regset := FSetAVL.Make(OrderedPositive).
