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

(** First optimisation: remove mfence instructions called with an empty
    buffer *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Pointers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Kildall.
Require Import Lattice.

(** Static analysis: we perform a forwards all-path analysis with the Boolean
    abstract domain, where [bot] (false) means there is an atomic instruction
    before the current program point with no intervening write. *)

Module D := LBoolean.

Module DS := Dataflow_Solver(D)(NodeSetForward).

Definition transfer (f: function) (pc: node) (before: LBoolean.t) :=
  match f.(fn_code)!pc with
  | None => before
  | Some i =>
      match i with
      | Inop s =>
          before
      | Iop op args res s =>
          before
      | Iload chunk addr args dst s =>
          before
      | Istore chunk addr args src s =>
          LBoolean.top
      | Icall sig ros args res s =>
          LBoolean.top
      | Icond cond args ifso ifnot =>
          before
      | Ireturn optarg =>
          LBoolean.top
      | Ithreadcreate _ _ _ => 
          LBoolean.top
      | Iatomic _ _ _ _ =>
          LBoolean.bot
      | Ifence _ =>
          LBoolean.bot
      end
  end.

Definition analyze (f: RTL.function): PMap.t D.t :=
  match DS.fixpoint (successors f) (transfer f) 
                    ((f.(fn_entrypoint), D.top) :: nil) with
  | None => PMap.init D.top
  | Some res => res
  end.

(** Code transformation: replace any [Ifence] instructions that 
    are dominated by an atomic instruction without any intervening 
    store operations with a [Inop] instruction. *)

Definition transf_instr (app: D.t) (instr: instruction) :=
  match instr with
  | Ifence s => if app then instr else Inop s
  | _ => instr
  end.

Definition transf_code (approxs: PMap.t D.t) (instrs: code) : code :=
  PTree.map (fun pc instr => transf_instr approxs!!pc instr) instrs.

Definition transf_function (f: function) : function :=
  let approxs := analyze f in
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (transf_code approxs f.(fn_code))
    f.(fn_entrypoint).

Definition transf_fundef (fd: fundef) : fundef :=
  Ast.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.

