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

(** Second optimisation: remove mfence instructions that are followed
    by a sequence of memory writes and another fence instruction *)

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

(** Static analysis: we perform a backwards all-path analysis with the Boolean
    abstract domain, where [bot] (false) means there is an atomic instruction
    after the current program point with no intervening reads. *)

Definition transfer (f: function) (pc: node) (after: LBoolean.t) :=
  match f.(fn_code)!pc with
  | None => after
  | Some i =>
      match i with
      | Inop s =>
          after
      | Iop op args res s =>
          after
      | Iload chunk addr args dst s =>
          LBoolean.top
      | Istore chunk addr args src s =>
          after
      | Icall sig ros args res s =>
          LBoolean.top
      | Icond cond args ifso ifnot =>
          after
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

Module D := LBoolean.

Module DS := Backward_Dataflow_Solver(D)(NodeSetBackward).

Definition analyze (f: RTL.function): PMap.t D.t :=
  match DS.fixpoint (successors f) (transfer f) 
                    ((f.(fn_entrypoint), D.bot) :: nil) with
  | None => PMap.init D.top
  | Some res => res
  end.

(** Code transformation: replace any [Ifence] instructions that 
    are post-dominated by an atomic instruction without any 
    intervening loads with a [Inop] instruction. *)

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
