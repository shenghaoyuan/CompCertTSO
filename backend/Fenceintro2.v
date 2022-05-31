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

(** We perform PRE specialised for fenceelim2 *)

(* The implementation strategy runs two static analyses: 
[A] a backwards one returning
   TOP if along SOME path after the current program point there is an
   atomic instruction with no intervening reads.
[B] a forwards analysis returning BOT if along all paths to the current
   program point there is a fence with no later reads or atomic
   instructions.

The idea is that [B] says that an earlier fence that will be removed
if we insert a fence at the current program point.

So, insert fences after conditional nodes on branches where [A] returns
BOT provided that [A] returns TOP on the other branch and [B] returns BOT. *)

(** ** Analysis A *)

(** TOP (true) means that along SOME path after the current program
point there is an atomic instruction with no intervening reads *)

Definition transfer_A (f: function) (pc: node) (after: LBoolean.t) :=
  match f.(fn_code)!pc with
  | None => after
  | Some i =>
      match i with
      | Inop s =>
          after
      | Iop op args res s =>
          after
      | Iload chunk addr args dst s =>
          LBoolean.bot
      | Istore chunk addr args src s =>
          after
      | Icall sig ros args res s =>
          LBoolean.bot
      | Icond cond args ifso ifnot =>
          after 
      | Ireturn optarg =>
          LBoolean.bot
      | Ithreadcreate _ _ _ => 
          LBoolean.bot
      | Iatomic _ _ _ _ =>
          LBoolean.top
      | Ifence _ =>
          LBoolean.top
      end
  end.

Module DA := LBoolean.

Module DSA := Backward_Dataflow_Solver(DA)(NodeSetBackward).

Definition analyze_A (f: RTL.function): PMap.t DA.t :=
  match DSA.fixpoint (successors f) (transfer_A f) 
                    ((f.(fn_entrypoint), DA.bot) :: nil) with
  | None => PMap.init DA.bot
  | Some res => res
  end.

(** ** Analysis B *)

(** bot (false) means that along _all_ paths to the current program
   point there is a fence with no later reads or atomic instructions. *)

Definition transfer_B (f: function) (pc: node) (before: LBoolean.t) :=
  match f.(fn_code)!pc with
  | None => before
  | Some i =>
      match i with
      | Inop s =>
          before
      | Iop op args res s =>
          before
      | Iload chunk addr args dst s =>
          LBoolean.top
      | Istore chunk addr args src s =>
          before
      | Icall sig ros args res s =>
          LBoolean.top
      | Icond cond args ifso ifnot =>
          before
      | Ireturn optarg =>
          LBoolean.top
      | Ithreadcreate _ _ _ => 
          LBoolean.top
      | Iatomic _ _ _ _ =>
          LBoolean.top
      | Ifence _ =>
          LBoolean.bot
      end
  end.

Module DB :=  LBoolean.

Module DSB := Dataflow_Solver(DB)(NodeSetForward).

Definition analyze_B (f: RTL.function): PMap.t DB.t :=
  match DSB.fixpoint (successors f) (transfer_B f) 
                    ((f.(fn_entrypoint), DB.top) :: nil) with
  | None => PMap.init DB.top
  | Some res => res
  end.

(** Code transformation *)

(* insert fences after conditional nodes on branches where [A] returns
TOP provided that [A] returns BOT on the other branch and [B] returns BOT. *)

Fixpoint in_inops pc inops :=
  match inops with
    | (i1,i2)::l => 
      if peq pc i1 then Some i2 
      else if peq pc i2 then Some i1
      else in_inops pc l
    | nil => None
  end.

Definition transf_instr (appsA: PMap.t DA.t) (appsB: PMap.t DB.t) 
                          inops pc (instr: instruction) :=
  match instr with
  | Inop s => 
      match in_inops pc inops with
      | None => Inop s
      | Some pcb =>
          match appsA!!pc, appsB!!pc, appsA!!pcb with
          | false, false, true => Ifence s
          | _, _, _ => Inop s
          end
      end
  | _ => instr 
  end.

Definition transf_code (appsA: PMap.t DA.t) (appsB: PMap.t DB.t) inops instrs : code :=
  PTree.map (fun pc instr => transf_instr appsA appsB inops pc instr) instrs.

Fixpoint my_option_map A B (f:A -> option B) l :=
  match l with
    | nil => nil
    | a::l => 
      match f a with 
        | Some e => e :: my_option_map A B f l 
        | None => my_option_map A B f l 
      end
  end.
Implicit Arguments my_option_map [A B].

Definition transf_function (f: function) : function :=
  let appsA := analyze_A f in
  let appsB := analyze_B f in
  let inops :=
    my_option_map (fun x => 
      match snd x with 
        | Icond _ _ ifso ifnot => Some (ifso, ifnot)
        | _ => None 
      end )
      (PTree.elements f.(fn_code)) in
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (transf_code appsA appsB inops f.(fn_code))
    f.(fn_entrypoint).

Definition transf_fundef (fd: fundef) : fundef :=
  Ast.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.




