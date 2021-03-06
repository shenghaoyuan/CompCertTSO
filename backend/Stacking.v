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

(** Layout of activation records; translation from Linear to Mach. *)

Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import Ast.
Require Import Integers.
Require Import Op.
Require Import RTL.
Require Import Locations.
Require Import Linear.
Require Import Bounds.
Require Import Mach.
Require Import Conventions.
Require Import Stacklayout.
Require Mem.

(** * Layout of activation records *)

(** The machine- and ABI-dependent aspects of the layout are defined
  in module [Stacklayout]. *)

(** Computation the frame offset for the given component of the frame.
  The component is expressed by the following [frame_index] sum type. *)

Inductive frame_index: Type :=
(*  | FI_link: frame_index 
  | FI_retaddr: frame_index *)
  | FI_local: Z -> typ -> frame_index
  | FI_arg: Z -> typ -> frame_index
  | FI_saved_int: Z -> frame_index
  | FI_saved_float: Z -> frame_index.

Definition offset_of_index (fe: frame_env) (idx: frame_index) :=
  match idx with
(*  | FI_link => fe.(fe_ofs_link) 
  | FI_retaddr => fe.(fe_ofs_retaddr) *)
  | FI_local x Tint => fe.(fe_ofs_int_local) + 4 * x
  | FI_local x Tfloat => fe.(fe_ofs_float_local) + 8 * x
  | FI_arg x ty => 4 * x
  | FI_saved_int x => fe.(fe_ofs_int_callee_save) + 4 * x
  | FI_saved_float x => fe.(fe_ofs_float_callee_save) + 8 * x
  end.

(** * Saving and restoring callee-save registers *)

(** [save_callee_save fe k] adds before [k] the instructions that
  store in the frame the values of callee-save registers used by the
  current function. *)

Definition save_callee_save_reg
    (bound: frame_env -> Z) (number: mreg -> Z) (mkindex: Z -> frame_index)
    (ty: typ) (fe: frame_env) (cs: mreg) (k: Mach.code) :=
  let i := number cs in
  if zlt i (bound fe)
  then Msetstack cs (Int.repr (offset_of_index fe (mkindex i))) ty :: k
  else k.

Definition save_callee_save_regs
    (bound: frame_env -> Z) (number: mreg -> Z) (mkindex: Z -> frame_index)
    (ty: typ) (fe: frame_env) (csl: list mreg) (k: Mach.code) :=
  List.fold_right (save_callee_save_reg bound number mkindex ty fe) k csl.

Definition save_callee_save_int (fe: frame_env) :=
  save_callee_save_regs 
    fe_num_int_callee_save index_int_callee_save FI_saved_int
    Tint fe int_callee_save_regs.

Definition save_callee_save_float (fe: frame_env) :=
  save_callee_save_regs
    fe_num_float_callee_save index_float_callee_save FI_saved_float 
    Tfloat fe float_callee_save_regs.

Definition save_callee_save (fe: frame_env) (k: Mach.code) :=
  save_callee_save_int fe (save_callee_save_float fe k).

(** [restore_callee_save fe k] adds before [k] the instructions that
  re-load from the frame the values of callee-save registers used by the
  current function, restoring these registers to their initial values. *)

Definition restore_callee_save_reg
    (bound: frame_env -> Z) (number: mreg -> Z) (mkindex: Z -> frame_index)
    (ty: typ) (fe: frame_env) (cs: mreg) (k: Mach.code) :=
  let i := number cs in
  if zlt i (bound fe)
  then Mgetstack (Int.repr (offset_of_index fe (mkindex i))) ty cs :: k
  else k.

Definition restore_callee_save_regs
    (bound: frame_env -> Z) (number: mreg -> Z) (mkindex: Z -> frame_index)
    (ty: typ) (fe: frame_env) (csl: list mreg) (k: Mach.code) :=
  List.fold_right (restore_callee_save_reg bound number mkindex ty fe) k csl.

Definition restore_callee_save_int (fe: frame_env) :=
  restore_callee_save_regs 
    fe_num_int_callee_save index_int_callee_save FI_saved_int
    Tint fe int_callee_save_regs.

Definition restore_callee_save_float (fe: frame_env) :=
  restore_callee_save_regs
    fe_num_float_callee_save index_float_callee_save FI_saved_float 
    Tfloat fe float_callee_save_regs.

Definition restore_callee_save (fe: frame_env) (k: Mach.code) :=
  restore_callee_save_int fe (restore_callee_save_float fe k).

(** * Code transformation. *)

(** Translation of operations and addressing mode.
  In Linear, the stack pointer has offset 0, i.e. points to the
  beginning of the Cminor stack data block.  In Mach, the stack
  pointer points to the bottom of the activation record,
  at offset [- fe.(fe_size)] where [fe] is the frame environment.
  Operations and addressing mode that are relative to the stack pointer
  must therefore be offset by [fe.(fe_size)] to preserve their
  behaviour. *)

Definition transl_op (shift: Z) (op: operation) :=
  shift_stack_operation (Int.repr shift) op.

Definition transl_addr (shift: Z) (addr: addressing) :=
  shift_stack_addressing (Int.repr shift) addr.

(* Definition transl_op (fe: frame_env) (op: operation) := *)
(*   match op with *)
(*   | Oaddrstack ofs => Oaddrstack (Int.add (Int.repr fe.(fe_size)) ofs) *)
(*   | _ => op *)
(*   end. *)

(* Definition transl_addr (fe: frame_env) (addr: addressing) := *)
(*   match addr with *)
(*   | Ainstack ofs => Ainstack (Int.add (Int.repr fe.(fe_size)) ofs) *)
(*   | _ => addr *)
(*   end. *)

(** Translation of a Linear instruction.  Prepends the corresponding
  Mach instructions to the given list of instructions.
  [Lgetstack] and [Lsetstack] moves between registers and stack slots
  are turned into [Mgetstack], [Mgetparent] or [Msetstack] instructions
  at offsets determined by the frame environment.
  Instructions and addressing modes are modified as described previously.
  Code to restore the values of callee-save registers is inserted
  before the function returns. *)

Definition transl_instr
    (fe: frame_env) (shift: Z) (i: Linear.instruction) (k: Mach.code) : Mach.code :=
  match i with
  | Lgetstack s r =>
      match s with
      | Local ofs ty =>
          Mgetstack (Int.repr (offset_of_index fe (FI_local ofs ty))) ty r :: k
      | Incoming ofs ty =>
          Mgetparam (Int.repr (offset_of_index fe (FI_arg ofs ty))) ty r :: k
      | Outgoing ofs ty =>
          Mgetstack (Int.repr (offset_of_index fe (FI_arg ofs ty))) ty r :: k
      end
  | Lsetstack r s =>
      match s with
      | Local ofs ty =>
          Msetstack r (Int.repr (offset_of_index fe (FI_local ofs ty))) ty :: k
      | Incoming ofs ty =>
          k (* should not happen *)
      | Outgoing ofs ty =>
          Msetstack r (Int.repr (offset_of_index fe (FI_arg ofs ty))) ty :: k
      end
  | Lop op args res =>
      Mop (transl_op shift op) args res :: k
  | Lload chunk addr args dst =>
      Mload chunk (transl_addr shift addr) args dst :: k
  | Lstore chunk addr args src =>
      Mstore chunk (transl_addr shift addr) args src :: k
  | Lcall sig ros =>
      Mcall sig ros :: k
  | Llabel lbl =>
      Mlabel lbl :: k
  | Lgoto lbl =>
      Mgoto lbl :: k
  | Lcond cond args lbl =>
      Mcond cond args lbl :: k
  | Lreturn =>
      restore_callee_save fe
        (Mreturn :: k)
  | Latomic aop args res =>
      Matomic aop args res :: k
  | Lfence =>
      Mfence :: k
  | Lthreadcreate =>
      Mthreadcreate :: k
  end.

(** Translation of a function.  Code that saves the values of used
  callee-save registers is inserted at function entry, followed
  by the translation of the function body.

  Subtle point: the compiler must check that the frame is no
  larger than [- Int.min_signed] bytes, otherwise arithmetic overflows
  could occur during frame accesses using signed machine integers as
  offsets. *)

Definition transl_code
    (fe: frame_env) (shift: Z) (il: list Linear.instruction) : Mach.code :=
  List.fold_right (transl_instr fe shift) nil il.

Definition transl_body (f: Linear.function) (fe: frame_env) (shift: Z) :=
  save_callee_save fe (transl_code fe shift f.(Linear.fn_code)).

Open Local Scope string_scope.

Definition align_stacksize stacksize rasize := 
  align (stacksize + rasize) (Mem.align_size stacksize) - rasize.

Definition align_framesize stacksize framesize rasize :=
  align (stacksize + rasize + framesize) 16 - stacksize - rasize.

Definition transf_function (f: Linear.function) : res Mach.function :=
  let fe := make_env (function_bounds f) in
  let stacksize := align_stacksize (Int.unsigned f.(Linear.fn_stacksize)) fe_retaddrsize in
  let framesize := align_framesize stacksize fe.(fe_size) fe_retaddrsize in 
  if zle (- Int.min_signed) (stacksize + framesize + fe_retaddrsize) then
    Error (msg "Stack size exceeded")
(*  if Int.lt f.(Linear.fn_stacksize) Int.zero then
    Error (msg "Stacking.transf_function") 
  else if zle (- Int.min_signed) (fe.(fe_size) + Int.unsigned (f.(Linear.fn_stacksize))) then
    Error (msg "Stack size exceeded") *)
  else if zle (- Int.min_signed) (size_arguments f.(Linear.fn_sig) * 4 + fe_retaddrsize) then
    Error (msg "Maximum number of arguments exceeeded")
  else
    OK (Mach.mkfunction
         f.(Linear.fn_sig)
         (transl_body f fe framesize)
         stacksize
         f.(Linear.fn_stacksize)
         framesize).

Definition transf_fundef (f: Linear.fundef) : res Mach.fundef :=
  Ast.transf_partial_fundef transf_function f.

Definition transf_program (p: Linear.program) : res Mach.program :=
  transform_partial_program transf_fundef p.

