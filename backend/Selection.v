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

(** Instruction selection *)

(** The instruction selection pass recognizes opportunities for using
  combined arithmetic and logical operations and addressing modes
  offered by the target processor.  For instance, the expression [x + 1]
  can take advantage of the "immediate add" instruction of the processor,
  and on the PowerPC, the expression [(x >> 6) & 0xFF] can be turned
  into a "rotate and mask" instruction.

  Instruction selection proceeds by bottom-up rewriting over expressions.
  The source language is Cminor and the target language is CminorSel. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Globalenvs.
Require Cminor.
Require Cminorops.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.

Open Local Scope cminorsel_scope.

(** Conversion of conditional expressions *)

Fixpoint negate_condexpr (e: condexpr): condexpr :=
  match e with
  | CEtrue => CEfalse
  | CEfalse => CEtrue
  | CEcond c el => CEcond (negate_condition c) el
  | CEcondition e1 e2 e3 =>
      CEcondition e1 (negate_condexpr e2) (negate_condexpr e3)
  end.

Definition is_compare_neq_zero (c: condition) : bool :=
  match c with
  | Ccompimm Cne n => Int.eq n Int.zero
  | Ccompuimm Cne n => Int.eq n Int.zero
  | _ => false
  end.

Definition is_compare_eq_zero (c: condition) : bool :=
  match c with
  | Ccompimm Ceq n => Int.eq n Int.zero
  | Ccompuimm Ceq n => Int.eq n Int.zero
  | _ => false
  end.

Fixpoint condexpr_of_expr (e: expr) : condexpr :=
  match e with
  | Eop (Ointconst n) Enil =>
      if Int.eq n Int.zero then CEfalse else CEtrue
  | Eop (Ocmp c) (e1 ::: Enil) =>
      if is_compare_neq_zero c then
        condexpr_of_expr e1
      else if is_compare_eq_zero c then
        negate_condexpr (condexpr_of_expr e1)
      else
        CEcond c (e1 ::: Enil)
  | Eop (Ocmp c) el =>
      CEcond c el
  | Econdition ce e1 e2 =>
      CEcondition ce (condexpr_of_expr e1) (condexpr_of_expr e2)
  | _ =>
      CEcond (Ccompimm Cne Int.zero) (e:::Enil)
  end.

(** Conversion of loads and stores *)

Definition load (chunk: memory_chunk) (e1: expr) :=
  match addressing chunk e1 with
  | (mode, args) => Eload chunk mode args
  end.

Definition store (chunk: memory_chunk) (e1 e2: expr) :=
  match addressing chunk e1 with
  | (mode, args) => Sstore chunk mode args e2
  end.

(** Instruction selection for operator applications.  Most of the work
    is done by the processor-specific smart constructors defined
    in module [SelectOp]. *)

Definition sel_constant (cst: Cminor.constant) : expr :=
  match cst with
  | Cminor.Ointconst n => Eop (Ointconst n) Enil
  | Cminor.Ofloatconst f => Eop (Ofloatconst f) Enil
  | Cminor.Oaddrsymbol id ofs => addrsymbol id ofs
  | Cminor.Oaddrstack ofs => addrstack ofs
  end.

Definition sel_unop (op: Cminorops.unary_operation) (arg: expr) : expr :=
  match op with
  | Cminorops.Ocast8unsigned => cast8unsigned arg 
  | Cminorops.Ocast8signed => cast8signed arg 
  | Cminorops.Ocast16unsigned => cast16unsigned arg 
  | Cminorops.Ocast16signed => cast16signed arg 
  | Cminorops.Onegint => negint arg
  | Cminorops.Onotbool => notbool arg
  | Cminorops.Onotint => notint arg
  | Cminorops.Onegf => negf arg
  | Cminorops.Osingleoffloat => singleoffloat arg
  | Cminorops.Ointoffloat => intoffloat arg
  | Cminorops.Ointuoffloat => intuoffloat arg
  | Cminorops.Ofloatofint => floatofint arg
  | Cminorops.Ofloatofintu => floatofintu arg
  end.

Definition sel_binop (op: Cminorops.binary_operation) (arg1 arg2: expr) : expr :=
  match op with
  | Cminorops.Oadd => add arg1 arg2
  | Cminorops.Osub => sub arg1 arg2
  | Cminorops.Omul => mul arg1 arg2
  | Cminorops.Odiv => divs arg1 arg2
  | Cminorops.Odivu => divu arg1 arg2
  | Cminorops.Omod => mods arg1 arg2
  | Cminorops.Omodu => modu arg1 arg2
  | Cminorops.Oand => and arg1 arg2
  | Cminorops.Oor => or arg1 arg2
  | Cminorops.Oxor => xor arg1 arg2
  | Cminorops.Oshl => shl arg1 arg2
  | Cminorops.Oshr => shr arg1 arg2
  | Cminorops.Oshru => shru arg1 arg2
  | Cminorops.Oaddf => addf arg1 arg2
  | Cminorops.Osubf => subf arg1 arg2
  | Cminorops.Omulf => mulf arg1 arg2
  | Cminorops.Odivf => divf arg1 arg2
  | Cminorops.Ocmp c => comp c arg1 arg2
  | Cminorops.Ocmpu c => compu c arg1 arg2
  | Cminorops.Ocmpf c => compf c arg1 arg2
  end.

(** Conversion from Cminor expression to Cminorsel expressions *)

Fixpoint sel_expr (a: Cminor.expr) : expr :=
  match a with
  | Cminor.Evar id => Evar id
  | Cminor.Econst cst => sel_constant cst
  | Cminor.Eunop op arg => sel_unop op (sel_expr arg)
  | Cminor.Ebinop op arg1 arg2 => sel_binop op (sel_expr arg1) (sel_expr arg2)
  | Cminor.Eload chunk addr => load chunk (sel_expr addr)
  | Cminor.Econdition cond ifso ifnot =>
      Econdition (condexpr_of_expr (sel_expr cond))
                 (sel_expr ifso) (sel_expr ifnot)
  end.

Fixpoint sel_exprlist (al: list Cminor.expr) : exprlist :=
  match al with
  | nil => Enil
  | a :: bl => Econs (sel_expr a) (sel_exprlist bl)
  end.

(** Conversion of atomic operations. *)

Definition sel_aop (aop : Cminorops.atomic_statement) :=
  match aop with
    | Cminorops.AScas => AScas
    | Cminorops.ASlkinc => ASlkinc
  end.

(** Conversion from Cminor statements to Cminorsel statements. *)

Fixpoint sel_stmt (s: Cminor.stmt) : stmt :=
  match s with
  | Cminor.Sskip => Sskip
  | Cminor.Sassign id e => Sassign id (sel_expr e)
  | Cminor.Sstore chunk addr rhs => store chunk (sel_expr addr) (sel_expr rhs)
  | Cminor.Scall optid sg fn args =>
      Scall optid sg (sel_expr fn) (sel_exprlist args)
  | Cminor.Sseq s1 s2 => Sseq (sel_stmt s1) (sel_stmt s2)
  | Cminor.Sifthenelse e ifso ifnot =>
      Sifthenelse (condexpr_of_expr (sel_expr e))
                  (sel_stmt ifso) (sel_stmt ifnot)
  | Cminor.Sloop body => Sloop (sel_stmt body)
  | Cminor.Sblock body => Sblock (sel_stmt body)
  | Cminor.Sexit n => Sexit n
  | Cminor.Sswitch e cases dfl => Sswitch (sel_expr e) cases dfl
  | Cminor.Sreturn None => Sreturn None
  | Cminor.Sreturn (Some e) => Sreturn (Some (sel_expr e))
  | Cminor.Slabel lbl body => Slabel lbl (sel_stmt body)
  | Cminor.Sgoto lbl => Sgoto lbl
  | Cminor.Sthread_create e1 e2 => Sthread_create (sel_expr e1) (sel_expr e2)
  | Cminor.Satomic optid aop args => Satomic optid (sel_aop aop) (sel_exprlist args)
  | Cminor.Smfence => Sfence
  end.

(** Conversion of functions and programs. *)

Definition sel_function (f: Cminor.function) : function :=
  mkfunction
    f.(Cminor.fn_sig)
    f.(Cminor.fn_params)
    f.(Cminor.fn_vars)
    f.(Cminor.fn_stackspace)
    (sel_stmt f.(Cminor.fn_body)).

Definition sel_fundef (f: Cminor.fundef) : fundef :=
  transf_fundef sel_function f.

Definition sel_program (p: Cminor.program) : program :=
  transform_program sel_fundef p.



