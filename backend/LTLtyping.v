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

(** Typing rules for LTL. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import Conventions.
(* Require TSOmachine. (* for thread_create_sig *) *)

(** The following predicates define a type system for LTL similar to that
  of [RTL] (see file [RTLtyping]): it statically guarantees that operations
  and addressing modes are applied to the right number of arguments
  and that the arguments are of the correct types.  Moreover, it also
  guarantees that the locations of arguments and results are "acceptable",
  i.e. either non-temporary registers or [Local] stack locations. *)

Section WT_INSTR.

Variable funct: function.

Definition valid_successor (s: node) : Prop :=
  exists i, funct.(fn_code)!s = Some i.

Definition call_loc_acceptable (sig: signature) (los: loc + ident) : Prop :=
  match los with
  | inl l => Loc.type l = Tint /\ loc_acceptable l /\ ~In l (loc_arguments sig)
  | inr s => True
  end.

Inductive wt_instr : instruction -> Prop :=
  | wt_Lnop:
      forall s,
      valid_successor s ->
      wt_instr (Lnop s)
  | wt_Lopmove:
      forall r1 r s,
      Loc.type r1 = Loc.type r -> loc_acceptable r1 -> loc_acceptable r ->
      valid_successor s ->
      wt_instr (Lop Omove (r1 :: nil) r s)
  | wt_Lop:
      forall op args res s,
      op <> Omove ->
      (List.map Loc.type args, Loc.type res) = type_of_operation op ->
      locs_acceptable args -> loc_acceptable res ->
      valid_successor s ->
      wt_instr (Lop op args res s)
  | wt_Lload:
      forall chunk addr args dst s,
      List.map Loc.type args = type_of_addressing addr ->
      Loc.type dst = type_of_chunk chunk ->
      locs_acceptable args -> loc_acceptable dst ->
      valid_successor s ->
      wt_instr (Lload chunk addr args dst s)
  | wt_Lstore:
      forall chunk addr args src s,
      List.map Loc.type args = type_of_addressing addr ->
      Loc.type src = type_of_chunk chunk ->
      locs_acceptable args -> loc_acceptable src ->
      valid_successor s ->
      wt_instr (Lstore chunk addr args src s)
  | wt_Lcall:
      forall sig ros args res s,
      List.map Loc.type args = sig.(sig_args) ->
      Loc.type res = proj_sig_res sig ->
      call_loc_acceptable sig ros ->
      locs_acceptable args -> loc_acceptable res ->
      valid_successor s ->
      wt_instr (Lcall sig ros args res s)
  | wt_Lcond:
      forall cond args s1 s2,
      List.map Loc.type args = type_of_condition cond ->
      locs_acceptable args ->
      valid_successor s1 -> valid_successor s2 ->
      wt_instr (Lcond cond args s1 s2)
  | wt_Lreturn: 
      forall optres,
      option_map Loc.type optres = funct.(fn_sig).(sig_res) ->
      match optres with None => True | Some r => loc_acceptable r end ->
      wt_instr (Lreturn optres)
  | wt_Latomic:
      forall op args res s,
      (List.map Loc.type args, Loc.type res) = type_of_atomic_statement op ->
      locs_acceptable args -> loc_acceptable res ->
      valid_successor s ->
      wt_instr (Latomic op args res s)
  | wt_Lfence:
      forall s,
      valid_successor s ->
      wt_instr (Lfence s)
  | wt_Lthreadcreate:
      forall fn arg s,
      List.map Loc.type (fn :: arg :: nil) = thread_create_sig.(sig_args) ->
      loc_acceptable fn ->
      loc_acceptable arg ->
      valid_successor s ->
      wt_instr (Lthreadcreate fn arg s).
      

End WT_INSTR.

Record wt_function (f: function): Prop :=
  mk_wt_function {
    wt_params:
      List.map Loc.type f.(fn_params) = f.(fn_sig).(sig_args);
    wt_acceptable:
      locs_acceptable f.(fn_params);
    wt_norepet:
      Loc.norepet f.(fn_params);
    wt_instrs:
      forall pc instr, 
      f.(fn_code)!pc = Some instr -> wt_instr f instr;
    wt_entrypoint:
      valid_successor f f.(fn_entrypoint)
}.

Inductive wt_fundef: fundef -> Prop :=
  | wt_fundef_external: forall ef,
      wt_fundef (External ef)
  | wt_function_internal: forall f,
      wt_function f ->
      wt_fundef (Internal f).

Definition wt_program (p: program): Prop :=
  forall i f, In (i, f) (prog_funct p) -> wt_fundef f.
