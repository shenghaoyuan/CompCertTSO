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

(** The whole compiler and its proof of semantic preservation *)

(** Libraries. *)
Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import Ast.
Require Import Values.
Require Import Traces.
Require Import TSOmachine.
(** Languages (syntax and semantics). *)
Require Csyntax.
Require Csem.
Require Csharpminor.
Require Cminor.
Require CminorSel.
Require RTL.
Require LTL.
Require LTLin.
Require Linear.
Require Mach.
Require Asm.
(** Translation passes. *)
Require Cshmgen.
Require Cminorgen.
Require Selection.
Require RTLgen.
Require Constprop.
Require CSE.
Require Fenceelim.
Require Fenceintro2.
Require Fenceelim2.
Require Allocation.
Require Tunneling.
Require Linearize.
Require Reload.
Require Stacking.
Require Asmgen.
(** Type systems. *)
Require Ctyping.
Require RTLtyping.
Require LTLtyping.
Require LTLintyping.
Require Lineartyping.
Require Machtyping.
(** Proofs of semantic preservation and typing preservation. *)
Require Cshmgenproof3.
Require Cstackedproof.
Require Cminorgenproof.
Require Selectionproof.
Require RTLgenproof.
Require Constpropproof.
Require CSEproof.
Require Fenceelimproof.
Require Fenceintro2proof.
Require Fenceelim2proof.
Require Allocproof.
Require Alloctyping.
Require Tunnelingproof.
Require Tunnelingtyping.
Require Linearizeproof.
Require Linearizetyping.
Require Reloadproof.
Require Reloadtyping.
Require Stackingproof.
Require Stackingtyping.
Require MMproof. 
Require Asmgenproof.

Open Local Scope string_scope.

(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

(** Program compilation *)

Definition transf_c_program (insf fe1 fi2 fe2: bool) (p: Csyntax.program) : res Asm.program :=
  if (Ctyping.typecheck_program p) then
    OK p 
    @@@ Cshmgen.transl_program
    @@@ Cminorgen.transl_program
    @@ Selection.sel_program
    @@@ (RTLgen.transl_program insf)
    @@ Constprop.transf_program
    @@ CSE.transf_program
    @@ (if fe1 then Fenceelim.transf_program else (fun x => x))
    @@ (if fi2 then Fenceintro2.transf_program else (fun x => x))
    @@ (if fe2 then Fenceelim2.transf_program else (fun x => x))
    @@@ Allocation.transf_program
    @@ Tunneling.tunnel_program
    @@@ Linearize.transf_program
    @@ Reload.transf_program
    @@@ Stacking.transf_program
    @@@ Asmgen.transf_program
  else
    Error (msg "Ctyping: type error").

(** Compiler correctness theorem *)

Theorem compiler_correctness : 
  forall fe1 fi2 fe2 p p',
    transf_c_program false fe1 fi2 fe2 p = OK p' ->
    forall args trace,
      valid_args args ->
      prog_traces tso_mm Asm.x86_sem p' args trace ->
      prog_traces tso_mm Csem.Clight.cl_sem p args trace. 
Proof.
  unfold transf_c_program, apply_partial, apply_total; intros.
  repeat (match goal with
   | H : context[match (Ctyping.typecheck_program ?p) with true => _ | false => _ end] |- _ =>
       destruct (Ctyping.typecheck_program p) as [] _eqn: ?; clarify 
   | H : context[match ?x with OK _ => _ | Error _ => _ end] |- _ =>
       destruct x as [] _eqn: ?; clarify
   end).
  Ltac typtac2 PL N := refine (modusponens _ _ (PL _ _) _); try edone; []; intro N.
  Ltac typtac3 PL N := refine (modusponens _ _ (PL _ _ _) _); try edone; []; intro N.
  Ltac typtac4 PL N := refine (modusponens _ _ (PL _ _ _ _) _);  try edone; []; intro N.
  Ltac phase X := eapply (Sim.traces_incl X); try edone; vauto.
  Ltac phase2 X := eapply (WTsim.traces_incl X); try edone; vauto.

  typtac3 Alloctyping.program_typing_preserved ALLOCt.
  typtac2 Tunnelingtyping.program_typing_preserved TUNNELt.
  typtac4 Linearizetyping.program_typing_preserved LINt.
  typtac2 Reloadtyping.program_typing_preserved RLt.
  typtac4 Stackingtyping.program_typing_preserved MACHt.

  phase (Cshmgenproof3.clight_cshm_sim    tso_mm).
  phase (Cstackedproof.cshm_cst_sim             ).
  phase (Cminorgenproof.cst_cminor_sim          ).
  phase (Selectionproof.sel_sim           tso_mm).
  phase (RTLgenproof.rtlgen_sim           tso_mm).
  phase (Constpropproof.constprop_sim     tso_mm).
  phase (CSEproof.cse_sim                 tso_mm).
  assert (prog_traces tso_mm LTL.ltl_sem p3 args trace)
  by (phase (Tunnelingproof.tunnel_sim    tso_mm);
      phase (Linearizeproof.linearize_sim tso_mm);
      phase (Reloadproof.reload_sim             );
      phase (Stackingproof.stacking_sim   tso_mm);
      phase (MMproof.mm_sim                     );
      phase (Asmgenproof.asmgen_sim             )).
  destruct fe1; [phase (Fenceelimproof.fenceelim_sim)|];
  (destruct fi2; [phase (Fenceintro2proof.fenceintro2_sim tso_mm)|]);
  (destruct fe2; [phase2 (Fenceelim2proof.fenceelim2sim)|]);
  phase (Allocproof.alloc_sim             tso_mm tso_pure_load_condition).
Qed.
