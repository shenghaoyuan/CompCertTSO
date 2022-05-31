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

(** Type preservation for the Linearize pass *)

Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import Ast.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import LTLtyping.
Require Import LTLin.
Require Import Linearize.
Require Import LTLintyping.
Require Import Conventions.

(** * Type preservation for the linearization pass *)

Lemma wt_add_instr:
  forall f i k, wt_instr f i -> wt_code f k -> wt_code f (i :: k).
Proof.
  intros; red; intros. elim H1; intro. subst i0; auto. auto.
Qed.

Lemma wt_add_branch:
  forall f s k, wt_code f k -> wt_code f (add_branch s k).
Proof.
  intros; unfold add_branch. destruct (starts_with s k).
  auto. apply wt_add_instr; auto. constructor.
Qed.

Lemma wt_linearize_instr:
  forall f instr,
  LTLtyping.wt_instr f instr ->
  forall k,
  wt_code f.(LTL.fn_sig) k ->
  wt_code f.(LTL.fn_sig) (linearize_instr instr k).
Proof.
  induction 1; simpl; intros;
   try (case ifP; intro);
   try (apply wt_add_instr; [by constructor; auto; try (rewrite H; destruct cond)|]);
   try (by apply wt_add_branch); try done.
Qed.

Lemma wt_linearize_body:
  forall f,
  (forall pc instr, 
     f.(LTL.fn_code)!pc = Some instr -> LTLtyping.wt_instr f instr) ->
  forall enum,
  wt_code f.(LTL.fn_sig) (linearize_body f enum).
Proof.
  induction enum; simpl.
  red; simpl; intros; contradiction.
  caseEq ((LTL.fn_code f)!a); intros.
  apply wt_add_instr. constructor. apply wt_linearize_instr; eauto with coqlib.
  auto.
Qed.

Lemma wt_transf_function:
  forall f tf,
  LTLtyping.wt_function f ->
  transf_function f = OK tf ->
  wt_function tf. 
Proof.
  intros. inv H. monadInv H0. constructor; auto.
  simpl. apply wt_add_branch. 
  apply wt_linearize_body. auto. 
Qed.

Lemma wt_transf_fundef:
  forall f tf,
  LTLtyping.wt_fundef f ->
  transf_fundef f = OK tf ->
  wt_fundef tf. 
Proof.
  induction 1; intros. monadInv H. constructor. 
  monadInv H0. constructor; eapply wt_transf_function; eauto.
Qed.

Lemma program_typing_preserved:
  forall (p: LTL.program) (tp: LTLin.program),
  LTLtyping.wt_program p ->
  transf_program p = OK tp ->
  LTLintyping.wt_program tp.
Proof.
  intros; red; intros.
  generalize (transform_partial_program_function transf_fundef _ _ _ H0 H1).
  intros [f0 [IN TR]].
  eapply wt_transf_fundef; eauto. 
Qed.
