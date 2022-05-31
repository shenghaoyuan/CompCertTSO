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

(** Type preservation for the Tunneling pass *)

Require Import Coqlib.
Require Import Maps.
Require Import UnionFind.
Require Import Ast.
Require Import Values.
Require Import Mem.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import LTLtyping.
Require Import Tunneling.
Require Import Tunnelingproof.

(** Tunneling preserves typing. *)

Lemma branch_target_valid_1:
  forall f pc, wt_function f ->
  valid_successor f pc ->
  valid_successor f (branch_target f pc).
Proof.
  intros. 
  assert (forall n p,
          (count_gotos f p < n)%nat ->
          valid_successor f p ->
          valid_successor f (branch_target f p)).
  induction n; intros.
  omegaContradiction.
  elim H2; intros i EQ.
  generalize (record_gotos_correct f p). rewrite EQ.
  destruct i; try congruence.
  intros [A | [B C]]. congruence. 
  generalize (wt_instrs _ H _ _ EQ); intro WTI; inv WTI.
  rewrite B. apply IHn. omega. auto. 

  apply H1 with (Datatypes.S (count_gotos f pc)); auto.
Qed.

Lemma tunnel_valid_successor:
  forall f pc,
  valid_successor f pc -> valid_successor (tunnel_function f) pc.
Proof.
  intros. destruct H as [i AT].
  unfold valid_successor; simpl. rewrite PTree.gmap. rewrite AT. 
  simpl. exists (tunnel_instr (record_gotos f) i); auto.
Qed.

Lemma branch_target_valid:
  forall f pc,
  wt_function f ->
  valid_successor f pc ->
  valid_successor (tunnel_function f) (branch_target f pc).
Proof.
  intros. apply tunnel_valid_successor. apply branch_target_valid_1; auto.
Qed.
  
Lemma wt_tunnel_instr:
  forall f i,
  wt_function f ->
  wt_instr f i -> wt_instr (tunnel_function f) (tunnel_instr (record_gotos f) i).
Proof.
  intros; inv H0; simpl; econstructor; eauto;
  eapply branch_target_valid; eauto.
Qed.

Lemma wt_tunnel_function:
  forall f, wt_function f -> wt_function (tunnel_function f).
Proof.
  intros. inversion H. constructor; simpl; auto.
  intros until instr. rewrite PTree.gmap. unfold option_map. 
  caseEq (fn_code f)!pc. intros b0 AT EQ. inv EQ. 
  apply wt_tunnel_instr; eauto.
  congruence.
  eapply branch_target_valid; eauto.
Qed.

Lemma wt_tunnel_fundef:
  forall f, wt_fundef f -> wt_fundef (tunnel_fundef f).
Proof.
  intros. inversion H; simpl. constructor; auto. 
  constructor. apply wt_tunnel_function; auto.
Qed.

Lemma program_typing_preserved:
  forall (p: LTL.program),
  wt_program p -> wt_program (tunnel_program p).
Proof.
  intros; red; intros.
  generalize (transform_program_function tunnel_fundef p i f H0).
  intros [f0 [IN TRANSF]].
  subst f. apply wt_tunnel_fundef. eauto.
Qed.
