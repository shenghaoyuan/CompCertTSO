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
Require Import Globalenvs.
Require Import Mach.
Require Import Machabstr.
Require Import Machconcr.
Require Import Machtyping.
Require Import TSOmachine.
Require Import MMtsosimproof.
Require Import MMperthreadsimproof.
Require Import Memcomp Traces.

Definition mm_match_prg p p' :=
  p = p' /\ wt_program p.

Theorem mm_sim : Sim.sim tso_mm tso_mm ma_sem mc_sem mm_match_prg.
Proof.
  eapply (
    MMtsosimproof.full_sim ma_sem mc_sem 
      (fun sge tge => sge = tge /\ wt_genv sge) 
      (fun sge tge => match_state tge)
      (fun sge tge => (ltof _ measure))
      mm_match_prg); intros.
  - intros. destruct GENVR as [-> _]. destruct MP as [-> _]. done.
  - intros. destruct MP as [-> WTP].
    exists tge. split. done. split. done. 
    intros v f FF. simpl in INIT. 
    eby exploit @Genv.find_funct_prop.
  - eapply Genv.initmem_allocated_global. apply INIT. edone.
  - destruct GENVR as [-> WT].
    destruct (thread_init_related WT INIT LD) as [si (SI & MS)].
    exists si. vauto.  
  - destruct GENVR as [-> WT].
    apply (thread_init_related_none INITF LD).
  - destruct GR as [-> WT].
    by apply mc_ma_perthread_sim.
  - destruct GR as [-> _]. apply mc_ma_perthread_stuck_sim.
  - destruct GR as [-> _]. apply mem_eq_preserves_simrel.
  - apply well_founded_ltof.
Qed.
