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

(** Predictor for return addresses in generated Asm code.
    The [return_address_offset] predicate defined here is used in the
    concrete semantics for Mach (module [Machconcr]) to determine the
    return addresses that are stored in activation records. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Asm.
Require Import Asmgen.

(** The ``code tail'' of an instruction list [c] is the list of instructions
  starting at PC [pos]. *)

Inductive code_tail: Z -> code -> code -> Prop :=
  | code_tail_0: forall c,
      code_tail 0 c c
  | code_tail_S: forall pos i c1 c2,
      code_tail pos c1 c2 ->
      code_tail (pos + 1) (i :: c1) c2.

Lemma code_tail_pos:
  forall pos c1 c2, code_tail pos c1 c2 -> pos >= 0.
Proof.
  induction 1; omega.
Qed.

(** Consider a Mach function [f] and a sequence [c] of Mach instructions
  representing the Mach code that remains to be executed after a
  function call returns.  The predicate [return_address_offset f c ofs]
  holds if [ofs] is the integer offset of the Asm instruction
  following the call in the assemby code obtained by translating the
  code of [f]. Graphically:
<<
     Mach function f    |--------- Mcall ---------|
         Mach code c    |                |--------|
                        |                 \        \
                        |                  \        \
                        |                   \        \
     Asm code           |                    |--------|
     Asm function       |--------------- Pbl ---------|

                        <-------- ofs ------->
>>
*)

Inductive return_address_offset: Mach.function -> Mach.code -> int -> Prop :=
  | return_address_offset_intro:
      forall f c ofs sig tf tc
        (TF: transf_function f = OK (sig,tf))
        (TC: transl_code f c = OK tc),
        code_tail ofs tf tc ->
      return_address_offset f c (Int.repr ofs)
  | return_address_offset_fail_tf:
      forall f c m
        (TF: transf_function f = Error m),
      return_address_offset f c Int.zero
  | return_address_offset_fail_tc:
      forall f c m
        (TC: transl_code f c = Error m),
      return_address_offset f c Int.zero.

Lemma code_tail_length:
  forall n c1 c2,
  code_tail n c1 c2 -> Z_of_nat (length c1) = n + Z_of_nat (length c2).
Proof.
  induction 1; simpl length; try rewrite inj_S; omega.
Qed.

Lemma code_tail_determinate:
  forall f c n1 n2
   (X: code_tail n1 f c)
   (Y: code_tail n2 f c),
    n1 = n2.
Proof.
  intros; eapply code_tail_length in X;
  eapply code_tail_length in Y; omega.
Qed.

Lemma return_address_offset_determinate:
  forall f c n1 n2,
    return_address_offset f c n1 ->
    return_address_offset f c n2 ->
    n1 = n2.
Proof.
   inversion_clear 1; inversion_clear 1;
     try (rewrite TF in *); try (rewrite TC in *); clarify.
   eby f_equal; eapply code_tail_determinate.
Qed.

(** We now show that such an offset always exists if the Mach code [c]
  is a suffix of [f.(fn_code)].  This holds because the translation
  from Mach to Asm is compositional: each Mach instruction becomes
  zero, one or several Asm instructions, but the order of instructions
  is preserved. *)

Lemma is_tail_code_tail:
  forall c1 c2, is_tail c1 c2 -> exists ofs, code_tail ofs c2 c1.
Proof.
  induction 1. exists 0; constructor.
  destruct IHis_tail as [ofs CT]. exists (ofs + 1); constructor; auto.
Qed.

(* Lemma is_tail_app: forall A (k: list A) k', is_tail k' (k ++ k'). *)
(* Proof. induction k; intros; constructor; auto. Qed. *)

Hint Resolve is_tail_refl: ppcretaddr.
(* Hint Resolve is_tail_app: retaddr. *)

(* Ltac IsTail := *)
(*   auto with retaddr; *)
(*   match goal with *)
(*   | [ |- is_tail _ (_ :: _) ] => constructor; IsTail *)
(*   | [ |- is_tail _ (match ?x with true => _ | false => _ end) ] => destruct x; IsTail *)
(*   | [ |- is_tail _ (match ?x with left _ => _ | right _ => _ end) ] => destruct x; IsTail *)
(*   | [ |- is_tail _ (match ?x with nil => _ | _ :: _ => _ end) ] => destruct x; IsTail *)
(*   | [ |- is_tail _ (match ?x with Tint => _ | Tfloat => _ end) ] => destruct x; IsTail *)
(*   | [ |- is_tail _ (?f _ _ _ _ _ _ ?k) ] => apply is_tail_trans with k; IsTail *)
(*   | [ |- is_tail _ (?f _ _ _ _ _ ?k) ] => apply is_tail_trans with k; IsTail *)
(*   | [ |- is_tail _ (?f _ _ _ _ ?k) ] => apply is_tail_trans with k; IsTail *)
(*   | [ |- is_tail _ (?f _ _ _ ?k) ] => apply is_tail_trans with k; IsTail *)
(*   | [ |- is_tail _ (?f _ _ ?k) ] => apply is_tail_trans with k; IsTail *)
(*   | _ => idtac *)
(*   end. *)

Ltac IsTail :=
  eauto with ppcretaddr;
  match goal with
  | [ |- is_tail _ (_ :: _) ] => constructor; IsTail
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: OK _ = OK _ |- _ ] => inversion H; subst; IsTail
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H; IsTail
  | [ H: (if ?x then _ else _) = OK _ |- _ ] => destruct x; IsTail
  | [ H: match ?x with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct x; IsTail
  | [ H: match ?x with Some _ => _ | None => _ end = OK _ |- _ ] => destruct x; IsTail
  | _ => idtac
  end.

(* Lemma load_fp_stack_tail: *)
(*   forall f k c, OK (load_fp_stack f k) = OK c -> is_tail k c. *)
(* Proof. *)
(*   unfold load_fp_stack; intros; IsTail. *)
(* Qed. *)

(* Lemma save_fp_stack_tail: *)
(*   forall f k c, OK (save_fp_stack f k) = OK c -> is_tail k c. *)
(* Proof. *)
(*   unfold save_fp_stack; intros; IsTail. *)
(* Qed. *)

(* Hint Resolve load_fp_stack_tail save_fp_stack_tail: ppcretaddr. *)

Lemma mk_mov_tail:
  forall rd rs k c, mk_mov rd rs k = OK c -> is_tail k c.
Proof.
  unfold mk_mov; intros; IsTail; destruct rs; IsTail; destruct rd; IsTail.
Qed.

Lemma mk_shift_tail:
  forall si r1 r2 k c, mk_shift si r1 r2 k = OK c -> is_tail k c.
Proof.
  unfold mk_shift; intros; IsTail.
Qed.

Lemma mk_div_tail:
  forall i di r1 r2 k c, mk_div i di r1 r2 k = OK c -> is_tail k c.
Proof.
  unfold mk_div; intros; IsTail.
Qed.

Lemma mk_mod_tail:
  forall i di r1 r2 k c, mk_mod i di r1 r2 k = OK c -> is_tail k c.
Proof.
  unfold mk_mod; intros; IsTail.
Qed.

Lemma mk_shrximm_tail:
  forall r n k c, mk_shrximm r n k = OK c -> is_tail k c.
Proof.
  unfold mk_shrximm; intros; IsTail.
Qed.

Lemma mk_intconv_tail:
  forall ex rd rs k c, mk_intconv ex rd rs k = OK c -> is_tail k c.
Proof.
  unfold mk_intconv; intros; IsTail.
Qed.

Lemma mk_smallstore_tail:
  forall ex addr rs k c, mk_smallstore ex addr rs k = OK c -> is_tail k c.
Proof.
  unfold mk_smallstore; intros; IsTail.
Qed.

Lemma loadind_tail:
  forall base ofs ty dst k c, loadind base ofs ty dst k = OK c -> is_tail k c.
Proof.
  unfold loadind; intros. destruct ty; IsTail. destruct (preg_of dst); IsTail.
Qed.

Lemma storeind_tail:
  forall src base ofs ty k c, storeind src base ofs ty k = OK c -> is_tail k c.
Proof.
  unfold storeind; intros. destruct ty; IsTail. destruct (preg_of src); IsTail.
Qed.

Hint Resolve mk_mov_tail mk_shift_tail mk_div_tail mk_mod_tail mk_shrximm_tail
             mk_intconv_tail mk_smallstore_tail loadind_tail storeind_tail : ppcretaddr.

Lemma transl_cond_tail:
  forall cond args k c, transl_cond cond args k = OK c -> is_tail k c.
Proof.
  unfold transl_cond; intros. destruct cond; IsTail; destruct (Int.eq_dec i Int.zero); IsTail.
Qed.

Lemma transl_op_tail:
  forall op args res k c, transl_op op args res k = OK c -> is_tail k c.
Proof.
  unfold transl_op; intros. destruct op; IsTail. 
  eapply is_tail_trans. 2: eapply transl_cond_tail; eauto. IsTail.
Qed.

Lemma transl_aop_tail:
  forall aop args res k c, transl_aop aop args res k = OK c -> is_tail k c.
Proof.
  unfold transl_aop; intros. destruct aop.
  destruct args; inv H. destruct args; inv H1. destruct args; inv H0. destruct args; inv H1. 
  monadInv H0. repeat destruct ireg_eq; try inversion EQ6; IsTail.   
  IsTail.
Qed.

Lemma transl_load_tail:
  forall chunk addr args dest k c, transl_load chunk addr args dest k = OK c -> is_tail k c.
Proof.
  unfold transl_load; intros. IsTail. destruct chunk; IsTail. 
Qed.

Lemma transl_store_tail:
  forall chunk addr args src k c, transl_store chunk addr args src k = OK c -> is_tail k c.
Proof.
  unfold transl_store; intros. IsTail. destruct chunk; IsTail. 
Qed.

Lemma transl_instr_tail:
  forall f i k c, transl_instr f i k = OK c -> is_tail k c.
Proof.
  unfold transl_instr; intros. destruct i; IsTail.
  eapply transl_op_tail; eauto.
  eapply transl_load_tail; eauto.
  eapply transl_store_tail; eauto.
  destruct s0; IsTail.
  eapply is_tail_trans. 2: eapply transl_cond_tail; eauto. IsTail.
  eapply transl_aop_tail; eauto. 
Qed.

Lemma transl_code_tail: 
  forall f c1 c2, is_tail c1 c2 ->
  forall tc1 tc2, transl_code f c1 = OK tc1 -> transl_code f c2 = OK tc2 ->
  is_tail tc1 tc2.
Proof.
  induction 1; simpl; intros.
  replace tc2 with tc1 by congruence. constructor.
  IsTail. apply is_tail_trans with x. eauto. eapply transl_instr_tail; eauto.
Qed.

Lemma return_address_exists:
  forall f c, is_tail c f.(fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros.
  caseEq (transf_function f). intros [sig tf] TF. 
    caseEq (transl_code f c). intros tc TC.  
      assert (is_tail tc tf). 
      unfold transf_function in *. monadInv TF. 
      destruct (zlt (code_size x) Int.max_unsigned); monadInv EQ0.
      IsTail. eapply transl_code_tail; eauto. 
      destruct (is_tail_code_tail _ _ H0) as [ofs A].
      eby eexists; eapply return_address_offset_intro.
    intros. eexists.
    eby eapply return_address_offset_fail_tc.
  intros. eexists.
  eby eapply return_address_offset_fail_tf.
Qed.
