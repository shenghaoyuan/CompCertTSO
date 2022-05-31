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

(** Correctness proof for x86 generation: auxiliary results. *)

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
Require Import Locations.
Require Import Simulations.
Require Import TSOmachine.
Require Import Mach.
Require Import Machconcr.
Require Import Machtyping.
Require Import Asm.
Require Import Asmgen.
Require Import Asmgenretaddr.
Require Import Conventions.
Require Import Errors.
Require Import Libtactics.



(** * Correspondence between Mach registers and x86 registers *)

Hint Extern 2 (_ <> _) => discriminate: x86gen.

(** Mapping from x86 registers to PPC registers. *)

Lemma preg_of_injective:
  forall r1 r2, preg_of r1 = preg_of r2 -> r1 = r2.
Proof.
  by destruct r1; destruct r2.
Qed.

Lemma preg_of_not_ESP:
  forall r, preg_of r <> ESP.
Proof.
  by destruct r. 
Qed.

Lemma preg_of_not_PC:
  forall r, preg_of r <> EIP.
Proof.
  by destruct r.
Qed.

Lemma preg_of_not_EFLAG:
  forall r f, preg_of r <> EFLAG f.
Proof.
  by destruct r; destruct f.
Qed.

Hint Resolve preg_of_not_ESP preg_of_not_PC preg_of_not_EFLAG: x86gen.

Lemma ireg_of_eq:
  forall r r', ireg_of r = OK r' -> preg_of r = IR r'.
Proof.
  unfold ireg_of; intros. destruct (preg_of r); inv H; auto.
Qed.

Lemma freg_of_eq:
  forall r r', freg_of r = OK r' -> preg_of r = FR r'.
Proof.
  unfold freg_of; intros. destruct (preg_of r); inv H; auto.
Qed.

(** Important registers *)

Definition important_preg (r: preg) : bool :=
  match r with
  | EIP => false
  | IR _ => true
  | FR _ => true
  | ST0 => true
  | EFLAG _ => false
  end.

Lemma preg_of_important:
  forall r, important_preg (preg_of r) = true.
Proof.
  by destruct r.
Qed.

Lemma important_diff:
  forall r r',
  important_preg r = true -> important_preg r' = false -> r <> r'.
Proof.
  congruence.
Qed.

Hint Resolve important_diff: x86gen.


(** Non-temporary registers *)

Definition nontemp_preg (r: preg) : bool :=
  match r with
  | EIP => false
  | IR EAX => false
  | IR ECX => false
  | IR EDX => false
  | IR _ => true
  | FR XMM6 => false
  | FR XMM7 => false
  | FR _ => true
  | ST0 => false
  | EFLAG _ => false
  end.

Lemma nontemp_diff:
  forall r r',
  nontemp_preg r = true -> nontemp_preg r' = false -> r <> r'.
Proof.
  congruence.
Qed.

Hint Resolve nontemp_diff: x86gen.

Remark undef_regs_1:
  forall l ms r, ms r = Vundef -> Mach.undef_regs l ms r = Vundef.
Proof.
  induction l; simpl; intros. auto. apply IHl. unfold Regmap.set.
  destruct (RegEq.eq r a); congruence.
Qed.

Remark undef_regs_2:
  forall l ms r, In r l -> Mach.undef_regs l ms r = Vundef.
Proof.
  induction l; simpl; intros. contradiction. 
  destruct H. subst. apply undef_regs_1. apply Regmap.gss.
  auto.
Qed.

Remark undef_regs_3:
  forall l ms r, ~In r l -> Mach.undef_regs l ms r = ms r.
Proof.
  induction l; simpl; intros. auto.
  rewrite IHl. apply Regmap.gso. intuition. intuition.
Qed.


(** * Useful properties of [nextinstr] *)

Lemma nextinstr_inv:
  forall r rs,
  r <> EIP ->
  (nextinstr rs)#r = rs#r.
Proof.
  by intros; apply Pregmap.gso; red; intro; subst.
Qed.

Lemma nextinstr_inv_nontemp:
  forall r rs,
  nontemp_preg r = true ->
  (nextinstr rs)#r = rs#r.
Proof.
  by intros; apply nextinstr_inv; red; intro; subst.
Qed.

Lemma nextinstr_inv_important:
  forall r rs,
  important_preg r = true ->
  (nextinstr rs)#r = rs#r.
Proof.
  by intros; apply nextinstr_inv; red; intro; subst.
Qed.

Lemma nextinstr_set_preg:
  forall rs m v,
  (nextinstr (rs#(preg_of m) <- v))#EIP = Val.add rs#EIP Vone.
Proof.
  intros. unfold nextinstr. rewrite Pregmap.gss. 
  rewrite Pregmap.gso. auto. apply sym_not_eq. apply preg_of_not_PC. 
Qed.

Lemma nextinstr_commute: 
  forall rs r c, r <> EIP -> (nextinstr rs) # r <- c = nextinstr rs # r <- c.
Proof.
  intros; unfold nextinstr.
  rewrite Pregmap.gso; auto. 
  apply extensionality; intro x.
  destruct (preg_eq x r); [subst; rewrite Pregmap.gss, Pregmap.gso, Pregmap.gss; try done|].
  rewrite Pregmap.gso; [|done].
  destruct (preg_eq x EIP); subst; [by rewrite !Pregmap.gss|]. 
  by rewrite !Pregmap.gso.
Qed.
Hint Resolve nextinstr_commute: x86gen.


(*
Lemma add_zero:
  forall v, Val.has_type v Tint -> Val.add Vzero v = v.
Proof.
  unfold Vzero; simpl; destruct v; try done.
  by rewrite Int.add_commut, Int.add_zero.
  by rewrite Ptr.add_zero_r.
Qed. *)

(** Agreement between Mach register sets and IA32 register sets. *)

Record agree (ms: Mach.regset) (sp: val) (rs: Asm.regset) : Prop := mkagree {
  agree_sp: rs#ESP = sp;
  agree_sp_def: sp <> Vundef;
  agree_mregs: forall r: mreg, Val.lessdef (ms r) (rs#(preg_of r))
}.

Lemma preg_val:
  forall ms sp rs r,
  agree ms sp rs -> Val.lessdef (ms r) rs#(preg_of r).
Proof.
  intros. destruct H. auto.
Qed.

Lemma preg_vals:
  forall ms sp rs, agree ms sp rs ->
  forall l, Val.lessdef_list (map ms l) (map rs (map preg_of l)).
Proof.
  induction l; simpl. constructor. constructor. eapply preg_val; eauto. auto.
Qed.

Lemma ireg_val:
  forall ms sp rs r r',
  agree ms sp rs ->
  ireg_of r = OK r' ->
  Val.lessdef (ms r) rs#r'.
Proof.
  intros. rewrite <- (ireg_of_eq _ _ H0). eapply preg_val; eauto.
Qed.

Lemma freg_val:
  forall ms sp rs r r',
  agree ms sp rs ->
  freg_of r = OK r' ->
  Val.lessdef (ms r) (rs#r').
Proof.
  intros. rewrite <- (freg_of_eq _ _ H0). eapply preg_val; eauto.
Qed.

Lemma sp_val:
  forall ms sp rs,
  agree ms sp rs ->
  sp = rs#ESP.
Proof.
  intros. destruct H; auto.
Qed.

Hint Resolve preg_val ireg_val freg_val sp_val: x86gen.

Lemma agree_exten:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r, important_preg r = true -> rs'#r = rs#r) ->
  agree ms sp rs'.
Proof.
  intros. destruct H. split. 
  rewrite H0; auto. auto.
  intros. rewrite H0; auto. apply preg_of_important.
Qed.

(** Preservation of register agreement under various assignments. *)

Lemma agree_set_mreg:
  forall ms sp rs r v rs',
  agree ms sp rs ->
  Val.lessdef v (rs'#(preg_of r)) ->
  (forall r', important_preg r' = true -> r' <> preg_of r -> rs'#r' = rs#r') ->
  agree (Regmap.set r v ms) sp rs'.
Proof.
  intros. destruct H. split.
  rewrite H1; auto. apply sym_not_equal. apply preg_of_not_ESP.
  auto.
  intros. unfold Regmap.set. destruct (RegEq.eq r0 r). congruence. 
  rewrite H1. auto. apply preg_of_important.
  red; intros; elim n. eapply preg_of_injective; eauto.
Qed.

Lemma agree_set_other:
  forall ms sp rs r v,
  agree ms sp rs ->
  important_preg r = false ->
  agree ms sp (rs#r <- v).
Proof.
  intros. apply agree_exten with rs. auto.
  intros. apply Pregmap.gso. congruence.
Qed.

Lemma agree_nextinstr:
  forall ms sp rs,
  agree ms sp rs -> agree ms sp (nextinstr rs).
Proof.
  by intros; apply agree_set_other.
Qed.

Lemma agree_undef_unimportant_regs:
  forall ms sp rl rs,
  agree ms sp rs ->
  (forall r, In r rl -> important_preg r = false) ->
  agree ms sp (undef_regs rl rs).
Proof.
  induction rl; simpl; intros. auto.
  apply IHrl. apply agree_exten with rs; auto.
  intros. apply Pregmap.gso. red; intros; subst.
  assert (important_preg a = false) by auto. congruence.
  auto.
Qed.

Lemma agree_exten_temps:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r, nontemp_preg r = true -> rs'#r = rs#r) ->
  agree (undef_temps ms) sp rs'.
Proof.
  intros. destruct H. split. 
  rewrite H0; auto. auto. 
  intros. unfold undef_temps. 
  destruct (In_dec mreg_eq r (int_temporaries ++ float_temporaries)).
  rewrite undef_regs_2; auto. 
  rewrite undef_regs_3; auto. rewrite H0; auto.
  simpl in n. destruct r; auto; intuition.
Qed.

Lemma agree_set_undef_mreg:
  forall ms sp rs r v rs',
  agree ms sp rs ->
  Val.lessdef v (rs'#(preg_of r)) ->
  (forall r', nontemp_preg r' = true -> r' <> preg_of r -> rs'#r' = rs#r') ->
  agree (Regmap.set r v (undef_temps ms)) sp rs'.
Proof.
  intros. apply agree_set_mreg with (rs'#(preg_of r) <- (rs#(preg_of r))); auto.
  eapply agree_exten_temps; eauto. 
  intros. unfold Pregmap.set. destruct (PregEq.eq r0 (preg_of r)). 
  congruence. auto. 
  intros. rewrite Pregmap.gso; auto. 
Qed.

(** A few useful lemmas *)

Lemma exec_pexstorei_split:
 forall ge rs rm v stkr (NE: rm <> Xr ESP),
     exec_pex_instr ge (State rs (XPEstorei rm v) stkr) =
     write_int_rm ge rs rm v stkr.
Proof.
  by destruct rm as [[]|].
Qed.

Lemma write_eflag_EIP:
  forall v f rs,
    (write_eflag f v rs) EIP = rs EIP.
Proof.
  by intros; apply Pregmap.gso. 
Qed.

Lemma write_eflag_nontemp:
  forall v f rs r,
    nontemp_preg r = true ->
    (write_eflag f v rs) r = rs r.
Proof.
  by intros; apply Pregmap.gso; intro; clarify. 
Qed.

Lemma write_eflag_important:
  forall v f rs r,
    important_preg r = true ->
    (write_eflag f v rs) r = rs r.
Proof.
  by intros; apply Pregmap.gso; intro; clarify. 
Qed.

Lemma agree_eflag:
  forall ms sp f v rs,
    agree ms sp rs ->
    agree ms sp (write_eflag f v rs).
Proof.
  intros; unfold write_eflag. 
  eapply agree_exten; eauto.
  by intros; apply Pregmap.gso; intro; clarify. 
Qed.

(** * Properties of control flow *)

Lemma find_instr_in:
  forall c pos i,
  find_instr pos c = Some i -> In i c.
Proof.
  induction c; simpl; try done.
  intros until i. case zeq; intros; clarify; eauto.
Qed.

Lemma find_instr_tail:
  forall c1 i c2 pos,
  code_tail pos c1 (i :: c2) ->
  find_instr pos c1 = Some i.
Proof.
  induction c1; simpl; intros.
  inv H.
  destruct (zeq pos 0). subst pos.
  inv H. auto. generalize (code_tail_pos _ _ _ H4). intro. omegaContradiction.
  inv H. congruence. replace (pos0 + 1 - 1) with pos0 by omega.
  eauto. 
Qed.

Remark code_size_pos:
  forall fn, code_size fn >= 0.
Proof.
  induction fn; simpl; omega.
Qed.

Remark code_tail_bounds: 
  forall fn ofs i c,
  code_tail ofs fn (i :: c) -> 0 <= ofs < code_size fn.
Proof.
  cut (forall ofs fn c, code_tail ofs fn c ->
          forall i c', c = i :: c' -> 0 <= ofs < code_size fn); [eauto|].
  induction 1; intros; clarify; simpl.
    by generalize (code_size_pos c'); omega.
  by generalize (IHcode_tail _ _ (refl_equal _)); omega.
Qed.

Lemma code_tail_next:
  forall fn ofs i c,
  code_tail ofs fn (i :: c) ->
  code_tail (ofs + 1) fn c.
Proof.
  cut (forall ofs fn c, code_tail ofs fn c ->
         forall i c', c = i :: c' -> code_tail (ofs + 1) fn c'); [eauto|].
  induction 1; intros; clarify; vauto.
  constructor; eauto.
Qed.

Lemma code_tail_next_int:
  forall fn ofs i c,
  code_size fn <= Int.max_unsigned ->
  code_tail (Int.unsigned ofs) fn (i :: c) ->
  code_tail (Int.unsigned (Int.add ofs Int.one)) fn c.
Proof.
  intros. rewrite Int.add_unsigned. 
  change (Int.unsigned Int.one) with 1.
  rewrite Int.unsigned_repr. apply code_tail_next with i; auto.
  generalize (code_tail_bounds _ _ _ _ H0). omega. 
Qed.

Hint Resolve code_tail_next_int : x86gen.


Remark code_tail_no_bigger:
  forall {pos c1 c2}, code_tail pos c1 c2 -> (length c2 <= length c1)%nat.
Proof.
  induction 1; simpl; omega.
Qed.

Remark code_tail_unique:
  forall {fn c pos pos'},
  code_tail pos fn c -> code_tail pos' fn c -> pos = pos'.
Proof.
  induction fn; intros until pos'; intros ITA CT; inv ITA; inv CT; auto.
  generalize (code_tail_no_bigger H3); simpl; intro; omega.
  generalize (code_tail_no_bigger H3); simpl; intro; omega.
  f_equal. eauto.
Qed.

(** The [find_label] function returns the code tail starting at the
  given label.  A connection with [code_tail] is then established. *)

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some c' else find_label lbl c'
  end.

Lemma label_pos_code_tail:
  forall lbl c pos c',
  find_label lbl c = Some c' ->
  exists pos',
  label_pos lbl pos c = Some pos'
  /\ code_tail (pos' - pos) c c'
  /\ pos < pos' <= pos + code_size c.
Proof.
  induction c; simpl; intros; try done.
  destruct (is_label lbl a); clarify.
    exists (pos + 1); split; try done; split.
      by (replace (pos + 1 - pos) with (0 + 1) by omega); vauto.  
    pose proof (code_size_pos c'); omega.
  pose proof (IHc (pos + 1) c' H) as [pos' [A [B C]]].
  exists pos'; split; try done; split; [|omega].
  replace (pos' - pos) with ((pos' - (pos + 1)) + 1) by omega.
  by constructor.
Qed.

(** The following lemmas show that the translation from Mach to Asm
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ Asm instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- Asm instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that Asm constructor
  functions do not introduce new labels.
*)

Section TRANSL_LABEL.

Variable lbl: label.

Remark mk_mov_label:
  forall rd rs k c, mk_mov rd rs k = OK c -> find_label lbl c = find_label lbl k.
Proof.
  unfold mk_mov; intros. 
  destruct rd; try discriminate; destruct rs; inv H; auto.
Qed.

Remark mk_shift_label:
  forall i r1 r2 k c, mk_shift i r1 r2 k = OK c -> 
  find_label lbl c = find_label lbl k.
Proof.
  unfold mk_shift; intros.
  destruct (ireg_eq r2 ECX); monadInv H; simpl; auto. 
Qed.

Remark mk_div_label:
  forall i1 i2 r1 r2 k c, mk_div i1 i2 r1 r2 k = OK c -> 
  is_label lbl i1 = false ->
  find_label lbl c = find_label lbl k.
Proof.
  unfold mk_div; intros.
  destruct (ireg_eq r1 EAX).
  destruct (ireg_eq r2 EDX); monadInv H; simpl; rewrite H0; auto.
  destruct (ireg_eq r2 EAX); monadInv H; simpl; rewrite H0; auto.
Qed.

Remark mk_mod_label:
  forall i1 i2 r1 r2 k c, mk_mod i1 i2 r1 r2 k = OK c -> 
  is_label lbl i1 = false ->
  find_label lbl c = find_label lbl k.
Proof.
  unfold mk_mod; intros.
  destruct (ireg_eq r1 EAX).
  destruct (ireg_eq r2 EDX); monadInv H; simpl; rewrite H0; auto.
  destruct (ireg_eq r2 EDX); monadInv H; simpl; rewrite H0; auto.
Qed.

Remark mk_shrximm_label:
  forall r n k c, mk_shrximm r n k = OK c -> find_label lbl c = find_label lbl k.
Proof.
  intros. monadInv H; auto.
Qed.

Remark mk_intconv_label:
  forall e r1 r2 k c, mk_intconv e r1 r2 k = OK c -> 
  find_label lbl c = find_label lbl k.
Proof.
  unfold mk_intconv; intros. destruct (get_low_ireg r2); inv H; simpl; auto. 
Qed.

Remark mk_smallstore_label:
  forall sz addr r k c, mk_smallstore sz addr r k = OK c -> 
  find_label lbl c = find_label lbl k.
Proof.
  unfold mk_smallstore; intros. destruct (get_low_ireg r); monadInv H; simpl; auto.
Qed.

Remark loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c ->
  find_label lbl c = find_label lbl k.
Proof.
  unfold loadind; intros. destruct ty. 
  monadInv H; auto. 
  destruct (preg_of dst); inv H; auto.
Qed.

Remark storeind_label:
  forall base ofs ty src k c,
  storeind src base ofs ty k = OK c ->
  find_label lbl c = find_label lbl k.
Proof.
  unfold storeind; intros. destruct ty. 
  monadInv H; auto. 
  destruct (preg_of src); inv H; auto.
Qed.

Ltac ArgsInv :=
  match goal with
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: match ?args with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct args; ArgsInv
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H; ArgsInv
  | _ => idtac
  end.

Remark transl_cond_label:
  forall cond args k c,
  transl_cond cond args k = OK c ->
  find_label lbl c = find_label lbl k.
Proof.
  unfold transl_cond; intros. 
  destruct cond; ArgsInv; auto. 
  destruct (Int.eq_dec i Int.zero); auto.
  destruct c0; auto.
  destruct c0; auto.
Qed.

Remark transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c ->
  find_label lbl c = find_label lbl k.
Proof.
  unfold transl_op; intros. destruct op; ArgsInv; auto. 
  eapply mk_mov_label; eauto.
  eapply mk_intconv_label; eauto.
  eapply mk_intconv_label; eauto.
  eapply mk_intconv_label; eauto.
  eapply mk_intconv_label; eauto.
  eapply mk_div_label; eauto.
  eapply mk_div_label; eauto.
  eapply mk_mod_label; eauto.
  eapply mk_mod_label; eauto.
  eapply mk_shift_label; eauto.
  eapply mk_shift_label; eauto.
  eapply mk_shrximm_label; eauto.
  eapply mk_shift_label; eauto.
  eapply trans_eq. eapply transl_cond_label; eauto. auto.
Qed.

Remark transl_aop_label:
  forall aop args r k c,
  transl_aop aop args r k = OK c ->
  find_label lbl c = find_label lbl k.
Proof.
  unfold transl_aop; intros.
  destruct aop; ArgsInv; auto.
  by repeat destruct ireg_eq; monadInv EQ6. 
Qed.

Remark transl_load_label:
  forall chunk addr args dest k c,
  transl_load chunk addr args dest k = OK c ->
  find_label lbl c = find_label lbl k.
Proof.
  intros. monadInv H. destruct chunk; monadInv EQ0; auto. 
Qed.

Remark transl_store_label:
  forall chunk addr args src k c,
  transl_store chunk addr args src k = OK c ->
  find_label lbl c = find_label lbl k.
Proof.
  intros. monadInv H. destruct chunk; monadInv EQ0; auto; eapply mk_smallstore_label; eauto.
Qed.

Lemma transl_instr_label:
  forall f i k c,
  transl_instr f i k = OK c ->
  find_label lbl c = if Mach.is_label lbl i then Some k else find_label lbl k.
Proof.
  intros; generalize (Mach.is_label_correct lbl i). 
  case (Mach.is_label lbl i); intro.
    by subst i; monadInv H; simpl; rewrite peq_true.
Opaque loadind.
  destruct i; simpl in H; try by (monadInv H; auto).
  - eapply loadind_label; eauto.
  - eapply storeind_label; eauto.
  - eapply loadind_label; eauto.
  - eapply transl_op_label; eauto.
  - eapply transl_load_label; eauto.
  - eapply transl_store_label; eauto.
  - destruct s0; monadInv H; auto.
  - monadInv H; simpl; destruct (peq lbl l); [congruence | auto]. 
  - eapply trans_eq; [eapply transl_cond_label|]; eauto.
  - eapply transl_aop_label; eauto.
Qed.

Lemma transl_code_label:
  forall f c tc,
  transl_code f c = OK tc ->
  match Mach.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_code f c' = OK tc'
  end.
Proof.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H. rewrite (transl_instr_label _ _ _ _ EQ0). 
  destruct (Mach.is_label lbl a). exists x; auto. apply IHc. auto. 
Qed.

Lemma transl_find_label:
  forall f sig tf,
  transf_function f = OK (sig,tf) ->
  match Mach.find_label lbl f.(fn_code) with
  | None => find_label lbl tf = None
  | Some c => exists tc, find_label lbl tf = Some tc /\ transl_code f c = OK tc
  end.
Proof.
  intros. monadInv H. destruct (zlt (code_size x) Int.max_unsigned); inv EQ0.
  simpl. apply transl_code_label; auto. 
Qed.

End TRANSL_LABEL.
