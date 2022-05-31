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

(** Correctness proof for RTL generation. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Switch.
Require Import Registers.
Require Import Cminor.
Require Import Op.
Require Import Errors.
Require Conventions.
Require Import CminorSel.
Require Import CminorP.
Require Import RTL.
Require Import RTLgen.
Require Import RTLgenspec.
Require Import Integers.
Require Import Memcomp Traces.
Require Import Simulations MCsimulation.
Require Import Smallstep.
Require Setoid.
Require Import Libtactics.


(** * Correspondence between Cminor environments and RTL register sets *)

(** A compilation environment (mapping) is well-formed if
  the following properties hold:
- Two distinct Cminor local variables are mapped to distinct pseudo-registers.
- A Cminor local variable and a let-bound variable are mapped to
  distinct pseudo-registers.
*)

Record map_wf (m: mapping) : Prop :=
  mk_map_wf {
    map_wf_inj:
      (forall id1 id2 r,
         m.(map_vars)!id1 = Some r -> m.(map_vars)!id2 = Some r -> id1 = id2);
     map_wf_disj:
      (forall id r,
         m.(map_vars)!id = Some r -> In r m.(map_letvars) -> False)
  }.

Lemma init_mapping_wf:
  map_wf init_mapping.
Proof.
  unfold init_mapping; split; simpl.
  intros until r. rewrite PTree.gempty. congruence.
  tauto.
Qed.

Lemma add_var_wf:
  forall s1 s2 map name r map' i,
  add_var map name s1 = OK (r,map') s2 i -> 
  map_wf map -> map_valid map s1 -> map_wf map'.
Proof.
  intros. monadInv H. 
  apply mk_map_wf; simpl.
  intros until r0. repeat rewrite PTree.gsspec.
  destruct (peq id1 name); destruct (peq id2 name).
  congruence.
  intros. inv H. elimtype False. 
  apply valid_fresh_absurd with r0 s1. 
  apply H1. left; exists id2; auto.
  eauto with rtlg.
  intros. inv H2. elimtype False. 
  apply valid_fresh_absurd with r0 s1. 
  apply H1. left; exists id1; auto.
  eauto with rtlg.
  inv H0. eauto.
  intros until r0. rewrite PTree.gsspec.
  destruct (peq id name). 
  intros. inv H.
  apply valid_fresh_absurd with r0 s1.
  apply H1. right; auto.
  eauto with rtlg.
  inv H0; eauto.
Qed.

Lemma add_vars_wf:
  forall names s1 s2 map map' rl i,
  add_vars map names s1 = OK (rl,map') s2 i ->
  map_wf map -> map_valid map s1 -> map_wf map'.
Proof.
  induction names; simpl; intros; monadInv H. 
  auto.
  exploit add_vars_valid; eauto. intros [A B].
  eapply add_var_wf; eauto.
Qed.

(** An RTL register environment matches a CminorSel local environment and
  let-environment if the value of every local or let-bound variable in
  the CminorSel environments is identical to the value of the
  corresponding pseudo-register in the RTL register environment. *)

Record match_env
      (map: mapping) (e: env) (rs: regset) : Prop :=
  mk_match_env {
    me_vars:
      (forall id v,
         e!id = Some v -> exists r, map.(map_vars)!id = Some r /\ rs#r = v)
  }.

Lemma match_env_find_var:
  forall map e rs id v r,
  match_env map e rs ->
  e!id = Some v ->
  map.(map_vars)!id = Some r ->
  rs#r = v.
Proof.
  intros. exploit me_vars; eauto. intros [r' [EQ' RS]].
  replace r with r'. auto. congruence.
Qed.

(*
Lemma match_env_find_letvar:
  forall map e le rs idx v r,
  match_env map e le rs ->
  List.nth_error le idx = Some v ->
  List.nth_error map.(map_letvars) idx = Some r ->
  rs#r = v.
Proof.
  intros. exploit me_letvars; eauto. intros.
  rewrite <- H2 in H0. rewrite list_map_nth in H0. 
  change reg with positive in H1. rewrite H1 in H0. 
  simpl in H0. congruence.
Qed.
*)

Lemma match_env_invariant:
  forall map e rs rs',
  match_env map e rs ->
  (forall r, (reg_in_map map r) -> rs'#r = rs#r) ->
  match_env map e rs'.
Proof.
  intros. inversion H. apply mk_match_env.
  intros. exploit me_vars0; eauto. intros [r [A B]].
  exists r; split. auto. rewrite H0; auto. left; exists id; auto.
Qed.

(** Matching between environments is preserved when an unmapped register
  (not corresponding to any Cminor variable) is assigned in the RTL
  execution. *)

Lemma match_env_update_temp:
  forall map e rs r v,
  match_env map e rs ->
  ~(reg_in_map map r) ->
  match_env map e (rs#r <- v).
Proof.
  intros. apply match_env_invariant with rs; auto.
  intros. case (Reg.eq r r0); intro. 
  subst r0; contradiction.
  apply Regmap.gso; auto.
Qed.
Hint Resolve match_env_update_temp: rtlg.

(** Matching between environments is preserved by simultaneous
  assignment to a Cminor local variable (in the Cminor environments)
  and to the corresponding RTL pseudo-register (in the RTL register
  environment). *)

Lemma match_env_update_var:
  forall map e rs id r v,
  map_wf map ->
  map.(map_vars)!id = Some r ->
  match_env map e rs ->
  match_env map (PTree.set id v e) (rs#r <- v).
Proof.
  intros. inversion H. inversion H1. apply mk_match_env.
  intros id' v'. rewrite PTree.gsspec. destruct (peq id' id); intros.
  subst id'. inv H2. exists r; split. auto. apply PMap.gss.
  exploit me_vars0; eauto. intros [r' [A B]].
  exists r'; split. auto. rewrite PMap.gso; auto.
  red; intros. subst r'.  elim n.  eauto.
Qed.

(*
Lemma match_env_bind_letvar:
  forall map e rs r v,
  match_env map e rs ->
  rs#r = v ->
  match_env (add_letvar map r) e (v :: le) rs.
Proof.
  intros. inv H. unfold add_letvar. apply mk_match_env; simpl; auto.
Qed.

Lemma match_env_unbind_letvar:
  forall map e le rs r v,
  match_env (add_letvar map r) e (v :: le) rs ->
  match_env map e le rs.
Proof.
  unfold add_letvar; intros. inv H. simpl in *. 
  constructor. auto. congruence.
Qed.
*)

Lemma match_env_empty:
  forall map,
  match_env map (PTree.empty val) (Regmap.init Vundef).
Proof.
  intros. apply mk_match_env.
  intros. rewrite PTree.gempty in H. discriminate.
Qed.

Lemma match_env_update_dest:
  forall map e rs dst r v,
  map_wf map ->
  reg_map_ok map r dst ->
  match_env map e rs ->
  match_env map (set_optvar dst v e) (rs#r <- v).
Proof.
  intros. inv H0; simpl. 
  eapply match_env_update_temp; eauto. 
  eapply match_env_update_var; eauto.
Qed.
Hint Resolve match_env_update_dest: rtlg.

(** The assignment of function arguments to local variables (on the Cminor
  side) and pseudo-registers (on the RTL side) preserves matching
  between environments. *)


Lemma match_set_params_init_regs:
  forall il rl s1 map2 s2 vl i,
  add_vars init_mapping il s1 = OK (rl, map2) s2 i ->
  match_env map2 (set_params vl il) (init_regs vl rl)
  /\ (forall r, reg_fresh r s2 -> (init_regs vl rl)#r = Vundef).
Proof.
  induction il; intros.

  inv H. split. apply match_env_empty. auto. intros. 
  simpl. apply Regmap.gi.

  monadInv H. simpl.
  exploit add_vars_valid; eauto. apply init_mapping_valid. intros [A B].
  exploit add_var_valid; eauto. intros [A' B']. clear B'.
  monadInv EQ1. 
  destruct vl as [ | v1 vs].
  (* vl = nil *)
  destruct (IHil _ _ _ _ nil _ EQ) as [ME UNDEF]. inv ME. split.
  constructor; simpl.
  intros id v. repeat rewrite PTree.gsspec. destruct (peq id a); intros.
  subst a. inv H. exists x1; split. auto. apply Regmap.gi.
  replace (init_regs nil x) with (Regmap.init Vundef) in me_vars0. eauto.
  destruct x; reflexivity.
  intros. apply Regmap.gi.
  (* vl = v1 :: vs *)
  destruct (IHil _ _ _ _ vs _ EQ) as [ME UNDEF]. inv ME. split.
  constructor; simpl.
  intros id v. repeat rewrite PTree.gsspec. destruct (peq id a); intros.
  subst a. inv H. exists x1; split. auto. apply Regmap.gss.
  exploit me_vars0; eauto. intros [r' [C D]]. 
  exists r'; split. auto. rewrite Regmap.gso. auto.
  apply valid_fresh_different with s.
  apply B. left; exists id; auto.
  eauto with rtlg. 
  intros. rewrite Regmap.gso. apply UNDEF. 
  apply reg_fresh_decr with s2; eauto with rtlg.
  apply sym_not_equal. apply valid_fresh_different with s2; auto.
Qed.

Lemma match_set_locals:
  forall map1 s1,
  map_wf map1 ->
  forall il rl map2 s2 e rs i,
  match_env map1 e rs ->
  (forall r, reg_fresh r s1 -> rs#r = Vundef) ->
  add_vars map1 il s1 = OK (rl, map2) s2 i ->
  match_env map2 (set_locals il e) rs.
Proof.
  induction il; simpl in *; intros.

  inv H2. auto.

  monadInv H2. 
  exploit IHil; eauto. intro. 
  monadInv EQ1.
  constructor.
  intros id v. simpl. repeat rewrite PTree.gsspec. 
  destruct (peq id a). subst a. intro. 
  exists x1. split. auto. inv H3. 
  apply H1. apply reg_fresh_decr with s. auto.
  eauto with rtlg.
  intros. eapply me_vars; eauto. 
Qed.

Lemma match_init_env_init_reg:
  forall params s0 rparams map1 s1 i1 vars rvars map2 s2 i2 vparams,
  add_vars init_mapping params s0 = OK (rparams, map1) s1 i1 ->
  add_vars map1 vars s1 = OK (rvars, map2) s2 i2 ->
  match_env map2 (set_locals vars (set_params vparams params))
            (init_regs vparams rparams).
Proof.
  intros.
  exploit match_set_params_init_regs; eauto. intros [A B].
  eapply match_set_locals; eauto.
  eapply add_vars_wf; eauto. apply init_mapping_wf.
  apply init_mapping_valid.
Qed.

(** * The simulation argument *)

Definition genv_rel : CminorSel.genv -> RTL.genv -> Prop :=
(fun x y => Genv.genv_match (fun a b => transl_fundef false a = Errors.OK b) y x).

Require Import Errors.

Section CORRECTNESS.

Variable ge:  CminorSel.genv.
Variable tge: RTL.genv.
Hypothesis TRANSF: genv_rel ge tge.

(** Relationship between the global environments for the original
  CminorSel program and the generated RTL program. *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof. by intros; destruct TRANSF. Qed.

(** Correctness of the code generated by [add_move]. *)

Lemma tr_move_correct:
  forall r1 ns r2 nd cs code sp rs,
  tr_move code ns r1 nd r2 ->
  exists rs', 
  rtl_trace tge (State cs code sp ns rs) (weakcons TEtau nil)
                (State cs code sp nd rs') /\
  rs'#r2 = rs#r1 /\
  (forall r, r <> r2 -> rs'#r = rs#r).
Proof.
  intros. inv H. 
  exists rs; split.
  apply rtl_trace_refl.
  by split. 
  exists (rs#r2 <- (rs#r1));  split.
  eapply rtl_trace_step_one.
  eapply exec_Iop; eauto. simpl; eauto. 
  split. apply Regmap.gss. intros; apply Regmap.gso; auto.
Qed.

(** Correctness of the code generated by [store_var] and [store_optvar]. *)

Lemma tr_store_var_correct:
  forall rs cs code map r id ns nd e sp,
  tr_store_var code map r id ns nd ->
  map_wf map ->
  match_env map e rs ->
  exists rs',
    rtl_trace tge (State cs code sp ns rs) 
                  (weakcons TEtau nil)
                  (State cs code sp nd rs')
  /\ match_env map (PTree.set id rs#r e) rs'.
Proof.
  intros. destruct H as [rv [A B]].
  exploit tr_move_correct; eauto. intros [rs' [EX [RES OTHER]]].
  exists rs'; split. eexact EX.
  apply match_env_invariant with (rs#rv <- (rs#r)).
  apply match_env_update_var; auto.
  intros. rewrite Regmap.gsspec. destruct (peq r0 rv).
  subst r0; auto.
  auto.
Qed.

Lemma tr_store_optvar_correct:
  forall rs cs code map r optid ns nd e sp,
  tr_store_optvar code map r optid ns nd ->
  map_wf map ->
  match_env map e rs ->
  exists rs',
     rtl_trace tge (State cs code sp ns rs)
                   (weakcons TEtau nil)
                   (State cs code sp nd rs')
  /\ match_env map (set_optvar optid rs#r e) rs'.
Proof.
  intros. destruct optid; simpl in H.
  eapply tr_store_var_correct; eauto.
  exists rs; split. subst.
  econstructor. by simpl. 
Qed.

(** Correctness of the translation of [switch] statements *)

Lemma transl_switch_correct:
  forall cs sp e f map r nexits t ns,
  tr_switch f map r nexits t ns ->
  forall rs i act,
  rs#r = Vint i ->
  map_wf map ->
  match_env map e rs ->
  comptree_match i t = act ->
  exists nd, exists rs',
  rtl_trace tge 
      (State cs f sp ns rs ) (weakcons TEtau nil)
      (State cs f sp nd rs' ) /\
  nth_error nexits act = Some nd /\
  match_env map e rs'.
Proof.
  induction 1; simpl; intros.
(* action *)
   inv H3. exists n; exists rs; intuition.  
   by apply rtl_trace_refl. 
(* ifeq *)
  caseEq (Int.eq i key); intro EQ; rewrite EQ in *; clarify.
  exists nfound'; exists rs;  intuition.
   eapply rtl_trace_trans.
     eapply rtl_trace_step_one; eapply exec_Icond_true; eauto.
     simpl. rewrite H4. congruence.
     eapply rtl_trace_step_one; eapply exec_Inop; eauto.
   done.
   exploit IHtr_switch; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
   exists nd1; exists rs1;  intuition.
  eapply rtl_trace_trans.
  eapply rtl_trace_step_one; eapply exec_Icond_false. eauto.
  simpl; rewrite H4; congruence. 
  eapply rtl_trace_trans.
  eapply rtl_trace_step_one; eapply exec_Inop; eauto.
  by eexact EX; simpl. 
  done.
  done. 
   by rewrite <- plus_n_O in NTH.
  (* iflt *)
  caseEq (Int.ltu i key); intro EQ; rewrite EQ in *.
  exploit IHtr_switch1; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply rtl_trace_trans.
  - eapply rtl_trace_step_one; eapply exec_Icond_true; eauto; simpl.
    rewrite H4; congruence. 
  eapply rtl_trace_trans.
  - eapply rtl_trace_step_one; eapply exec_Inop; eauto; simpl.
  - by eexact EX. 
  done.
  done.
  exploit IHtr_switch2; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply rtl_trace_trans.
  eapply rtl_trace_step_one.
  eapply exec_Icond_false. eauto. simpl.
    rewrite H4; congruence. 
  eapply rtl_trace_trans.
  - eapply rtl_trace_step_one; eapply exec_Inop; eauto; simpl.
  - by eexact EX. 
  done.
  done.
Qed.

Section CORRECTNESS_EXPR.

Variable e: env.
Variable sp : option Pointers.pointer.

(** The proof of semantic preservation for the translation of expressions
  is a simulation argument based on diagrams of the following form:
<<
                    I /\ P
    e, le, m, a ------------- State cs code sp ns rs m
         ||                      |
         ||                      |*
         ||                      |
         \/                      v
    e, le, m', v ------------ State cs code sp nd rs' m'
                    I /\ Q
>>
  where [tr_expr code map pr a ns nd rd] is assumed to hold.
  The left vertical arrow represents an evaluation of the expression [a].
  The right vertical arrow represents the execution of zero, one or
  several instructions in the generated RTL flow graph [code].

  The invariant [I] is the agreement between Cminor environments and
  RTL register environment, as captured by [match_envs].

  The precondition [P] includes the well-formedness of the compilation
  environment [mut].

  The postconditions [Q] state that in the final register environment
  [rs'], register [rd] contains value [v], and the registers in
  the set of preserved registers [pr] are unchanged, as are the registers
  in the codomain of [map].

  We formalize this simulation property by the following predicate
  parameterized by the CminorSel evaluation (left arrow).  *)

Definition transl_expr_prop 
    (lt : list thread_event) (a: expr) (v: val) : Prop :=
  forall cs f map pr ns nd rd rs dst 
    (MWF: map_wf map)
    (TE: tr_expr f map pr a ns nd rd dst)
    (ME: match_env map e rs),
  exists rs', 
     rtl_trace tge (State cs f sp ns rs) lt  (State cs f sp nd rs')
  /\ match_env map (set_optvar dst v e)  rs'
  /\ rs'#rd = v
  /\ (forall r, In r pr -> rs'#r = rs#r).


(** The simulation properties for lists of expressions and for
  conditional expressions are similar. *)

Definition transl_exprlist_prop 
     (lt : list thread_event) (al: exprlist) (vl: list val) : Prop :=
  forall cs f map pr ns nd rl rs
    (MWF: map_wf map)
    (TE: tr_exprlist f map pr al ns nd rl)
    (ME: match_env map e rs),
  exists rs', 
     rtl_trace tge (State cs f sp ns rs) lt (State cs f sp nd rs')
  /\ match_env map e rs'
  /\ rs'##rl = vl
  /\ (forall r, In r pr -> rs'#r = rs#r).

Definition transl_condition_prop 
    (lt : list thread_event)  (a: condexpr) (vb: bool) : Prop :=
  forall cs f map pr ns ntrue nfalse rs 
    (MWF: map_wf map)
    (TE: tr_condition f map pr a ns ntrue nfalse)
    (ME: match_env map e rs),
  exists rs', 
     rtl_trace tge (State cs f sp ns rs) lt
                   (State cs f sp (if vb then ntrue else nfalse) rs')
  /\ match_env map e rs'
  /\ (forall r, In r pr -> rs'#r = rs#r).


(** The correctness of the translation is a huge induction over
  the Cminor evaluation derivation for the source program.  To keep
  the proof manageable, we put each case of the proof in a separate
  lemma.  There is one lemma for each Cminor evaluation rule.
  It takes as hypotheses the premises of the Cminor evaluation rule,
  plus the induction hypotheses, that is, the [transl_expr_prop], etc,
  corresponding to the evaluations of sub-expressions or sub-statements. *)

Lemma transl_expr_Evar_correct:
  forall (id : positive) (v : val),
  e ! id = Some v ->
  transl_expr_prop nil (Evar id) v.
Proof.
  intros; red; intros. inv TE.
  exploit match_env_find_var; eauto. intro EQ.
  exploit tr_move_correct; eauto. intros [rs' [A [B C]]]. 
  exists rs'; split. eauto.
  destruct H2 as [[D E] | [D E]].
  (* optimized case *)
  subst r dst. simpl.
  assert (forall r, rs'#r = rs#r).
    intros. destruct (Reg.eq r rd). subst r. eauto. eauto.
  split. eapply match_env_invariant; eauto.
  split. congruence. auto.
  (* general case *)
  split.
  apply match_env_invariant with (rs#rd <- v).
  apply match_env_update_dest; auto. 
  intros. rewrite Regmap.gsspec. destruct (peq r0 rd). congruence. auto. 
  split. congruence. 
  intros. apply C. intuition congruence.
Qed.

Lemma transl_expr_Eop_correct:
  forall (op : operation) (lt : list thread_event) 
         (args : exprlist)
         (vargs : list val) (v : val),
  eval_exprlist ge sp e lt args vargs ->
  transl_exprlist_prop lt args vargs ->
  eval_operation ge sp op vargs = Some v ->
  transl_expr_prop lt (Eop op args) v.
Proof.
  intros; red; intros. inv TE. 
  exploit H0; eauto. intros [rs1 [EX1 [ME1 [RR1 RO1]]]].
  exists (rs1#rd <- v).
(* Exec *)
  split.
  eapply trace_step_right.  eexact EX1.
  eapply exec_Iop; eauto.
  erewrite (@eval_operation_preserved CminorSel.fundef _ _ _). 
  subst vargs; eauto.
  exact symbols_preserved. unfold weakcons; simpl. 
    apply app_nil_end.
(* Match-env *)
  split. eauto with rtlg.  
(* Result reg *)
  split. apply Regmap.gss.
(* Other regs *)
  intros. rewrite Regmap.gso. auto. intuition congruence.
Qed.

Lemma transl_expr_Eload_correct:
  forall (chunk : memory_chunk) (addr : Op.addressing)
         (args : exprlist) v (t tl : list thread_event)
         (vargs : list val) p 
  (EXP:  eval_exprlist ge sp e tl args vargs)
  (TEXP: transl_exprlist_prop tl args vargs)
  (OP: Op.eval_addressing ge sp addr vargs = Some (Vptr p))
  (HT: Val.has_type v (type_of_chunk chunk)),
  t = (tl ++ (TEmem(MEread p chunk v)) :: nil) ->
  transl_expr_prop t (Eload chunk addr args) v.
Proof.
  intros; red; intros. inv TE.
  exploit TEXP; eauto. intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  exists (rs1#rd <- v).
(* Exec *)
  split. eapply trace_step_right. eexact EX1. eapply exec_Iload; eauto.
  rewrite RES1. rewrite (@eval_addressing_preserved _ _ ge tge).
  eexact OP. exact symbols_preserved. eby simpl.
(* Match-env *)
  split. eauto with rtlg. 
(* Result *)
  split. apply Regmap.gss.
(* Other regs *)
  intros. rewrite Regmap.gso. auto. intuition congruence. 
Qed.

Lemma transl_expr_Econdition_correct:
  forall (t1 t23 : list thread_event)
         (cond : condexpr) (ifso ifnot : expr)
         (vcond : bool) (v : val) (t : list thread_event), 
  eval_condexpr ge sp e t1 cond vcond ->
  transl_condition_prop t1 cond vcond ->
  eval_expr ge sp e t23 (if vcond then ifso else ifnot) v ->
  transl_expr_prop  t23 (if vcond then ifso else ifnot) v  ->
  t = t1 ++ t23 ->
  transl_expr_prop t (Econdition cond ifso ifnot) v.
Proof.
  intros; red; intros; inv TE. 
  destruct vcond;
    exploit H0; eauto; intros [rs1 [EX1 [ME1 OTHER1]]];
    exploit H2; eauto; intros [rs2 [EX2 [ME2 [RES2 OTHER2]]]];
  exists rs2;
  (split; [eapply rtl_trace_trans; [eexact EX1|eapply rtl_trace_trans;
    [eapply rtl_trace_step_one; eapply exec_Inop; eauto|eexact EX2|]|]
    |split; [|split]]; try done; intros; transitivity (rs1#r); auto).
Qed.

Lemma add_letvar_wf:
  forall map r,
  map_wf map -> ~reg_in_map map r -> map_wf (add_letvar map r).
Proof.
  intros. inv H. unfold add_letvar; constructor; simpl.
  auto.
  intros. elim H1; intro. subst r0. elim H0. left; exists id; auto.
  eauto.
Qed.

Lemma match_env_bind_letvar:
  forall map e rs r v,
  match_env map e rs ->
  rs#r = v ->
  match_env (add_letvar map r) e rs.
Proof.
  intros. inv H. unfold add_letvar. apply mk_match_env; simpl; auto.
Qed.

Lemma match_env_unbind_letvar:
  forall map e rs r,
  match_env (add_letvar map r) e  rs ->
  match_env map e rs.
Proof.
  unfold add_letvar; intros. inv H. simpl in *. 
  constructor. auto. 
Qed.

Lemma transl_expr_Ediscard_correct:
  forall (a1: expr)  (t1 : list thread_event)
         (v1 : val)  (a2 : expr)
         (t2 : list thread_event)
         (v2 : val) (t : list thread_event),
  eval_expr ge sp e t1 a1 v1 ->
  transl_expr_prop t1 a1 v1 ->
  eval_expr ge sp e t2 a2 v2 ->
  transl_expr_prop t2 a2 v2  ->
  t = t1 ++ t2 ->
  transl_expr_prop t (Ediscard a1 a2) v2.
Proof.
  intros; red; intros; inv TE. 
  exploit H0; eauto. intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  assert (map_wf (add_letvar map r)).
    eapply add_letvar_wf; eauto. 
  exploit H2; eauto. eapply match_env_bind_letvar; eauto. 
  intros [rs2 [EX2 [ME3 [RES2 OTHER2]]]].
  exists rs2.
(* Exec *)
  split. eapply rtl_trace_trans. eexact EX1. eexact EX2. auto.
(* Match-env *)
  split. eapply match_env_unbind_letvar; eauto.
(* Result *)
  split. assumption.
(* Other regs *)
  intros. transitivity (rs1#r0). 
  apply OTHER2.  auto.
  unfold reg_in_map, add_letvar; simpl.
  auto.
Qed.

Lemma transl_condition_CEtrue_correct:
   transl_condition_prop nil CEtrue true.
Proof.
  intros. red. intros. inv TE. 
  exists rs. split. apply rtl_trace_refl. split. auto. auto.
Qed.    

Lemma transl_condition_CEfalse_correct:
  transl_condition_prop nil CEfalse false.
Proof.
  intros; red; intros; inv TE. 
  exists rs. split. apply rtl_trace_refl. split. auto. auto.
Qed.    

Lemma transl_condition_CEcond_correct:
  forall (lt: list thread_event)
         (cond : condition) (args : exprlist)
         (vargs : list val) (b : bool),
  eval_exprlist ge sp e lt args vargs ->
  transl_exprlist_prop lt args vargs ->
  eval_condition cond vargs = Some b ->
  transl_condition_prop lt (CEcond cond args) b.
Proof.
  intros; red; intros; inv TE.
  exploit H0; eauto. intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  exists rs1.
(* Exec *)
  split. eapply trace_step_right. eexact EX1. 
  destruct b.
  eapply exec_Icond_true; eauto. 
  rewrite RES1. assumption.
  eapply exec_Icond_false; eauto. 
  rewrite RES1. assumption.
  unfold weakcons; simpl. apply app_nil_end.
(* Match-env *)
  split. assumption.
(* Regs *)
  auto.
Qed.

Lemma transl_condition_CEcondition_correct:
  forall (t t1 t23 : list thread_event)
         (cond ifso ifnot : condexpr) (vcond v : bool),
  eval_condexpr ge sp e t1 cond vcond ->
  transl_condition_prop t1 cond vcond ->
  eval_condexpr ge sp e t23 (if vcond then ifso else ifnot) v ->
  transl_condition_prop t23
     (if vcond then ifso else ifnot) v ->
  t = t1 ++ t23 ->
  transl_condition_prop t (CEcondition cond ifso ifnot) v.
Proof.
  intros; red; intros; inv TE. 
  exploit H0; eauto. intros [rs1 [EX1 [ME1 OTHER1]]].
  destruct vcond;
    exploit H2; eauto; intros [rs2 [EX2 [ME2 OTHER2]]];
  exists rs2;
  (split; [eapply rtl_trace_trans; [eexact EX1|eapply rtl_trace_trans;
    [eapply rtl_trace_step_one; eapply exec_Inop; eauto|eexact EX2|]|]
    |split]; try done; intros; transitivity (rs1#r); auto).
Qed.
 
Lemma transl_exprlist_Enil_correct:
  transl_exprlist_prop nil Enil nil.
Proof.
  intros; red; intros; inv TE.
  exists rs.
  split. apply rtl_trace_refl.
  split. assumption.
  split. reflexivity.
  auto.
Qed.


Lemma transl_exprlist_Econs_correct:
  forall (t1 tl : list thread_event)
         (a1 : expr) (al : exprlist) (v1 : val)
         (vl : list val) (t : list thread_event),
  eval_expr ge sp e t1 a1 v1 ->
  transl_expr_prop t1 a1 v1 ->
  eval_exprlist ge sp e tl al vl ->
  transl_exprlist_prop  tl al vl ->
  t = t1 ++ tl ->
  transl_exprlist_prop t (Econs a1 al) (v1 :: vl).
Proof.
  intros; red; intros; inv TE.
  exploit H0; eauto. intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  exploit H2; eauto. intros [rs2 [EX2 [ME2 [RES2 OTHER2]]]].
  exists rs2.
(* Exec *)
  split. eapply rtl_trace_trans. eexact EX1. eexact EX2. auto. 
(* Match-env *)
  split. assumption.
(* Results *)
  split. simpl. rewrite RES2. rewrite OTHER2. rewrite RES1. auto.
  simpl; tauto. 
(* Other regs *)
  intros. transitivity (rs1#r).
  apply OTHER2; auto. simpl; tauto. 
  apply OTHER1; auto.
Qed.

Theorem transl_expr_correct:
  forall t a v,
  eval_expr ge sp e t a v ->
  transl_expr_prop t a v.
Proof
 (eval_expr_ind3 ge sp e 
   transl_expr_prop
   transl_condition_prop
   transl_exprlist_prop
   transl_expr_Evar_correct
   transl_expr_Eop_correct
   transl_expr_Eload_correct
   transl_expr_Econdition_correct
   transl_expr_Ediscard_correct
   transl_condition_CEtrue_correct
   transl_condition_CEfalse_correct
   transl_condition_CEcond_correct
   transl_condition_CEcondition_correct
   transl_exprlist_Enil_correct
   transl_exprlist_Econs_correct).

Theorem transl_condexpr_correct:
  forall t a v,
  eval_condexpr ge sp e t a v ->
  transl_condition_prop t a v.
Proof
 (eval_condexpr_ind3 ge sp e 
   transl_expr_prop
   transl_condition_prop
   transl_exprlist_prop
   transl_expr_Evar_correct
   transl_expr_Eop_correct
   transl_expr_Eload_correct
   transl_expr_Econdition_correct
   transl_expr_Ediscard_correct
   transl_condition_CEtrue_correct
   transl_condition_CEfalse_correct
   transl_condition_CEcond_correct
   transl_condition_CEcondition_correct
   transl_exprlist_Enil_correct
   transl_exprlist_Econs_correct).

Theorem transl_exprlist_correct:
  forall t a v,
  eval_exprlist ge sp e t a v ->
  transl_exprlist_prop t a v.
Proof
  (eval_exprlist_ind3 ge sp e 
     transl_expr_prop
     transl_condition_prop
     transl_exprlist_prop
     transl_expr_Evar_correct
     transl_expr_Eop_correct
     transl_expr_Eload_correct
     transl_expr_Econdition_correct
     transl_expr_Ediscard_correct
     transl_condition_CEtrue_correct
     transl_condition_CEfalse_correct
     transl_condition_CEcond_correct
     transl_condition_CEcondition_correct
     transl_exprlist_Enil_correct
     transl_exprlist_Econs_correct).

End CORRECTNESS_EXPR.


(** ** Measure over CminorSel states *)

Open Local Scope nat_scope.

Fixpoint size_stmt (s: stmt) : nat :=
  match s with
  | Sskip => 0
  | Sseq s1 s2 => (size_stmt s1 + size_stmt s2 + 1)
  | Sifthenelse e s1 s2 => (size_stmt s1 + size_stmt s2 + 1)
  | Sloop s1 => (size_stmt s1 + 1)
  | Sblock s1 => (size_stmt s1 + 1)
  | Sexit n => 0
  | Slabel lbl s1 => (size_stmt s1 + 1)
  | _ => 1
  end.

Fixpoint size_cont (k: cont) : nat :=
  match k with
  | Kseq s k1 => (size_stmt s + size_cont k1 + 1)
  | Kblock k1 => (size_cont k1 + 1)
  | _ => 0%nat
  end.

Definition measure_state (S: CminorSel.state) :=
  match S with
  | CminorSel.SKstmt  s _ _ k =>
      existS (fun (x: nat) => nat)
             (size_stmt s + size_cont k)
             (size_stmt s)
  | CminorSel.SKreturn  _ _ =>
      existS (fun (x: nat) => nat) 1 1
  | _ =>
      existS (fun (x: nat) => nat) 0 0
  end.


Require Import Relations.
Require Import Wellfounded.

Definition lt_state (S1 S2: CminorSel.state) :=
  lexprod nat (fun (x: nat) => nat)
          lt (fun (x: nat) => lt)
          (measure_state S1) (measure_state S2).

Lemma lt_state_intro:
  forall s1 k1 sp1 e1 s2 k2 sp2 e2,
  size_stmt s1 + size_cont k1 < size_stmt s2 + size_cont k2
  \/ (size_stmt s1 + size_cont k1 = size_stmt s2 + size_cont k2
      /\ size_stmt s1 < size_stmt s2) ->
  lt_state (CminorSel.SKstmt  s1 sp1 e1 k1)
           (CminorSel.SKstmt  s2 sp2 e2 k2).
Proof.
  intros. unfold lt_state. simpl. destruct H as [A | [A B]].
  apply left_lex. auto.
  rewrite A. apply right_lex. auto.
Qed.

Ltac Lt_state :=
  apply lt_state_intro; simpl; try omega.

Require Import Wf_nat.

Lemma lt_state_wf:
  well_founded lt_state.
Proof.
  unfold lt_state. apply wf_inverse_image with (f := measure_state).
  apply wf_lexprod. apply lt_wf. intros. apply lt_wf. 
Qed.

(** ** Semantic preservation for the translation of statements *)   

(** The simulation diagram for the translation of statements
  and functions is a "star" diagram of the form:
<<
           I                         I
     S1 ------- R1             S1 ------- R1
     |          |              |          |
   t |        + | t      or  t |        * | t    and |S2| < |S1|
     v          v              v          |
     S2 ------- R2             S2 ------- R2
           I                         I
>>
  where [I] is the [match_states] predicate defined below.  It includes:
- Agreement between the Cminor statement under consideration and
  the current program point in the RTL control-flow graph,
  as captured by the [tr_stmt] predicate.
- Agreement between the Cminor continuation and the RTL control-flow
  graph and call stack, as captured by the [tr_cont] predicate below.
- Agreement between Cminor environments and RTL register environments,
  as captured by [match_envs].

*)

Inductive tr_funbody (c: code) (map: mapping) (f: CminorSel.function)
                     (ngoto: labelmap) (nret: node) (rret: option reg) : Prop :=
  | tr_funbody_intro: forall nentry r,
      rret = ret_reg f.(CminorSel.fn_sig) r ->
      tr_stmt c map f.(fn_body) nentry nret nil ngoto nret rret ->
      tr_funbody c map f ngoto nret rret.

Inductive tr_cont: RTL.code -> mapping -> 
                   CminorSel.cont -> node ->
                   list node -> labelmap -> node -> option reg ->
                   list RTL.stackframe -> Prop :=
  | tr_Kseq: forall c map s k nd nexits ngoto nret rret cs n,
      tr_stmt c map s nd n nexits ngoto nret rret ->
      tr_cont c map k n nexits ngoto nret rret cs ->
      tr_cont c map (Kseq s k) nd nexits ngoto nret rret cs
  | tr_Kblock: forall c map k nd nexits ngoto nret rret cs,
      tr_cont c map k nd nexits ngoto nret rret cs ->
      tr_cont c map (Kblock k) nd (nd :: nexits) ngoto nret rret cs
  | tr_Kstop: forall c map ngoto nret rret cs,
      c!nret = Some(Ireturn rret) ->
      match_stacks Kstop cs ->
      tr_cont c map Kstop nret nil ngoto nret rret cs
  | tr_Kcall: forall c map optid f sp e k ngoto nret rret cs,
      c!nret = Some(Ireturn rret) ->
      match_stacks (Kcall optid f sp e k) cs ->
      tr_cont c map (Kcall optid f sp e k) nret nil ngoto nret rret cs

with match_stacks: CminorSel.cont -> list RTL.stackframe -> Prop :=
  | match_stacks_stop:
      match_stacks Kstop nil 
  | match_stacks_call_stop: forall f,
      match_stacks (Kcall None (Internal f) None (PTree.empty val) Kstop) nil 
  | match_stacks_call: forall optid f fd sp e k r c n rs cs 
                              map nexits ngoto nret rret,
      map_wf map ->
      tr_funbody c map f ngoto nret rret ->
      match_env map e rs ->
      reg_map_ok map r optid ->
(*      tr_store_optvar c map r optid n n' ->
      ~reg_in_map map r -> *)
      tr_cont c map k n nexits ngoto nret rret cs ->
      get_fundef (call_cont k) = Some (Internal f) ->
      match_stacks (Kcall optid fd sp e k) (Stackframe r c sp n rs :: cs).

Inductive match_states: CminorSel.state -> RTL.state -> Prop :=
  | match_state:
      forall f s k sp e cs c ns rs map ncont nexits ngoto nret rret
        (MWF: map_wf map)
        (TS: tr_stmt c map s ns ncont nexits ngoto nret rret)
        (TF: tr_funbody c map f ngoto nret rret) 
        (GFD: get_fundef (call_cont k) = Some (Internal f))
        (TK: tr_cont c map k ncont nexits ngoto nret rret cs)
        (ME: match_env map e rs),
      match_states (CminorSel.SKstmt s sp e k)
                   (RTL.State cs c sp ns rs)
  | match_callstate:
      forall f args k cs tf optid sp env' k'
        (TF: transl_fundef false f = OK tf)
        (CONT: k = (Kcall optid f sp env' k'))
        (MS: match_stacks k cs),
      match_states (CminorSel.SKcall args k)
                   (RTL.Callstate cs tf args)
  | match_returnstate:
      forall v k cs
        (MS: match_stacks (call_cont k) cs),
      match_states (CminorSel.SKreturn v k)
                   (RTL.Returnstate cs v)
  | match_returnstate_stop:
      forall v,
      match_states (CminorSel.SKstmt Sskip None (PTree.empty val) Kstop)
                   (RTL.Returnstate nil v)
  | match_externalstate:
    forall ef tgt sp env k  cs
    (MS : match_stacks (Kcall tgt (External ef) sp env k) cs),
    match_states (SKexternal (ef_sig ef) (Kcall tgt (External ef) sp env k))
                             (Blockedstate cs (ef_sig ef)).



Lemma match_stacks_call_cont:
  forall c map k ncont nexits ngoto nret rret cs,
  tr_cont c map k ncont nexits ngoto nret rret cs ->
  match_stacks (call_cont k) cs /\ c!nret = Some(Ireturn rret).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma tr_cont_call_cont:
  forall c map k ncont nexits ngoto nret rret cs,
  tr_cont c map k ncont nexits ngoto nret rret cs ->
  tr_cont c map (call_cont k) nret nil ngoto nret rret cs.
Proof.
  induction 1; simpl; auto; econstructor; eauto.
Qed.


Lemma tr_find_label:
  forall c map lbl n (ngoto: labelmap) nret rret s' k' cs,
  ngoto!lbl = Some n ->
  forall s k ns1 nd1 nexits1,
  find_label lbl s k = Some (s', k') ->
  tr_stmt c map s ns1 nd1 nexits1 ngoto nret rret ->
  tr_cont c map k nd1 nexits1 ngoto nret rret cs ->
  exists ns2, exists nd2, exists nexits2,
     c!n = Some(Inop ns2)
  /\ tr_stmt c map s' ns2 nd2 nexits2 ngoto nret rret
  /\ tr_cont c map k' nd2 nexits2 ngoto nret rret cs.
Proof.
  induction s; intros until nexits1; simpl; try congruence.
  (* seq *)
  caseEq (find_label lbl s1 (Kseq s2 k)); intros.
  inv H1. inv H2. eapply IHs1; eauto. econstructor; eauto.
  inv H2. eapply IHs2; eauto. 
  (* ifthenelse *)
  caseEq (find_label lbl s1 k); intros.
  inv H1. inv H2. eapply IHs1; eauto.
  inv H2. eapply IHs2; eauto.
  (* loop *)
  intros. inversion H1; subst.
  eapply IHs; eauto. econstructor; eauto.
  (* block *)
  intros. inv H1.
  eapply IHs; eauto. econstructor; eauto.
  (* label *)
  destruct (ident_eq lbl l); intros.
  inv H0. inv H1.
  assert (n0 = n). change positive with node in H4. 
      congruence. subst n0.
  exists ns1; exists nd1; exists nexits1; auto.
  inv H1. eapply IHs; eauto.
Qed.

Lemma functions_translated:
  forall (v: val) (f: CminorSel.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef false f = OK tf.
Proof.
  intros.  
  unfold Genv.find_funct; destruct v; intuition; inv H.
  destruct TRANSF.
  unfold CminorSel.fundef in H1.
  specialize (H0 p).
  rewrite H1 in H0.
  destruct (Genv.find_funct_ptr tge p) as []_eqn : K.
  exists f0; split. done.
  unfold RTL.fundef in K.
  rewrite K in H0; done.
  unfold RTL.fundef in K.
  rewrite K in H0. intuition.
Qed.

Lemma sig_transl_function:
  forall (f: CminorSel.fundef) (tf: RTL.fundef),
  transl_fundef false f = OK tf ->
  RTL.funsig tf = CminorSel.funsig f.
Proof.
  intros until tf.
  unfold transl_fundef. unfold transf_partial_fundef.
  case f; intro.
  unfold transl_function.
  destruct (reserve_labels (fn_body f0) (PTree.empty node, init_state)) 
    as [ngoto s0].
  case (transl_fun false f0 ngoto s0); simpl; intros.
  monadInv H. destruct Zgt_bool; try discriminate.
  destruct Zlt_bool; try discriminate.
  destruct p. monadInv H.
    destruct Zgt_bool; try discriminate.
    destruct Zlt_bool; try discriminate.
  inv EQ. reflexivity.
  intro. inv H. reflexivity.
Qed.


Ltac dest := repeat match goal with
   | H : match ?a with
        | Some x => _
        | None => _
        end = _ |- _ => destruct a as [] _eqn: ?; clarify
   | H : _, H': _ |- _ => specialize (H _ _ _ H'); clarify
   end.

Lemma simpl_call_cont:
  forall k,
  call_cont (call_cont k) = call_cont k.
Proof.
  induction k; clarify.
Qed.

Lemma match_call_cont_label:
  forall l s s' k k'
  (LAB: find_label l s k = Some (s', k')),
  call_cont k = call_cont k'.
Proof.
  intro. 
  induction s; intros; try inv LAB; try dest.
  destruct ident_eq; clarify. 
  specialize (IHs s' k k' H0); clarify.
Qed.

Theorem transl_step_correct:
  forall S1 t S2, CminorSel.step ge S1 t S2 ->
  forall R1, match_states S1 R1 ->
  exists R2, 
   (RTL.rtl_trace_plus tge R1 t R2 \/ (RTL.rtl_trace tge R1 t R2 /\ lt_state S2 S1))
      /\ match_states S2 R2.
Proof.
  induction 1; intros R1 MSTATE; inv MSTATE.

  (* skip block *)
  inv TS. inv TK. econstructor; split.
  right. split. apply rtl_trace_refl. Lt_state.
  econstructor; eauto. constructor.

  (* assign *)
  inv TS. 
  exploit transl_expr_correct; eauto. 
  intros [rs' [A [B [C D]]]].
  econstructor. split.
  right; split. eauto. Lt_state.  
  econstructor; eauto. constructor.
  exploit transl_expr_correct; eauto.
  intros [rs' [A [B [C D]]]].
  exploit tr_move_correct; eauto.
  intros [rs'' [P [Q R]]].
  econstructor; split.
  right; split. assert (t = (t ++ nil)). apply app_nil_end.
   rewrite H. eapply rtl_trace_trans. eexact A.
  assert (nil = (weakcons TEtau nil)). by unfold weakcons.
   rewrite H0. eexact P. by unfold weakcons. Lt_state.
  econstructor; eauto. constructor.
  simpl in B. apply match_env_invariant with (rs'#r <- v).
  apply match_env_update_var; auto.
  intros. rewrite Regmap.gsspec. destruct (peq r0 r). by congruence. auto.

  (* store *)
  inv TS.
  exploit transl_exprlist_correct; eauto.
  intros [rs' [A [B [C D]]]].
  exploit transl_expr_correct; eauto.
  intros [rs'' [E [F [G J]]]].
  assert (rs''##rl = vl).
    rewrite <- C. apply list_map_exten. intros. symmetry. apply J. auto.
  econstructor; split.
  left. eapply plus_right. eapply rtl_trace_trans. 
    eexact A. eexact E.  edone.
  eapply exec_Istore with (a := ptr); eauto.
  rewrite H.  rewrite <- EVAL. apply eval_addressing_preserved.
  eexact symbols_preserved.
  rewrite G. unfold weakcons. rewrite <- app_ass.
  econstructor; eauto. econstructor; eauto. constructor.

  (* call *)
  generalize TS; intros. inv TS.  
  exploit transl_expr_correct; eauto.
  intros [rs' [A [B [C D]]]].
  exploit transl_exprlist_correct; eauto.
  intros [rs'' [E [F [G J]]]].
  exploit functions_translated; eauto. intros [tf' [ P Q]].
  econstructor; split.
  left; eapply plus_right. eapply rtl_trace_trans.
    eexact A. eexact E.  edone.
  eapply exec_Icall. edone. simpl. rewrite J. rewrite C. eauto. simpl. 
    by left.
  by apply sig_transl_function. simpl. by rewrite <- app_nil_end.
  rewrite G. econstructor. edone.  econstructor; eauto. 
  econstructor; eauto.

  (* atomic - some *)
  inv TS.
  exploit transl_exprlist_correct; eauto; intro; des. 
  eexists; split; [by left; eapply plus_right with (l := TEmem lab); try edone; vauto|].
  by inv H10; econstructor; eauto using match_env_update_temp; vauto.

  (* atomic - none *)
  inv TS.
  exploit transl_exprlist_correct; eauto; intro; des. 
  eexists; split; [by left; eapply plus_right with (l := TEmem lab); try edone; vauto|].
  by inv H10; econstructor; eauto using match_env_update_var; vauto.

  (* fence *)
  by inv TS; eexists; split; [left|]; vauto.


  (* seq *)
  inv TS.  
  econstructor.  econstructor. 
  right; split. apply rtl_trace_refl. Lt_state.
  econstructor; eauto. econstructor; eauto. 

  (* ifthenelse *)
  inv TS.
  exploit transl_condexpr_correct; eauto. 
  intros [rs' [A [B C]]].
  destruct vb; econstructor; (split; [
  right; split; [
    eapply rtl_trace_trans; 
      [eexact A|eapply rtl_trace_step_one; vauto|apply app_nil_end]|]; Lt_state
  |vauto]).

  (* loop *)
  inversion TS; subst.
  econstructor; split.
  left. assert (nil = (weakcons TEtau nil)). by unfold weakcons.
    rewrite H.  apply plus_one. eapply exec_Inop; eauto. 
  econstructor; eauto. 
  econstructor; eauto.

  (* block *)
  inv TS.
  econstructor; split.
  right; split. eapply rtl_trace_refl. Lt_state.
  econstructor; eauto. econstructor; eauto.

  (* exit seq *)
  inv TS. inv TK. 
  econstructor; split.
  right; split. eapply rtl_trace_refl. Lt_state.
  econstructor; eauto. econstructor; eauto.

  (* exit skip *)
  inv TS. inv TK. 
  econstructor; split.
  right; split. eapply rtl_trace_refl. Lt_state.
  econstructor; eauto. inv H0. constructor.

  (* exit block n+1 *)
  inv TS. inv TK. simpl in H0.
  econstructor; split.
  right; split. eapply rtl_trace_refl. Lt_state.
  econstructor; eauto. econstructor; eauto.

  (* switch *)
  inv TS. 
  exploit transl_expr_correct; eauto. 
  intros [rs' [A [B [C D]]]].
  exploit transl_switch_correct; eauto.
  intros [nd [rs'' [K [F G]]]].
  econstructor; split.
  right; split. 
  assert (t = t ++ (weakcons TEtau nil)).
    unfold weakcons. by rewrite <- app_nil_end.
  rewrite H. eapply rtl_trace_trans.
  eexact A.  eexact K. by simpl. Lt_state.
  rewrite (validate_switch_correct _ _ _ H2 n). 
  econstructor; eauto.
  econstructor; eauto.
  assert (comptree_match n t0 = comptree_match n t0 + 0).
    by rewrite <- plus_n_O.
  eby rewrite H.

  (* label *)
  inv TS.
  econstructor; split.
  right; split. apply rtl_trace_refl. Lt_state.
  econstructor; eauto.

  (* goto *)
  inv TS.  inversion TF; subst.
  exploit tr_find_label; eauto. 
  rewrite GFD in GFD0; clarify; eauto.
  eapply tr_cont_call_cont; eauto. 
  intros [ns2 [nd2 [nexits2 [A [B C]]]]].
  econstructor; split.
  assert (nil = (weakcons TEtau nil)). by unfold weakcons.
   rewrite H. 
  left; apply plus_one. eapply exec_Inop; eauto.
  econstructor; eauto.
  pose proof (match_call_cont_label lbl 
                (fn_body f) s' (call_cont k) k'' FL)
     as MCC.
  rewrite simpl_call_cont in MCC.
  by rewrite <- MCC.

  (* return none *)
  inv TS.
  exploit match_stacks_call_cont; eauto. intros [U V].
  econstructor; split.
  left; apply plus_one. eapply exec_Ireturn; eauto.
  simpl. constructor; auto.

  (* return some *)
  inv TS.
  exploit transl_expr_correct; eauto.
  intros [rs' [A [B [C D]]]].
  exploit match_stacks_call_cont; eauto. intros [U V].  
  econstructor; split.
  left; eapply plus_right. eexact A. eapply exec_Ireturn; eauto. 
    destruct sp; try by simpl.
  simpl. rewrite C. constructor; auto.

  (* return finish *)
  rewrite CC in MS.
  inv MS. 
    econstructor; split.
    right. split. 
    - apply rtl_trace_refl.
    - by unfold lt_state; constructor; simpl; omega.
    - by constructor.
  econstructor; split.

  left.  assert (nil = weakcons TEtau nil). by unfold weakcons.
    rewrite H.
  eapply plus_one. eapply exec_return. 
  econstructor; eauto. econstructor.
  eapply match_env_update_dest; eauto.

  (* internal call *)
  unfold transl_fundef, transf_partial_fundef in TF. 
  destruct f0 as []_eqn : K.
  monadInv TF. unfold transl_function in EQ.
  exploit transl_function_charact; eauto. intro TRF.
  inversion TRF. subst f0. clarify.
  pose (e := set_locals (fn_vars f1) (set_params vs (CminorSel.fn_params f1))).
  pose (rs := init_regs vs rparams).
  assert (ME: match_env map2 e rs).
    unfold rs, e. eapply match_init_env_init_reg; eauto.
  assert (MWF: map_wf map2).
    assert (map_valid init_mapping s0) by apply init_mapping_valid.
    exploit (add_vars_valid (CminorSel.fn_params f1)); eauto. 
  intros [A B]. 
    eapply add_vars_wf; eauto. 
    eapply add_vars_wf; eauto. apply init_mapping_wf.
  econstructor; split.
  left. 
   assert (nil = (weakcons TEtau nil)). by unfold weakcons.
  rewrite H1.
  apply plus_one. eapply exec_function_internal_empty; simpl; eauto.
  rewrite FZ. econstructor; eauto.
  econstructor; eauto.
  inversion MS; subst; econstructor; eauto.
  by simpl. econstructor. by simpl. done.
  inv CONT.

  (* internal call -- non-zero stack *)
  unfold transl_fundef, transf_partial_fundef in TF. 
  destruct f0 as []_eqn : K.
  monadInv TF. unfold transl_function in EQ.
  exploit transl_function_charact; eauto. intro TRF.
  inversion TRF. subst f0. clarify.
  pose (e := set_locals (fn_vars f1) (set_params vs (CminorSel.fn_params f1))).
  pose (rs := init_regs vs rparams).
  assert (ME: match_env map2 e rs).
    unfold rs, e. eapply match_init_env_init_reg; eauto.
  assert (MWF: map_wf map2).
    assert (map_valid init_mapping s0) by apply init_mapping_valid.
    exploit (add_vars_valid (CminorSel.fn_params f1)); eauto. 
  intros [A B]. 
    eapply add_vars_wf; eauto. 
    eapply add_vars_wf; eauto. apply init_mapping_wf.
  econstructor; split.
  left. eapply plus_left.
  eapply exec_function_internal_nonempty; simpl; eauto.
  intro E. elim FNZ.
  rewrite <- (Int.signed_repr (fn_stackspace f1)), E.
  unfold Int.zero in E.  rewrite <- (Int.signed_repr 0) in E.
  done. done.
  destruct (Zgt_bool (fn_stackspace f1) Int.max_signed) as []_eqn : K.
  destruct (reserve_labels (fn_body f1) (PTree.empty node, init_state)).
   monadInv EQ.
  destruct (Zlt_bool (fn_stackspace f1) 0) as []_eqn : M.
  destruct (reserve_labels (fn_body f1) (PTree.empty node, init_state)).
   monadInv EQ.
  split. 
  pose proof (Zlt_cases (fn_stackspace f1) Int.min_signed) as ZL.
  unfold Zlt_bool in ZL.  destruct (fn_stackspace f1) as []_eqn : F.
    omega. simpl in  ZL; done. inv M.
  pose proof (Zgt_cases (fn_stackspace f1) Int.max_signed) as ZG.
   rewrite K in ZG. assumption.
  econstructor; eauto. 
  unfold weakcons; simpl. edone.
  econstructor; eauto.
  econstructor; eauto.
  by simpl. econstructor; eauto.
  inv CONT.

  (* external call *)
  unfold transl_fundef, transf_partial_fundef in TF. 
  destruct f as []_eqn : F; try discriminate.
  monadInv TF. 
  econstructor; split.
  left.  change (TEext (Ecall (ef_id ef) evargs) :: nil) with
          (weakcons (TEext (Ecall (ef_id ef) evargs)) nil).
  apply plus_one. eapply exec_function_external_call; eauto. 
  by inv CONT.
  clarify. constructor; auto.

  (* external return *)
  econstructor. split.
  left.  destruct (sig_res (ef_sig ef)) as []_eqn :S.
  change (TEext (Ereturn t evres) :: nil) with 
         (weakcons (TEext (Ereturn t evres)) nil).
  apply plus_one. eapply exec_function_external_return.
  by rewrite S. by eauto. auto.
  change (TEext (Ereturn Tint evres) :: nil) with 
         (weakcons (TEext (Ereturn Tint evres)) nil).
  apply plus_one. eapply exec_function_external_return.
  by rewrite S. by eauto. auto.
  by constructor.

  (* step next *)
  inv TS. inv TK.
  econstructor; split.  
  right.   split.
  econstructor. Lt_state.
  econstructor; eauto.

  (* step stop *)
  inv GFD.
  eexists. split. 
    left. replace (TEexit :: nil) with (weakcons TEexit nil) by done.
    apply plus_one. by constructor.
  by constructor.
   
  (* step thread *)
  inv TS.
  exploit transl_expr_correct; try apply EFN; try edone.
  intros [rs' [A [B [C D]]]].
  exploit transl_expr_correct; try apply EARGS; try edone.
  intros [rs'' [E [F [G J]]]].
  assert(rs''#r1 = Vptr p). by rewrite J; vauto.
  econstructor; split.
  left. eapply plus_right. eapply rtl_trace_trans. 
    eexact A. eexact E.  edone.
  eapply exec_Ithread_create; eauto. 
  by rewrite app_ass, G. 
  econstructor; eauto. econstructor; eauto.
Qed.

Definition small_step_cs := small_step_Recep CminorSel.state (step ge).

Let lts := (mklts thread_labels small_step_cs).
Let tlts := (mklts thread_labels (rtl_step tge)).

Inductive rtl_trace_strong : RTL.state -> list thread_event -> RTL.state -> Prop :=
  | rtl_trace_strong_nil: forall s, rtl_trace_strong s nil s
  | rtl_trace_strong_cons : forall st1 lab (st2 : RTL.state) t st3
    (TS: taustep tlts st1 lab st2)
    (NT: lab <> TEtau)
    (TR: rtl_trace_strong st2 t st3),
    rtl_trace_strong st1 (lab :: t) st3.

Inductive ss_match_states:
  small_step_state CminorSel.state -> RTL.state -> Prop :=
| ss_match_states_state: forall css rtls t rtls'
    (MS : match_states css rtls)
    (*TRS: t = nil \/ exists r, exists css', CminorSel.step ge css (t ++ r) css'*)
    (TRT: rtl_trace_strong rtls t rtls'),
      ss_match_states (SSState _ css t) rtls'
| ss_match_states_stuck: forall rtls,
      ss_match_states (SSStuck _) rtls.

Inductive ss_lt_state: 
  small_step_state CminorSel.state ->
  small_step_state CminorSel.state ->
  Prop :=
| ss_lt_state_intro:
    forall s s' t
      (LT: lt_state s s'),
        ss_lt_state (SSState _ s t) (SSState _ s' t).

  
Lemma wf_lt_stuck: Acc ss_lt_state (SSStuck CminorSel.state).
Proof.
  apply Acc_intro.
  intros y LT. inversion LT.
Qed.

Lemma wf_ss_lt_state:
  well_founded ss_lt_state.
Proof.  
  intro a.
  destruct a as [o|].
  set (IH o := Acc ss_lt_state (SSState _ o l)).
  apply (well_founded_ind lt_state_wf IH). unfold IH. clear IH o.
    intros o IH.
    apply Acc_intro.
    intros o' LT.
    destruct o' as [|o']; try (by apply wf_lt_stuck).
    inversion LT; apply IH; assumption. 

  apply wf_lt_stuck.
Qed.

Require Import Libtactics.
Tactic Notation "small_step_Recep_cases" tactic(first) tactic(c) :=
    first; [
      c "StepRecepInter" |
      c "StepRecepInterR" |
      c "StepRecepNext" |
      c "StepRecepNextR" |
      c "StepRecepTau"].


Lemma rtl_trace_to_plus_or_eq:
  forall {s t s'}
    (TR: rtl_trace tge s t s'),
      rtl_trace_plus tge s t s' \/
      s = s' /\ t = nil.
Proof.
  intros.
  inv TR. by right.
  left. econstructor. edone. edone.
  by destruct lab.
Qed.

Remark transl_step_correct2:
  forall S1 t S2 (ST: CminorSel.step ge S1 t S2) R1 (MS: match_states S1 R1),
  exists R2, 
   (RTL.rtl_trace_plus tge R1 t R2 \/ (R1 = R2 /\ t = nil /\ lt_state S2 S1))
      /\ match_states S2 R2.
Proof.
  intros.
  destruct (transl_step_correct _ _ _ ST _ MS) as [s' [[TP | [TR M]] MS']].
    eexists. split. eby left. done.
  destruct (rtl_trace_to_plus_or_eq TR) as [TP | [-> ->]].
    eexists. split. eby left. done.
  eexists. split. right. edone. edone.
Qed.

Lemma rtl_trace_from_plus:
  forall s t s'
    (T: rtl_trace_plus tge s t s'),
    rtl_trace tge s t s'.
Proof.
  intros.
  inv T. rewrite weakcons_app.
  eby econstructor. 
Qed.

Lemma rtl_trace_to_taustar:
  forall s s'
    (T: rtl_trace tge s nil s'),
      taustar tlts s s'.
Proof.
  intros.
  remember (@nil thread_event) as l.
  
  induction T; [by vauto|].
  destruct lab; destruct t; try done; [].
  eauto using taustar_step. 
Qed.

Lemma rtl_trace_from_taustar:
  forall s s'
    (T: taustar tlts s s'),
      rtl_trace tge s nil s'.
Proof.
  intros.
  induction T. by vauto.
  replace (@nil thread_event) with (weakcons TEtau nil) by done.
  eby econstructor.
Qed.

Lemma weakcons_nt:
  forall l t (NT: l <> TEtau),
    weakcons l t = l :: t.
Proof. by intros []. Qed.

Lemma rtl_trace_from_strong:
  forall {s t s'} 
    (T: rtl_trace_strong s t s'),
      rtl_trace tge s t s'.
Proof.
  intros.
  induction T. by vauto.
  destruct TS as [st' [TAU ST]].
  eapply rtl_trace_trans; [eby eapply rtl_trace_from_taustar| |edone].
  eby rewrite <- weakcons_nt by done; econstructor. 
Qed.

Lemma rtl_trace_to_weakstep:
  forall s l s'
    (T: rtl_trace tge s (l :: nil) s'),
      weakstep tlts s l s'.
Proof.
  intros.
  remember (l :: nil) as t.
  induction T. done.
  destruct lab; 
    try by inv Heqt; eexists; eexists; 
      eauto using taustar_refl, rtl_trace_to_taustar.
  eapply steptau_weakstep; eauto.
Qed.

Lemma rtl_trace_det_app:
  forall {s1 t s2 te t' s3}
  (RT:  rtl_trace tge s1 t s2)
  (RT': rtl_trace tge s1 (t ++ te :: t') s3),
    rtl_trace tge s2 (te :: t') s3.
Proof.
  intros.
  induction RT; simpl in *.
    remember (te :: t') as t.
    induction RT'. done.
    destruct lab; try (by inv Heqt; eauto using rtl_trace_step).
    by specialize (IHRT' Heqt); vauto.
  destruct lab as [[] | [] | | | | | | ]; simpl in *;
    try by (inv RT';
      destruct lab as [[] | [] | | | | | | ]; clarify; 
        destruct (rtl_determinate _ _ _ _ _ _ ST ST0); 
          try (inv H); inv H1;  specialize (H0 (refl_equal _)); subst; auto).
  inv RT'. by apply app_cons_not_nil in H1.
  destruct (rtl_determinate _ _ _ _ _ _ ST ST0) as [SK S].
  destruct lab; try done; simpl in *; 
    specialize (S (refl_equal _)); subst; auto.
Qed.  

Lemma rtl_trace_strong_one:
  forall s l s'
    (NL: l <> TEtau)
    (ST: rtl_step tge s l s'),
      rtl_trace_strong s (l :: nil) s'.
Proof.
  intros.
  eby econstructor; vauto; apply step_taustep. 
Qed.

Lemma rtl_trace_cons_decomp:
  forall {s te t s'}
  (RT: rtl_trace tge s (te :: t) s'),
  exists si,
    rtl_trace_strong s (te :: nil) si /\
    rtl_trace tge si t s'.
Proof.
  intros.
  remember (te :: t) as t'.
  induction RT. done.
  destruct lab as [[] | [] | | | | | |]; simpl in *;
    try (eby inv Heqt'; eexists; split; 
      [eapply rtl_trace_strong_one|]).
  destruct (IHRT Heqt' ) as [si (RT1 & RT2)].
  exists si; split; [|edone].
  eapply rtl_trace_strong_cons; [ | by inv RT1 | vauto].
  inv RT1. inv TR. destruct TS as [si' [TAU ST']].
  eby eexists; split; [eapply taustar_step|].
Qed.

Lemma rtl_trace_weakstep:
  forall {s1 t s2 te r s3}
  (RT:  rtl_trace tge s1 t s2)
  (RT': rtl_trace tge s1 (t ++ te :: r) s3),
  exists s',
    weakstep tlts s2 te s'.
Proof.
  intros.
  pose proof (rtl_trace_det_app RT RT') as RTr.
  destruct (rtl_trace_cons_decomp RTr) as [si [RT1 RT2]].
  eauto using rtl_trace_to_weakstep, @rtl_trace_from_strong.
Qed.

Lemma rtl_trace_from_weakstep:
  forall s te s'
    (NT : te <> TEtau)
    (WS : weakstep tlts s te s'),
      rtl_trace tge s (te :: nil) s'.
Proof.
  intros. destruct WS as [s1 [s2 (TAU1 & ST & TAU2)]].
  eapply rtl_trace_trans.
      eby eapply rtl_trace_from_taustar.
    eapply rtl_trace_step . edone.
    eby eapply rtl_trace_from_taustar.
  eby destruct te.
Qed.

Lemma rtl_trace_app_strong:
  forall st1 t1 st2 te t2 st3
    (RT1: rtl_trace tge st1 t1 st2)
    (RT2: rtl_trace_strong st2 (te :: t2) st3),
      rtl_trace_strong st1 (t1 ++ te :: t2) st3.
Proof.
  intros.
  induction RT1. done.
  specialize (IHRT1 RT2).
  destruct (thread_event_eq_dec lab TEtau) as [->|N]; simpl.
    inversion IHRT1; subst. by apply app_cons_not_nil in H1.
    econstructor; try edone.
    eapply taustar_taustep. eby apply steptau_taustar. done.
  rewrite weakcons_nt by done. simpl.
  econstructor; try edone. eby eapply step_taustep.
Qed.

Theorem fw_sim:
  forward_sim lts tlts ss_match_states ss_lt_state.
Proof.
  split.
  (* Well-foundedness *)
  apply wf_ss_lt_state.
  (* Simulation *)
  intros until 0; simpl. intros ST MS.

  (small_step_Recep_cases (destruct ST) Case).
  
  Case "StepRecepInter".
    destruct TS as [stB [te' [tb TS]]].
    inv MS. (* destruct TRS as [-> | [r [css' ST]]]. *)
    destruct (transl_step_correct2 _ _ _ TS _ MS0) 
      as [R' [[TP | (-> & E & LT)] MS']].
    (* plus step *)    
    right; left. apply rtl_trace_from_plus in TP.
    pose proof (rtl_trace_det_app (rtl_trace_from_strong TRT) TP) as RTr.
    destruct (rtl_trace_cons_decomp RTr) as [si [RT1 RT2]].
    eexists. split. eauto using rtl_trace_to_weakstep, @rtl_trace_from_strong.
    econstructor. edone.
    (* replace (ta ++ te :: te' :: tb) with ((ta ++ te :: nil) ++ (te' :: tb)) in TS. *)
    (* eby right; eexists; eexists. *)
    (* by rewrite app_ass, <- app_comm_cons. *)
    eapply rtl_trace_app_strong. eby eapply rtl_trace_from_strong. done.
    (* measured step *)
    apply sym_eq in E. by apply app_cons_not_nil in E.

  Case "StepRecepInterR".
    destruct TS as [stB [te' [tb TS]]].
    inv MS. (* destruct TRS as [-> | [r [css' ST]]]. *)
    destruct (transl_step_correct2 _ _ _ TS _ MS0) 
      as [R' [[TP | (-> & E & LT)] MS']].
    (* plus step *)    
    right; left. apply rtl_trace_from_plus in TP.
    pose proof (rtl_trace_det_app (rtl_trace_from_strong TRT) TP) as RTr.
    destruct (rtl_trace_cons_decomp RTr) as [si [RT1 RT2]].
    inv RT1. destruct TS0 as [t' [TAU' ST']].
    pose proof (rtl_receptive _ _ _ _ _ ST' SAME) as [s'' ST''].
    eexists. split. eexists; eexists. eauto using taustar_refl. 
    vauto.
    (* measured step *)
    apply sym_eq in E. by apply app_cons_not_nil in E.
    
  Case "StepRecepNext".
    inv MS.
    destruct (transl_step_correct2 _ _ _ TS _ MS0) 
      as [R' [[TP | (-> & E & LT)] MS']].
    (* plus step *)    
    right; left. apply rtl_trace_from_plus in TP.
    pose proof (rtl_trace_det_app (rtl_trace_from_strong TRT) TP) as RTr.
    apply rtl_trace_to_weakstep in RTr.
    exists R'. split. edone.
    econstructor. edone. (* by t. *) vauto.
    (* measured step *)
    apply sym_eq in E. by apply app_cons_not_nil in E. 

  Case "StepRecepNextR".
    inv MS.
    destruct (transl_step_correct2 _ _ _ TS _ MS0) 
      as [R' [[TP | (-> & E & LT)] MS']].
    (* plus step *)    
    right; left. apply rtl_trace_from_plus in TP.
    pose proof (rtl_trace_det_app (rtl_trace_from_strong TRT) TP) as RTr.
    apply rtl_trace_to_weakstep in RTr.
    destruct RTr as [s1 [s2 (TAU1 & ST' & TAU2)]].
    pose proof (rtl_receptive _ _ _ _ _ ST' SAME) as [s'' ST''].
    eexists. split. eexists; eexists. eauto using taustar_refl. 
    vauto.
    apply sym_eq in E. by apply app_cons_not_nil in E. 
    
  Case "StepRecepTau".
    inv MS.
    destruct (transl_step_correct2 _ _ _ TS _ MS0) 
      as [R' [[TP | (-> & E & LT)] MS']].
    (* plus step *)
    right; left.
    exists R'. split.
      inv TP. destruct t1; try done. destruct t2; try done.
      inv TRT. eexists; eexists; split. apply taustar_refl.
      split. edone. eby apply rtl_trace_to_taustar.
    eby econstructor; [|vauto].
    (* measured stutter step *)
    inv TRT.
    right; right. 
    split. done.
    split. econstructor. edone. vauto.
    done.
Qed.

Definition bsim_rel := @bsr _ lts tlts ss_match_states.
Definition bsim_order := @bsc _ tlts.

Lemma my_backward_sim:
  backward_sim lts tlts false bsim_rel bsim_order.
Proof.
  apply (@forward_to_backward_sim thread_labels lts tlts 
            (SEM_receptive cms_sem _) (rtl_determinate tge) (cms_progress_dec ge)
            ss_match_states ss_lt_state fw_sim). 
Qed.

Lemma init_sim_succ:
  forall {p vals tinit},
    rtl_init tge p vals = Some tinit ->
    exists sinit, cms_init ge p vals = Some sinit /\ bsim_rel tinit sinit.
Proof.
  intros p vals tinit INIT. unfold cms_init, rtl_init in *.
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  fold CminorSel.fundef fundef in *.
  repeat (destruct Genv.find_funct_ptr); clarify.
  destruct f0; destruct f; pose proof MF as MF'; monadInv MF; clarify.
  unfold transl_function in EQ.
  destruct reserve_labels. 
  destruct Zgt_bool; [done|].
  destruct Zlt_bool; [done|].
  destruct transl_fun; [done|].
  destruct p0; inv EQ; simpl in INIT |- *.
  destruct beq_nat; [|done].
  eexists; split. edone.
  inv INIT.
  apply fsr_in_bsr.
  econstructor; [|apply rtl_trace_strong_nil].
  econstructor; eauto. constructor. 
Qed.

Lemma init_sim_fail:
  forall p vals,
    rtl_init tge p vals = None ->
    cms_init ge p vals = None.
Proof.
  intros p vals INIT. unfold cms_init, rtl_init in *.
  pose proof TRANSF as (MG & MF).
  specialize (MF p).
  fold CminorSel.fundef fundef in *.
  repeat destruct (Genv.find_funct_ptr); clarify. 
  destruct f0; monadInv MF; [|done].
  unfold transl_function in EQ.
  destruct reserve_labels. 
  destruct Zgt_bool; [done|].
  destruct Zlt_bool; [done|].
  destruct transl_fun; [done|].
  destruct p0; inv EQ; simpl in INIT |- *.
  by destruct beq_nat.
Qed.

End CORRECTNESS.

Definition rtlgen_match_prg p p' := transl_program false p = OK p'.


(** The whole-system backward simulation for the [RTLgen] phase. *)
Theorem rtlgen_sim Mm : Sim.sim Mm Mm cms_sem rtl_sem rtlgen_match_prg.
Proof.
  eapply (MCsim.sim (false_pure_load_cond Mm) 
            cms_sem rtl_sem genv_rel bsim_rel (fun _ => bsim_order)); 
  intros; simpl in *; 
  eauto using init_sim_succ, init_sim_fail, my_backward_sim.
  - destruct GENVR as [GR FR]. rewrite GR.
    by rewrite (transform_partial_program_main _ _ MP).
  - eapply Genv.exists_matching_genv_and_mem_rev 
      with (match_var := fun a b => a = b), INIT.
    by apply transform_partial_program_match, MP.
Qed.

