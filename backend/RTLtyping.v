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

(** Typing rules and a type inference algorithm for RTL. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Ast.
Require Import Op.
Require Import Registers.
Require Import Globalenvs.
Require Import Values.
Require Import Mem.
Require Import Integers.
Require Import Events.
Require Import RTL.
Require Conventions.
Require Import Libtactics.

(** * The type system *)

(** Like Cminor and all intermediate languages, RTL can be equipped with
  a simple type system that statically guarantees that operations
  and addressing modes are applied to the right number of arguments
  and that the arguments are of the correct types.  The type algebra
  is trivial, consisting of the two types [Tint] (for integers and pointers)
  and [Tfloat] (for floats).  

  Additionally, we impose that each pseudo-register has the same type
  throughout the function.  This requirement helps with register allocation,
  enabling each pseudo-register to be mapped to a single hardware register
  or stack location of the correct type.

  Finally, we also check that the successors of instructions
  are valid, i.e. refer to non-empty nodes in the CFG.

  The typing judgement for instructions is of the form [wt_instr f env
  instr], where [f] is the current function (used to type-check
  [Ireturn] instructions) and [env] is a typing environment
  associating types to pseudo-registers.  Since pseudo-registers have
  unique types throughout the function, the typing environment does
  not change during type-checking of individual instructions.  One
  point to note is that we have one polymorphic operator, [Omove],
  which can work over both integers and floats.
*)

Definition regenv := reg -> typ.

Section WT_INSTR.

Variable env: regenv.
Variable funct: function.

Definition valid_successor (s: node) : Prop :=
  exists i, funct.(fn_code)!s = Some i.

Inductive wt_instr : instruction -> Prop :=
  | wt_Inop:
      forall s,
      valid_successor s ->
      wt_instr (Inop s)
  | wt_Iopmove:
      forall r1 r s,
      env r1 = env r ->
      valid_successor s ->
      wt_instr (Iop Omove (r1 :: nil) r s)
  | wt_Iop:
      forall op args res s,
      op <> Omove ->
      (List.map env args, env res) = type_of_operation op ->
      valid_successor s ->
      wt_instr (Iop op args res s)
  | wt_Iload:
      forall chunk addr args dst s,
      List.map env args = type_of_addressing addr ->
      env dst = type_of_chunk chunk ->
      valid_successor s ->
      wt_instr (Iload chunk addr args dst s)
  | wt_Istore:
      forall chunk addr args src s,
      List.map env args = type_of_addressing addr ->
      env src = type_of_chunk chunk ->
      valid_successor s ->
      wt_instr (Istore chunk addr args src s)
  | wt_Icall:
      forall sig ros args res s,
      match ros with inl r => env r = Tint | inr s => True end ->
      List.map env args = sig.(sig_args) ->
      env res = proj_sig_res sig ->
      valid_successor s ->
      wt_instr (Icall sig ros args res s)
  | wt_Icond:
      forall cond args s1 s2,
      List.map env args = type_of_condition cond ->
      valid_successor s1 ->
      valid_successor s2 ->
      wt_instr (Icond cond args s1 s2)
  | wt_Ireturn: 
      forall optres,
      option_map env optres = funct.(fn_sig).(sig_res) ->
      wt_instr (Ireturn optres)
  | wt_Iatomic:
      forall s args res op,
      (List.map env args, env res) = type_of_atomic_statement op ->      
      valid_successor s ->
      wt_instr (Iatomic op args res s)
  | wt_Ifence:
      forall s,
      valid_successor s ->
      wt_instr (Ifence s)
  | wt_Ithreadcreate:
      forall fn arg s,
      env fn = Tint ->
      env arg = Tint ->
      valid_successor s ->
      wt_instr (Ithreadcreate fn arg s).

End WT_INSTR.

(** A function [f] is well-typed w.r.t. a typing environment [env],
   written [wt_function env f], if all instructions are well-typed,
   parameters agree in types with the function signature, and
   parameters are pairwise distinct. *)

Record wt_function (f: function) (env: regenv): Prop :=
  mk_wt_function {
    wt_params:
      List.map env f.(fn_params) = f.(fn_sig).(sig_args);
    wt_norepet:
      NoDup f.(fn_params);
    wt_instrs:
      forall pc instr, 
      f.(fn_code)!pc = Some instr -> wt_instr env f instr;
    wt_entrypoint:
      valid_successor f f.(fn_entrypoint)
}.

Inductive wt_fundef: fundef -> Prop :=
  | wt_fundef_external: forall ef,
      wt_fundef (External ef)
  | wt_function_internal: forall f env,
      wt_function f env ->
      wt_fundef (Internal f).

Definition wt_genv (ge: genv): Prop :=
  forall v f, Genv.find_funct ge v = Some f -> wt_fundef f.

(** * Type inference *)

(** There are several ways to ensure that RTL code is well-typed and
  to obtain the typing environment (type assignment for pseudo-registers)
  needed for register allocation.  One is to start with well-typed Cminor
  code and show type preservation for RTL generation and RTL optimizations.
  Another is to start with untyped RTL and run a type inference algorithm
  that reconstructs the typing environment, determining the type of
  each pseudo-register from its uses in the code.  We follow the second
  approach.

  We delegate the task of determining the type of each pseudo-register
  to an external ``oracle'': a function written in Caml and not
  proved correct.  We verify the returned type environment using
  the following Coq code, which we will prove correct. *)

Parameter infer_type_environment:
  function -> list (node * instruction) -> option regenv.

(** ** Algorithm to check the correctness of a type environment *)

Section TYPECHECKING.

Variable funct: function.
Variable env: regenv.

Definition check_reg (r: reg) (ty: typ): bool :=
  if typ_eq_dec (env r) ty then true else false.

Fixpoint check_regs (rl: list reg) (tyl: list typ) {struct rl}: bool :=
  match rl, tyl with
  | nil, nil => true
  | r1::rs, ty::tys => check_reg r1 ty && check_regs rs tys
  | _, _ => false
  end.

Definition check_op (op: operation) (args: list reg) (res: reg): bool :=
  let (targs, tres) := type_of_operation op in
  check_regs args targs && check_reg res tres.

Definition check_astmt (op: atomic_statement) (args: list reg) (res: reg): bool :=
  let (targs, tres) := type_of_atomic_statement op in
  check_regs args targs && check_reg res tres.

Definition check_successor (s: node) : bool :=
  match funct.(fn_code)!s with None => false | Some i => true end.

Definition check_instr (i: instruction) : bool :=
  match i with
  | Inop s =>
      check_successor s
  | Iop Omove (arg::nil) res s =>
      if typ_eq_dec (env arg) (env res) 
      then check_successor s
      else false
  | Iop Omove args res s =>
      false
  | Iop op args res s =>
      check_op op args res && check_successor s
  | Iload chunk addr args dst s =>
      check_regs args (type_of_addressing addr)
      && check_reg dst (type_of_chunk chunk)
      && check_successor s
  | Istore chunk addr args src s =>
      check_regs args (type_of_addressing addr)
      && check_reg src (type_of_chunk chunk)
      && check_successor s
  | Icall sig ros args res s =>
      match ros with inl r => check_reg r Tint | inr s => true end
      && check_regs args sig.(sig_args)
      && check_reg res (proj_sig_res sig)
      && check_successor s
  | Icond cond args s1 s2 =>
      check_regs args (type_of_condition cond)
      && check_successor s1
      && check_successor s2
  | Ireturn optres =>
      match optres, funct.(fn_sig).(sig_res) with
      | None, None => true
      | Some r, Some t => check_reg r t
      | _, _ => false
      end
  | Iatomic ros args res s =>
      check_astmt ros args res && check_successor s
  | Ifence s =>
      check_successor s
  | Ithreadcreate fn arg s =>
      check_reg fn Tint
      && check_reg arg Tint
      && check_successor s
  end.

Definition check_params_norepet (params: list reg): bool :=
  if nodup_dec Reg.eq params then true else false.

Fixpoint check_instrs (instrs: list (node * instruction)) : bool :=
  match instrs with
  | nil => true
  | (pc, i) :: rem => check_instr i && check_instrs rem
  end.

(** ** Correctness of the type-checking algorithm *)

Ltac elimAndb :=
  match goal with
  | [ H: _ && _ = true |- _ ] =>
      elim (andb_prop _ _ H); clear H; intros; elimAndb
  | _ =>
      idtac
  end.

Lemma check_reg_correct:
  forall r ty, check_reg r ty = true -> env r = ty.
Proof.
  unfold check_reg; intros.
  destruct (typ_eq_dec (env r) ty). auto. discriminate.
Qed.

Lemma check_regs_correct:
  forall rl tyl, check_regs rl tyl = true -> List.map env rl = tyl.
Proof.
  induction rl; destruct tyl; simpl; intros.
  auto. discriminate. discriminate.
  elimAndb.
  rewrite (check_reg_correct _ _ H). rewrite (IHrl tyl H0). auto.
Qed.

Lemma check_op_correct:
  forall op args res,
  check_op op args res = true ->
  (List.map env args, env res) = type_of_operation op.
Proof.
  unfold check_op; intros.
  destruct (type_of_operation op) as [targs tres].
  elimAndb. 
  rewrite (check_regs_correct _ _ H).
  rewrite (check_reg_correct _ _ H0).
  auto.
Qed.

Lemma check_astmt_correct:
  forall op args res,
  check_astmt op args res = true ->
  (List.map env args, env res) = type_of_atomic_statement op.
Proof.
  unfold check_astmt; intros.
  destruct (type_of_atomic_statement op) as [targs tres].
  elimAndb. 
  rewrite (check_regs_correct _ _ H).
  rewrite (check_reg_correct _ _ H0).
  auto.
Qed.

Lemma check_successor_correct:
  forall s,
  check_successor s = true -> valid_successor funct s.
Proof.
  intro; unfold check_successor, valid_successor.
  destruct (fn_code funct)!s; intro.
  exists i; auto.
  discriminate.
Qed.

Lemma check_instr_correct:
  forall i, check_instr i = true -> wt_instr env funct i.
Proof.
  unfold check_instr; intros; destruct i; elimAndb.
  (* nop *)
  constructor. apply check_successor_correct; auto.
  (* op *)
  destruct o; elimAndb;
  try (apply wt_Iop; [ congruence
                     | apply check_op_correct; auto
                     | apply check_successor_correct; auto ]).
  destruct l; try discriminate. destruct l; try discriminate.
  destruct (typ_eq_dec (env r0) (env r)); try discriminate.
  apply wt_Iopmove; auto. apply check_successor_correct; auto.
  (* load *)
  constructor. apply check_regs_correct; auto. apply check_reg_correct; auto.
  apply check_successor_correct; auto.
  (* store *)
  constructor. apply check_regs_correct; auto. apply check_reg_correct; auto.
  apply check_successor_correct; auto.
  (* call *)
  constructor.
  destruct s0; auto. apply check_reg_correct; auto.
  apply check_regs_correct; auto.
  apply check_reg_correct; auto.
  apply check_successor_correct; auto.
  (* cond *)
  constructor. apply check_regs_correct; auto.
  apply check_successor_correct; auto.
  apply check_successor_correct; auto.
  (* return *)
  constructor. 
  destruct o; simpl; destruct funct.(fn_sig).(sig_res); try discriminate.
  rewrite (check_reg_correct _ _ H); auto.
  auto.
  (* threadcreate *)
  constructor; try (by apply check_reg_correct); [].
  by apply check_successor_correct.
  (* atomic *)
  constructor.
  by apply check_astmt_correct.
  by apply check_successor_correct.
  (* fence *)
  constructor.
  by apply check_successor_correct.
Qed.

Lemma check_instrs_correct:
  forall instrs,
  check_instrs instrs = true ->
  forall pc i, In (pc, i) instrs -> wt_instr env funct i.
Proof.
  induction instrs; simpl; intros.
  elim H0.
  destruct a as [pc' i']. elimAndb. 
  elim H0; intro.
  inversion H2; subst pc' i'. apply check_instr_correct; auto.
  eauto.
Qed.

End TYPECHECKING.

(** ** The type inference function **)

Open Scope string_scope.

Definition type_function (f: function): res regenv :=
  let instrs := PTree.elements f.(fn_code) in
  match infer_type_environment f instrs with
  | None => Error (msg "RTL type inference error")
  | Some env =>
      if check_regs env f.(fn_params) f.(fn_sig).(sig_args)
      && check_params_norepet f.(fn_params)
      && check_instrs f env instrs
      && check_successor f f.(fn_entrypoint)
      then OK env
      else Error (msg "RTL type checking error")
  end.

Lemma type_function_correct:
  forall f env,
  type_function f = OK env ->
  wt_function f env.
Proof.
  unfold type_function; intros until env.
  set (instrs := PTree.elements f.(fn_code)).
  case (infer_type_environment f instrs).
  intro env'. 
  caseEq (check_regs env' f.(fn_params) f.(fn_sig).(sig_args)); intro; simpl; try congruence.
  caseEq (check_params_norepet f.(fn_params)); intro; simpl; try congruence.
  caseEq (check_instrs f env' instrs); intro; simpl; try congruence.
  caseEq (check_successor f (fn_entrypoint f)); intro; simpl; try congruence.
  intro EQ; inversion EQ; subst env'.
  constructor. 
  apply check_regs_correct; auto.
  unfold check_params_norepet in H0. 
  destruct (nodup_dec Reg.eq (fn_params f)). auto. discriminate.
  intros. eapply check_instrs_correct. eauto. 
  unfold instrs. apply PTree.elements_correct. eauto.
  apply check_successor_correct. auto.
  congruence.
Qed.

(** * Type preservation during evaluation *)

(** The type system for RTL is not sound in that it does not guarantee
  progress: well-typed instructions such as [Icall] can fail because
  of run-time type tests (such as the equality between callee and caller's
  signatures).  However, the type system guarantees a type preservation
  property: if the execution does not fail because of a failed run-time
  test, the result values and register states match the static
  typing assumptions.  This preservation property will be useful
  later for the proof of semantic equivalence between
  [Machabstr] and [Machconcr].
  Even though we do not need it for [RTL], we show preservation for [RTL]
  here, as a warm-up exercise and because some of the lemmas will be
  useful later. *)

Definition wt_regset (env: regenv) (rs: regset) : Prop :=
  forall r, Val.has_type (rs#r) (env r).

Lemma wt_regset_assign:
  forall env rs v r,
  wt_regset env rs ->
  Val.has_type v (env r) ->
  wt_regset env (rs#r <- v).
Proof.
  intros; red; intros. 
  rewrite Regmap.gsspec.
  case (peq r0 r); intro.
  subst r0. assumption.
  apply H.
Qed.

Lemma wt_regset_list:
  forall env rs,
  wt_regset env rs ->
  forall rl, Val.has_type_list (rs##rl) (List.map env rl).
Proof.
  induction rl; simpl; try done.
  rewrite IHrl; rewrite andb_b_true; apply H.
Qed.  

Lemma wt_init_regs:
  forall env rl args,
  Val.has_type_list args (List.map env rl) ->
  wt_regset env (init_regs args rl).
Proof.
  induction rl; destruct args; simpl; intuition; try done.
  by red; intros; rewrite Regmap.gi. 
  destruct (andP H); apply wt_regset_assign; auto.
Qed.

Inductive wt_stackframes: list stackframe -> option typ -> Prop :=
  | wt_stackframes_nil:
      wt_stackframes nil (Some Tint)
  | wt_stackframes_cons:
      forall s res f sp pc rs env tyres,
      wt_function f env ->
      wt_regset env rs ->
      env res = match tyres with None => Tint | Some t => t end ->
      wt_stackframes s (sig_res (fn_sig f)) ->
      wt_stackframes (Stackframe res (fn_code f) sp pc rs :: s) tyres.

Inductive wt_state: state -> Prop :=
  | wt_state_intro:
      forall s f sp pc rs env
        (WT_STK: wt_stackframes s (sig_res (fn_sig f)))
        (WT_FN: wt_function f env)
        (WT_RS: wt_regset env rs),
      wt_state (State s (fn_code f) sp pc rs)
  | wt_state_call:
      forall s f args,
      wt_stackframes s (sig_res (funsig f)) ->
      wt_fundef f ->
      Val.has_type_list args (sig_args (funsig f)) ->
      wt_state (Callstate s f args)
  | wt_state_return:
      forall s v tyres,
      wt_stackframes s tyres ->
      Val.has_type v (match tyres with None => Tint | Some t => t end) ->
      wt_state (Returnstate s v)
  | wt_state_blocked:
      forall s efsig,
      wt_stackframes s (sig_res efsig) ->
      wt_state (Blockedstate s efsig).

Section SUBJECT_REDUCTION.

Variable (ge : genv).

Hypothesis wt_ge: wt_genv ge.

Lemma find_function_wt:
  forall ros rs f,
  find_function ge ros rs = Some f -> wt_fundef f.
Proof.
  unfold wt_genv in wt_ge.
  intros ros rs f H. 
  destruct ros as [|i]; simpl in H; [eby eapply wt_ge|]. 
  destruct (Genv.find_symbol ge i) as [p|]; try done.
  eby specialize (wt_ge (Vptr p)); simpl in wt_ge; eapply wt_ge.
Qed.

Lemma subject_reduction:
  forall st1 t st2, rtl_step ge st1 t st2 ->
  forall (WT: wt_state st1), wt_state st2.
Proof.
  (rtl_step_cases (destruct 1) Case); intros; inv WT;
  try (generalize (wt_instrs _ _ WT_FN pc _ H);
       intro WT_INSTR;
       inv WT_INSTR);
  try (by econstructor; eauto).
  Case "exec_Iop".
  econstructor; eauto.
  apply wt_regset_assign. auto. 
  simpl in H0. inv H0. rewrite <- H3. apply WT_RS.
  econstructor; eauto.
  apply wt_regset_assign. auto.
  replace (env res) with (snd (type_of_operation op)).
  apply type_of_operation_sound with fundef ge rs##args sp; auto.
  rewrite <- H6. reflexivity.
  Case "exec_Iload".
  by econstructor; eauto; apply wt_regset_assign; [|rewrite H8].
  Case "exec_Icall".
  assert (wt_fundef f); [eby eapply find_function_wt|].
  econstructor; eauto.
  econstructor; eauto.
  rewrite <- H7. apply wt_regset_list. auto.
  Case "exec_Ireturn".
  econstructor; eauto. 
  destruct or; simpl in *; try done.
  by rewrite <- H1; apply WT_RS.
  Case "exec_Iatomic".
  econstructor; eauto; [].
  apply wt_regset_assign. auto.
  by inv ASME; inv H2; rewrite H4.
  Case "exec_function_internal_empty".
  simpl in *. inv H4. inversion H1; subst.  
  econstructor; eauto.
  apply wt_init_regs; auto. rewrite wt_params0; auto.
  Case "exec_function_internal_nonempty".
  simpl in *. inv H8. inversion H0; subst.  
  econstructor; eauto.
  apply wt_init_regs; auto. rewrite wt_params0; auto.
  Case "exec_return".
  inv H1. econstructor; eauto. 
  apply wt_regset_assign; auto. congruence. 
Qed.

End SUBJECT_REDUCTION.
