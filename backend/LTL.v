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

(** The LTL intermediate language: abstract syntax and semantics.

  LTL (``Location Transfer Language'') is the target language
  for register allocation and the source language for linearization. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Pointers. 
Require Import Values.
Require Import Events.
Require Import Mem.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Import Memcomp.
Require Import Libtactics.

(** * Abstract syntax *)

(** LTL is close to RTL, but uses locations instead of pseudo-registers. *)

Definition node := positive.

Inductive instruction: Type :=
  | Lnop: node -> instruction
  | Lop: operation -> list loc -> loc -> node -> instruction
  | Lload: memory_chunk -> addressing -> list loc -> loc -> node -> instruction
  | Lstore: memory_chunk -> addressing -> list loc -> loc -> node -> instruction
  | Lcall: signature -> loc + ident -> list loc -> loc -> node -> instruction
  | Lcond: condition -> list loc -> node -> node -> instruction
  | Lreturn: option loc -> instruction
  | Lthreadcreate: loc -> loc -> node -> instruction
  | Latomic: atomic_statement -> list loc -> loc -> node -> instruction
  | Lfence: node -> instruction.

Definition code: Type := PTree.t instruction.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list loc;
  fn_stacksize: int (* was Z *);
  fn_code: code;
  fn_entrypoint: node
}.

Definition fundef := Ast.fundef function.

Definition program := Ast.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.

(** * Operational semantics *)

Definition genv := Genv.t fundef.
Definition locset := Locmap.t.

Definition locmap_optget (ol: option loc) (dfl: val) (ls: locset) : val :=
  match ol with
  | None => dfl
  | Some l => ls l
  end.

Fixpoint init_locs (vl: list val) (rl: list loc) {struct rl} : locset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Locmap.set r1 v1 (init_locs vs rs)
  | _, _ => Locmap.init Vundef
  end.

(** [postcall_locs ls] returns the location set [ls] after a function
  call.  Caller-save registers and temporary registers
  are set to [undef], reflecting the fact that the called
  function can modify them freely. *)

Definition postcall_locs (ls: locset) : locset :=
  fun (l: loc) =>
    match l with
    | R r =>
        if In_dec Loc.eq (R r) Conventions.temporaries then
          Vundef
        else if In_dec Loc.eq (R r) Conventions.destroyed_at_call then
          Vundef
        else
          ls (R r)
    | S s => ls (S s)
    end.

Definition postthreadcreate_locs (ls: locset) : locset :=
  fun (l: loc) =>
    match l with
    | R r =>
        if In_dec Loc.eq (R r) Conventions.temporaries then
          Vundef
        else if In_dec Loc.eq (R r) Conventions.destroyed_at_threadcreate then
          Vundef
        else
          ls (R r)
    | S s => ls (S s)
    end.

Definition undef_temps (ls: locset) := Locmap.undef temporaries ls.

(** LTL execution states. *)

Inductive stackframe : Type :=
  | Stackframe:
      forall (res: loc)            (**r where to store the result *)
             (f: function)         (**r calling function *)
             (sp: option pointer)  (**r stack pointer in calling function *)
             (ls: locset)          (**r location state in calling function *)
             (pc: node),           (**r program point in calling function *)
      stackframe.

Inductive state : Type :=
  | State:
      forall (stack: list stackframe)  (**r call stack *)
             (f: function)             (**r function currently executing *)
             (sp: option pointer)      (**r stack pointer *)
             (pc: node)                (**r current program point *)
             (ls: locset),             (**r location state *)
      state
  | Callstate:
      forall (stack: list stackframe)  (**r call stack *)
             (f: fundef)               (**r function to call *)
             (args: list val),         (**r arguments to the call *)
      state
  | Returnstate:
      forall (stack: list stackframe)  (**r call stack *)
             (v: val),                 (**r return value for the call *)
      state
  | Blockedstate:
      forall (stack: list stackframe)  (**r call stack *)
        (sig: signature),              (**r function called *)
        state.

Section RELSEM.

Variable ge: genv.

Definition find_function (los: loc + ident) (rs: locset) : option fundef :=
  match los with
  | inl l => Genv.find_funct ge (rs l)
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

(** The LTL transition relation is very similar to that of RTL,
  with locations being used in place of pseudo-registers.
  The main difference is for the [call] instruction: caller-save
  registers are set to [Vundef] across the call, using the [postcall_locs]
  function defined above.  This forces the LTL producer to avoid
  storing values live across the call in a caller-save register. *)

Inductive ltl_step: state -> thread_event -> state -> Prop :=
  | exec_Lnop:
      forall s f sp pc rs pc',
      (fn_code f)!pc = Some(Lnop pc') ->
      ltl_step (State s f sp pc rs) 
        TEtau (State s f sp pc' rs)
  | exec_Lop:
      forall s f sp pc rs op args res pc' rs' v,
      (fn_code f)!pc = Some(Lop op args res pc') ->
      eval_operation ge sp op (map rs args) = Some v ->
      rs' = Locmap.set res v (undef_temps rs) ->
      ltl_step (State s f sp pc rs)
        TEtau (State s f sp pc' rs') 
  | exec_Lload:
      forall s f sp pc rs chunk addr args dst pc' rs' a v,
      (fn_code f)!pc = Some(Lload chunk addr args dst pc') ->
      rs' = (Locmap.set dst v (undef_temps rs)) ->
      eval_addressing ge sp addr (map rs args) = Some (Vptr a) ->
      Val.has_type v (type_of_chunk chunk) ->
      ltl_step (State s f sp pc rs)
        (TEmem (MEread a chunk v))
        (State s f sp pc' rs') 
  | exec_Lstore:
      forall s f sp pc rs chunk v addr args src pc' a,
      (fn_code f)!pc = Some(Lstore chunk addr args src pc') ->
      eval_addressing ge sp addr (map rs args) = Some (Vptr a) ->
      v = Val.conv (rs src) (type_of_chunk chunk) ->
      ltl_step (State s f sp pc rs)
        (TEmem (MEwrite a chunk (cast_value_to_chunk chunk v))) 
        (State s f sp pc' (undef_temps rs))
  | exec_Lcall:
      forall s f sp pc rs sig ros args res pc' f',
      (fn_code f)!pc = Some(Lcall sig ros args res pc') ->
      find_function ros rs = Some f' ->
      funsig f' = sig ->
      ltl_step (State s f sp pc rs)
        TEtau (Callstate (Stackframe res f sp (postcall_locs rs) pc' :: s)
                      f' (List.map rs args))
  | exec_Lcond_true:
      forall s f sp pc rs cond args ifso ifnot,
      (fn_code f)!pc = Some(Lcond cond args ifso ifnot) ->
      eval_condition cond (map rs args) = Some true ->
      ltl_step (State s f sp pc rs)
        TEtau (State s f sp ifso (undef_temps rs))
  | exec_Lcond_false:
      forall s f sp pc rs cond args ifso ifnot,
      (fn_code f)!pc = Some(Lcond cond args ifso ifnot) ->
      eval_condition cond (map rs args) = Some false ->
      ltl_step (State s f sp pc rs)
        TEtau (State s f sp ifnot (undef_temps rs))
  | exec_Lreturn:
      forall s f sp pc rs or lab,
      (fn_code f)!pc = Some(Lreturn or) ->
      lab = match sp with None => TEtau | 
              Some stk => TEmem (MEfree stk MObjStack) end ->
      ltl_step (State s f sp pc rs)
        lab
        (Returnstate s (locmap_optget or Vundef rs))
  | exec_Lthreadcreate:
      forall s f sp pc rs fn pfn arg pc',
      (fn_code f)!pc = Some(Lthreadcreate fn arg pc') ->
      rs fn = Vptr pfn -> 
      ltl_step 
        (State s f sp pc rs)
        (TEstart pfn (rs arg :: nil))
        (State s f sp pc' (postthreadcreate_locs rs))
  | exec_Latomic:
      forall s f sp pc rs op args res pc' v rs' lab
      (H : (fn_code f)!pc = Some(Latomic op args res pc'))
      (ASME : atomic_statement_mem_event op (map rs args) v lab)
      (Ers' : rs' = Locmap.set res v (undef_temps rs))
      (HTv : Val.has_type v Tint),
      ltl_step 
        (State s f sp pc rs)
        (TEmem lab)
        (State s f sp pc' rs')
  | exec_Lfence:
      forall s f sp pc rs pc'
      (H : (fn_code f)!pc = Some(Lfence pc')),
      ltl_step 
        (State s f sp pc rs)
        (TEmem MEfence)
        (State s f sp pc' rs)
  | exec_function_internal_empty:
      forall s f args epoint locs,
      f.(fn_stacksize) = Int.zero ->
      epoint = f.(fn_entrypoint) ->
      locs = init_locs args f.(fn_params) ->
      ltl_step (Callstate s (Internal f) args)
        (TEtau)
        (State s f None epoint locs)
  | exec_function_internal_nonempty:
      forall s f args stk stksize epoint locs,
      stksize = f.(fn_stacksize) ->
      epoint  = f.(fn_entrypoint) ->
      locs    = (init_locs args f.(fn_params)) ->
      stksize <> Int.zero ->
      ltl_step (Callstate s (Internal f) args)
        (TEmem (MEalloc stk stksize MObjStack))
        (State s f (Some stk) epoint locs)
  | exec_function_external_call:
      forall s ef args eargs lab,
      lab = TEext (Ecall ef.(ef_id) eargs (*(Val.conv_list args ef.(ef_sig).(sig_args))*) ) ->
      args = map val_of_eval eargs ->
      ltl_step (Callstate s (External ef) args) lab
         (Blockedstate s ef.(ef_sig))
  | exec_function_external_return:
      forall s efsig typ res eres,
      typ = (match sig_res efsig with Some x => x | None => Tint end) ->
      Val.has_type res typ ->
      res = val_of_eval eres ->
      ltl_step (Blockedstate s efsig)
         (TEext (Ereturn typ eres))
         (Returnstate s res)
  | exec_return:
      forall res f sp rs pc s vres,
      ltl_step (Returnstate (Stackframe res f sp rs pc :: s) vres)
        TEtau (State s f sp pc (Locmap.set res vres rs))
  | exec_return_exit:
      forall vres,
      ltl_step (Returnstate nil vres)
        TEexit (Returnstate nil vres).

Definition ltl_init  (p : pointer) (vs : list val) : option state :=
  match Genv.find_funct_ptr ge p with
   | Some (Internal f)  => 
       if beq_nat (length vs) (length f.(fn_sig).(sig_args))
         then Some (Callstate nil (Internal f) (Val.conv_list vs f.(fn_sig).(sig_args)))
         else None
   | _ => None
  end.

(* JS PARAM:
Definition ltl_init  (p : pointer) (vs : list val) : option state :=
  match Genv.find_funct_ptr ge p with
   | Some (Internal f)  => 
       match f.(fn_sig).(sig_args) with
         | nil => Some (Callstate nil (Internal f) nil)
         | _ => None
       end
   | _ => None
  end.*)

End RELSEM.

Tactic Notation "ltl_step_cases" tactic(first) tactic(c) :=
    first; [
      c "exec_Lnop" |
      c "exec_Lop" |
      c "exec_Lload" |
      c "exec_Lstore" |
      c "exec_Lcall" |
      c "exec_Lcond_true" |
      c "exec_Lcond_false" |
      c "exec_Lreturn" |
      c "exec_Lthreadcreate" |
      c "exec_Latomic" |
      c "exec_Lfence" |
      c "exec_function_internal_empty" |
      c "exec_function_internal_nonempty" |
      c "exec_function_external_call" |
      c "exec_function_external_return" |
      c "exec_return" |
      c "exec_return_exit"].


Definition ltl_ge_init (p : program) (ge : genv) (m : mem) :=
  Genv.globalenv_initmem p ge low_mem_restr m.


(** Execution of a whole program boils down to invoking its main
  function.  The result of the program is the return value of the
  main function, to be found in the machine register dictated
  by the calling conventions. *)

(*
Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f,
      let ge := Genv.globalenv p in
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      initial_state p (Callstate nil f nil).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall n,
      final_state (Returnstate nil (Vint n)) n.

Definition exec_program (p: program) (beh: program_behavior) : Prop :=
  program_behaves step (initial_state p) final_state (Genv.globalenv p) beh.
*)

(** * Operations over LTL *)

(** Computation of the possible successors of an instruction.
  This is used in particular for dataflow analyses. *)

Definition successors_instr (i: instruction) : list node :=
  match i with
  | Lnop s => s :: nil
  | Lop op args res s => s :: nil
  | Lload chunk addr args dst s => s :: nil
  | Lstore chunk addr args src s => s :: nil
  | Lcall sig ros args res s => s :: nil
  | Lcond cond args ifso ifnot => ifso :: ifnot :: nil
  | Lreturn optarg => nil
  | Lthreadcreate fn arg s => s :: nil
  | Latomic aop args res s => s :: nil
  | Lfence s => s :: nil
  end.

Definition successors (f: function): PTree.t (list node) :=
  PTree.map (fun pc i => successors_instr i) f.(fn_code).

(** * TSO machine set up *)

Section LTL_TSO.

Ltac atomic_dtac :=
  match goal with
    | H : atomic_statement_mem_event ?A ?B ?C ?D |- _ => inv H
  end.

Lemma ltl_receptive :
  forall ge l l' s s',
    ltl_step ge s l s' ->
    te_samekind l' l ->
    exists s'', ltl_step ge s l' s''.
Proof.
  intros g l l' s s' Step Te_Samekind.
  inversion Step; 
     subst;
     destruct l'; try destruct ev;
     try destruct sp;
     simpl in *; subst; clarify;
     try rewrite Te_Samekind; 
     try (destruct Te_Samekind; subst);
     try (destruct H3; subst);
     try (eexists; solve [ eassumption | econstructor; try eassumption; auto; done |
             econstructor; try apply H1; edone]);
     atomic_dtac; try done; destruct Te_Samekind as (-> & -> & -> & HTI);
     eexists; (eapply exec_Latomic; [edone | | reflexivity | apply HTI, HTv]).
   (* The following are necessary to get around silly handling
      of existential variables in Coq. *)
   eby rewrite <- H2; econstructor.
   eby rewrite <- H2; econstructor.
   eby rewrite <- H2; econstructor.
   eby rewrite <- H2; econstructor.
Qed.

Ltac determinate_aux_tac :=
  repeat match goal with
    | H' : ?a = _, H'' : ?a = _ |- _ => rewrite H' in H''; clarify
    | H : map val_of_eval ?x = map val_of_eval ?y |- _ => 
        rewrite (map_val_of_eval_eq H); done
    | H :  atomic_statement_mem_event _ _ _ _,
      H' : atomic_statement_mem_event _ _ _ _ |- _ => 
      try (eby clarify'; eapply atomic_statement_determinate);
      rewrite (atomic_statement_determinate_eq H H') in *
  end.

Lemma ltl_determinate:
  forall ge s s' s'' l l',
    ltl_step ge s l s' ->
    ltl_step ge s l' s'' ->
    (te_samekind l l' /\ (l = l' -> s' = s'')).
Proof.
  intros g s s' s'' l l' ST1 ST2.
  split.
  by destruct ST1; inv ST2; simpl; clarify; determinate_aux_tac; destruct sp.

  intro; subst.
  by destruct ST1; inv ST2; clarify; determinate_aux_tac.
Qed.

Require Import Classical.

Lemma ltl_progress_dec:
  forall ge s, (forall s' l', ~ ltl_step ge s l' s') \/
    (exists l', exists s', ltl_step ge s l' s').
Proof.
  intros g s.
  set (P := exists l' : thread_event, exists s' : state, ltl_step g s l' s').
  destruct (classic P). auto.
  left. intros s' l'. revert s'. apply not_ex_all_not.
  revert l'. apply not_ex_all_not. auto.
Qed.


Definition ltl_sem : SEM := 
  mkSEM state genv program 
  ltl_ge_init 
  (@prog_main _ _) (@Genv.find_symbol _) 
  ltl_step ltl_init ltl_progress_dec ltl_receptive ltl_determinate.

End LTL_TSO.
