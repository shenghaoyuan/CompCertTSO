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

(** The LTLin intermediate language: abstract syntax and semantcs *)

(** The LTLin language is a variant of LTL where control-flow is not
    expressed as a graph of basic blocks, but as a linear list of
    instructions with explicit labels and ``goto'' instructions. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Pointers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import Conventions.
Require Import Memcomp.
Require Import Libtactics.

(** * Abstract syntax *)

Definition label := positive.

(** LTLin instructions are similar to those of LTL.
  Except the last three, these instructions continue in sequence
  with the next instruction in the linear list of instructions.
  Unconditional branches [Lgoto] and conditional branches [Lcond]
  transfer control to the given code label.  Labels are explicitly
  inserted in the instruction list as pseudo-instructions [Llabel]. *)

Inductive instruction: Type :=
  | Lop: operation -> list loc -> loc -> instruction
  | Lload: memory_chunk -> addressing -> list loc -> loc -> instruction
  | Lstore: memory_chunk -> addressing -> list loc -> loc -> instruction
  | Lcall: signature -> loc + ident -> list loc -> loc -> instruction
  | Llabel: label -> instruction
  | Lgoto: label -> instruction
  | Lcond: condition -> list loc -> label -> instruction
  | Lreturn: option loc -> instruction
  | Lthreadcreate: loc -> loc -> instruction
  | Latomic: atomic_statement -> list loc -> loc -> instruction
  | Lfence: instruction.

Definition code: Type := list instruction.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list loc;
  fn_stacksize: int (* was Z *);
  fn_code: code
}.

Definition fundef := Ast.fundef function.

Definition program := Ast.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.

Definition genv := Genv.t fundef.
Definition locset := Locmap.t.

(** * Operational semantics *)

(** Looking up labels in the instruction list.  *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Llabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Llabel lbl else instr <> Llabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

(** [find_label lbl c] returns a list of instruction, suffix of the
  code [c], that immediately follows the [Llabel lbl] pseudo-instruction.
  If the label [lbl] is multiply-defined, the first occurrence is
  retained.  If the label [lbl] is not defined, [None] is returned. *)

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
  end.

(** The states of the dynamic semantics are similar to those used
  in the LTL semantics (see module [LTL]).  The only difference
  is that program points [pc] (nodes of the CFG in LTL) become
  code sequences [c] (suffixes of the code of the current function).
*)

Inductive stackframe : Type :=
  | Stackframe:
      forall (res: loc)               (**r where to store the result *)
             (f: function)            (**r calling function *)
             (sp: option pointer)     (**r stack pointer in calling function *)
             (ls: locset)             (**r location state in calling function *)
             (c: code),               (**r program point in calling function *)
      stackframe.

Inductive state : Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r function currently executing *)
             (sp: option pointer)     (**r stack pointer *)
             (c: code)                (**r current program point *)
             (ls: locset),            (**r location state *)
      state
  | Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (args: list val),        (**r arguments to the call *)
      state
  | Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (v: val),                (**r return value for the call *)
      state
  | Blockedstate:
      forall (stack: list stackframe) (**r call stack *)
             (sig: signature),        (**r function called *)
      state.

Section RELSEM.

Variable ge: genv.

Definition find_function (ros: loc + ident) (rs: locset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge (rs r)
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

Inductive ltlin_step: state -> thread_event -> state -> Prop :=
  | exec_Lop:
      forall s f sp op args res b rs v,
      eval_operation ge sp op (map rs args) = Some v ->
      ltlin_step (State s f sp (Lop op args res :: b) rs) TEtau 
        (State s f sp b (Locmap.set res v (undef_temps rs)))
  | exec_Lload:
      forall s f sp chunk addr args dst b rs a v rs',
      eval_addressing ge sp addr (map rs args) = Some (Vptr a) ->
      rs' = (Locmap.set dst v (undef_temps rs)) ->
      Val.has_type v (type_of_chunk chunk) ->
      ltlin_step (State s f sp (Lload chunk addr args dst :: b) rs)
        (TEmem (MEread a chunk v))
        (State s f sp b rs')
  | exec_Lstore:
      forall s f sp chunk v addr args src b rs a,
      eval_addressing ge sp addr (map rs args) = Some (Vptr a) ->
      v = Val.conv (rs src) (type_of_chunk chunk) ->
      ltlin_step (State s f sp (Lstore chunk addr args src :: b) rs)
        (TEmem (MEwrite a chunk (cast_value_to_chunk chunk v))) 
        (State s f sp b (undef_temps rs))
  | exec_Lcall:
      forall s f sp sig ros args res b rs f' args',
      find_function ros rs = Some f' ->
      sig = funsig f' ->
      args' = List.map rs args ->
      ltlin_step (State s f sp (Lcall sig ros args res :: b) rs)
        TEtau (Callstate (Stackframe res f sp (LTL.postcall_locs rs) b :: s) f' args')
  | exec_Llabel:
      forall s f sp lbl b rs,
      ltlin_step (State s f sp (Llabel lbl :: b) rs)
        TEtau (State s f sp b rs)
  | exec_Lgoto:
      forall s f sp lbl b rs b',
      find_label lbl f.(fn_code) = Some b' ->
      ltlin_step (State s f sp (Lgoto lbl :: b) rs)
        TEtau (State s f sp b' rs)
  | exec_Lcond_true:
      forall s f sp cond args lbl b rs b',
      eval_condition cond (map rs args) = Some true ->
      find_label lbl f.(fn_code) = Some b' ->
      ltlin_step (State s f sp (Lcond cond args lbl :: b) rs)
        TEtau (State s f sp b' (undef_temps rs))
  | exec_Lcond_false:
      forall s f sp cond args lbl b rs,
      eval_condition cond (map rs args) = Some false ->
      ltlin_step (State s f sp (Lcond cond args lbl :: b) rs)
        TEtau (State s f sp b (undef_temps rs))
  | exec_Lreturn:
      forall s f sp rs or b lab,
      lab = match sp with 
              | None => TEtau 
              | Some stk => TEmem (MEfree stk MObjStack) end ->
      ltlin_step (State s f sp (Lreturn or :: b) rs) lab
        (Returnstate s (LTL.locmap_optget or Vundef rs))
  | exec_Lthreadcreate:
      forall s f sp fn pfn arg b rs,
      rs fn = Vptr pfn ->
      ltlin_step 
        (State s f sp (Lthreadcreate fn arg :: b) rs) 
        (TEstart pfn (rs arg :: nil))
        (State s f sp b (LTL.postthreadcreate_locs rs))
  | exec_Latomic:
      forall s f sp rs op args res v rs' lab b
      (ASME : atomic_statement_mem_event op (map rs args) v lab)
      (Ers' : rs' = Locmap.set res v (undef_temps rs))
      (HTv : Val.has_type v Tint),
      ltlin_step 
        (State s f sp (Latomic op args res :: b) rs)
        (TEmem lab)
        (State s f sp b rs')
  | exec_Lfence:
      forall s f sp rs b,
      ltlin_step 
        (State s f sp (Lfence :: b) rs)
        (TEmem MEfence)
        (State s f sp b rs)
  | exec_function_internal_empty:
      forall s f args code locs,
      f.(fn_stacksize) = Int.zero -> 
      code = f.(fn_code) ->
      locs = LTL.init_locs args f.(fn_params) ->
      ltlin_step (Callstate s (Internal f) args)
        (TEtau)
        (State s f None code locs)
  | exec_function_internal_nonempty:
      forall s f args stk stksize code locs,
      stksize = f.(fn_stacksize) -> 
      code = f.(fn_code) ->
      locs = LTL.init_locs args f.(fn_params) ->
      stksize <> Int.zero -> 
      ltlin_step (Callstate s (Internal f) args)
        (TEmem (MEalloc stk stksize MObjStack))
        (State s f (Some stk) code locs)
  | exec_function_external_call:
      forall s ef args eargs lab,
      lab = TEext (Ecall ef.(ef_id) eargs) (*Val.conv_list args (sig_args ef.(ef_sig))*) ->
      args = map val_of_eval eargs ->
      ltlin_step (Callstate s (External ef) args) lab
         (Blockedstate s ef.(ef_sig))
  | exec_function_external_return:
      forall s res eres efsig typ,
      typ = (match sig_res efsig with Some x => x | None => Tint end) ->
      Val.has_type res typ ->
      res = val_of_eval eres ->
      ltlin_step (Blockedstate s efsig)
         (TEext (Ereturn typ eres))
         (Returnstate s res)
  | exec_return:
      forall res f sp rs b s vres,
      ltlin_step (Returnstate (Stackframe res f sp rs b :: s) vres)
        TEtau (State s f sp b (Locmap.set res vres rs))
  | exec_return_exit:
      forall vres,
      ltlin_step (Returnstate nil vres)
        TEexit (Returnstate nil vres).

Definition ltlin_init  (p : pointer) (vs : list val) : option state :=
  match Genv.find_funct_ptr ge p with
   | Some (Internal f)  => 
       if beq_nat (length vs) (length f.(fn_sig).(sig_args))
         then Some (Callstate nil (Internal f) 
           (Val.conv_list vs f.(fn_sig).(sig_args)))
         else None
   | _ => None
  end.

(* JS FIXME:
Definition ltlin_init  (p : pointer) (vs : list val) : option state :=
  match Genv.find_funct_ptr ge p with
   | Some (Internal f)  => 
       match f.(fn_sig).(sig_args) with
         | nil => Some (Callstate nil (Internal f) nil)
         | _ => None
       end
   | _ => None
  end.
*)

End RELSEM.

Tactic Notation "ltlin_step_cases" tactic(first) tactic(c) :=
    first; [
      c "exec_Lop" |
      c "exec_Lload" |
      c "exec_Lstore" |
      c "exec_Lcall" |
      c "exec_Llabel" |
      c "exec_Lgoto" |
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

Definition ltlin_ge_init (p : program) (ge : genv) (m : Mem.mem) := 
  Genv.globalenv_initmem p ge low_mem_restr m.

(** * Properties of the operational semantics *)

Lemma find_label_is_tail:
  forall lbl c c', find_label lbl c = Some c' -> is_tail c' c.
Proof.
  induction c; simpl; intros; clarify.
  destruct (is_label lbl a); clarify.
    constructor; constructor.
  constructor; auto.
Qed.

(** * TSO machine set up *)

Section LTLin_TSO.

Ltac atomic_dtac :=
  match goal with
    | H : atomic_statement_mem_event ?A ?B ?C ?D |- _ => inv H
  end.


Lemma ltlin_receptive :
  forall ge l l' s s',
    ltlin_step ge s l s' ->
    te_samekind l' l ->
    exists s'', ltlin_step ge s l' s''.
Proof.
  intros g l l' s s' Step Te_Samekind.
  inversion Step;
     subst;
     destruct l'; try destruct ev;
     try destruct sp;
     simpl in *; subst; clarify;
     try rewrite Te_Samekind; 
     try (destruct Te_Samekind; subst);
     try (decompose [and] H2; subst);
     try (eexists;
       solve [ eassumption | econstructor; try eassumption; auto; done |
               eby econstructor; try apply H1]);
     atomic_dtac; try done; destruct Te_Samekind as (-> & -> & -> & HTI);
     eexists; (eapply exec_Latomic; [| reflexivity | apply HTI, HTv]).
   (* The following are necessary to get around silly handling
      of existential variables in Coq. *)
   eby rewrite <- H1; econstructor.
   eby rewrite <- H1; econstructor.
   eby rewrite <- H1; econstructor.
   eby rewrite <- H1; econstructor.
Qed.

Ltac determinate_aux_tac :=
  repeat (clarify; match goal with
    | H' : ?a = _, H'' : ?a = _ |- _ => rewrite H' in H''
    | H : map val_of_eval ?x = map val_of_eval ?y |- _ => 
        rewrite (map_val_of_eval_eq H); done
    | H :  atomic_statement_mem_event _ _ _ _,
      H' : atomic_statement_mem_event _ _ _ _ |- _ => 
      try (eby clarify'; eapply atomic_statement_determinate);
      rewrite (atomic_statement_determinate_eq H H') in *
  end).

Lemma ltlin_determinate:
  forall ge s s' s'' l l',
    ltlin_step ge s l s' ->
    ltlin_step ge s l' s'' ->
    (te_samekind l l' /\ (l = l' -> s' = s'')).
Proof.
  intros g s s' s'' l l' ST1 ST2; split.
    by destruct ST1; inv ST2; simpl; determinate_aux_tac; destruct sp.
  by intro; subst; destruct ST1; inv ST2; determinate_aux_tac.
Qed.

Require Import Classical.

Lemma ltlin_progress_dec:
    forall ge s, (forall s' l', ~ ltlin_step ge s l' s') \/
      (exists l', exists s', ltlin_step ge s l' s').
Proof.
  intros g s.
  set (P := exists l' : thread_event, exists s' : state, ltlin_step g s l' s').
  destruct (classic P). auto.
  left. intros s' l'. revert s'. apply not_ex_all_not.
  revert l'. apply not_ex_all_not. auto.
Qed.

Definition ltlin_sem : SEM := 
  mkSEM state genv program 
  ltlin_ge_init 
  (@prog_main _ _) (@Genv.find_symbol _) 
  ltlin_step ltlin_init ltlin_progress_dec ltlin_receptive ltlin_determinate.


End LTLin_TSO.
