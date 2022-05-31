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

(** The RTL intermediate language: abstract syntax and semantics.

  RTL stands for "Register Transfer Language". This is the first
  intermediate language after Cminor and CminorSel.
*)

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
Require Import Registers.
Require Import Memcomp.
Require Import Libtactics.
Require Import CminorP. 
(*Require Import SelectionProof.*)

(** * Abstract syntax *)

(** RTL is organized as instructions, functions and programs.
  Instructions correspond roughly to elementary instructions of the
  target processor, but take their arguments and leave their results
  in pseudo-registers (also called temporaries in textbooks).
  Infinitely many pseudo-registers are available, and each function
  has its own set of pseudo-registers, unaffected by function calls.

  Instructions are organized as a control-flow graph: a function is
  a finite map from ``nodes'' (abstract program points) to instructions,
  and each instruction lists explicitly the nodes of its successors.
*)

Definition node := positive.
Inductive instruction: Type :=
  | Inop: node -> instruction
      (** No operation -- just branch to the successor. *)
  | Iop: operation -> list reg -> reg -> node -> instruction
      (** [Iop op args dest succ] performs the arithmetic operation [op]
          over the values of registers [args], stores the result in [dest],
          and branches to [succ]. *)
  | Iload: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
      (** [Iload chunk addr args dest succ] loads a [chunk] quantity from
          the address determined by the addressing mode [addr] and the
          values of the [args] registers, stores the quantity just read
          into [dest], and branches to [succ]. *)
  | Istore: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
      (** [Istore chunk addr args src succ] stores the value of register
          [src] in the [chunk] quantity at the
          the address determined by the addressing mode [addr] and the
          values of the [args] registers, then branches to [succ]. *)
  | Icall: signature -> reg + ident -> list reg -> reg -> node -> instruction
      (** [Icall sig fn args dest succ] invokes the function determined by
          [fn] (either a function pointer found in a register or a
          function name), giving it the values of registers [args] 
          as arguments.  It stores the return value in [dest] and branches
          to [succ]. *)
  | Icond: condition -> list reg -> node -> node -> instruction
      (** [Icond cond args ifso ifnot] evaluates the boolean condition
          [cond] over the values of registers [args].  If the condition
          is true, it transitions to [ifso].  If the condition is false,
          it transitions to [ifnot]. *)
  | Ireturn: option reg -> instruction
      (** [Ireturn] terminates the execution of the current function
          (it has no successor).  It returns the value of the given
          register, or [Vundef] if none is given. *)
  | Ithreadcreate: reg -> reg -> node -> instruction
      (** [Ithreadcreate fn arg] creates a thread and runs
          function [fn] with the argument [arg] in the created
          thread. *)
  | Iatomic: atomic_statement -> list reg -> reg -> node -> instruction
  | Ifence: node -> instruction.

Definition code: Type := PTree.t instruction.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: int (* was Z *);
  fn_code: code;
  fn_entrypoint: node
}.

(** A function description comprises a control-flow graph (CFG) [fn_code]
    (a partial finite mapping from nodes to instructions).  As in Cminor,
    [fn_sig] is the function signature and [fn_stacksize] the number of bytes
    for its stack-allocated activation record.  [fn_params] is the list
    of registers that are bound to the values of arguments at call time.
    [fn_entrypoint] is the node of the first instruction of the function
    in the CFG.  [fn_code_wf] asserts that all instructions of the function
    have nodes no greater than [fn_nextpc]. *)

Definition fundef := Ast.fundef function.

Definition program := Ast.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.

(** * Operational semantics *)

Definition genv := Genv.t fundef.
Definition regset := Regmap.t val.

Fixpoint init_regs (vl: list val) (rl: list reg) {struct rl} : regset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Regmap.set r1 v1 (init_regs vs rs)
  | _, _ => Regmap.init Vundef
  end.

(** The dynamic semantics of RTL is given in small-step style, as a 
  set of transitions between states.  A state captures the current
  point in the execution.  Three kinds of states appear in the transitions:

- [State cs c sp pc rs m] describes an execution point within a function.
  [c] is the code for the current function (a CFG).
  [sp] is the pointer to the stack block for its current activation
     (as in Cminor).
  [pc] is the current program point (CFG node) within the code [c].
  [rs] gives the current values for the pseudo-registers.
  [m] is the current memory state.
- [Callstate cs f args m] is an intermediate state that appears during
  function calls.
  [f] is the function definition that we are calling.
  [args] (a list of values) are the arguments for this call.
  [m] is the current memory state.
- [Returnstate cs v m] is an intermediate state that appears when a
  function terminates and returns to its caller.
  [v] is the return value and [m] the current memory state.

In all three kinds of states, the [cs] parameter represents the call stack.
It is a list of frames [Stackframe res c sp pc rs].  Each frame represents
a function call in progress.  
[res] is the pseudo-register that will receive the result of the call.
[c] is the code of the calling function.
[sp] is its stack pointer.
[pc] is the program point for the instruction that follows the call.
[rs] is the state of registers in the calling function.
*)

Inductive stackframe : Type :=
  | Stackframe:
      forall (res: reg)            (**r where to store the result *)
             (c: code)             (**r code of calling function *)
             (sp: option pointer)  (**r stack pointer in calling function *)
             (pc: node)            (**r program point in calling function *)
             (rs: regset),         (**r register state in calling function *)
      stackframe.

Inductive state : Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (c: code)                (**r current code *)
             (sp: option pointer)     (**r stack pointer **)
             (pc: node)               (**r current program point in [c] *)
             (rs: regset),            (**r register state *)
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
             (efsig: signature),      (**r pending external function *)
      state.

Section RELSEM.

Variable ge: genv.

Definition find_function
      (ros: reg + ident) (rs: regset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge rs#r
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

(** The transitions are presented as an inductive predicate
  [rtl_step ge st1 t st2], where [ge] is the global environment,
  [st1] the initial state, [st2] the final state, and [t] the trace
  of system calls performed during this transition. *)

Inductive rtl_step: state -> thread_event -> state -> Prop :=
  | exec_Inop:
      forall s c sp pc rs pc',
      c!pc = Some(Inop pc') ->
      rtl_step (State s c sp pc rs)
        TEtau (State s c sp pc' rs)
  | exec_Iop:
      forall s c sp pc rs op args res pc' v rs',
      c!pc = Some(Iop op args res pc') ->
      eval_operation ge sp op rs##args = Some v ->
      rs' = (rs#res <- v) ->
      rtl_step (State s c sp pc rs)
        TEtau (State s c sp pc' rs')
  | exec_Iload:
      forall s c sp pc rs a chunk v addr args dst pc' rs',
      c!pc = Some(Iload chunk addr args dst pc') ->
      rs' = (rs#dst <- v) ->
      eval_addressing ge sp addr rs##args = Some (Vptr a) ->
      Val.has_type v (type_of_chunk chunk) ->
      rtl_step (State s c sp pc rs)
        (TEmem (MEread a chunk v))
        (State s c sp pc' rs')
  | exec_Istore:
      forall s c sp pc rs a v chunk addr args src pc',
      c!pc = Some(Istore chunk addr args src pc') ->
      eval_addressing ge sp addr rs##args = Some (Vptr a) ->
      v = Val.conv (rs#src) (type_of_chunk chunk) ->
      rtl_step (State s c sp pc rs)
        (TEmem (MEwrite a chunk (cast_value_to_chunk chunk v)))
        (State s c sp pc' rs)
  | exec_Icall:
      forall s c sp pc rs sig ros args res pc' f,
      c!pc = Some(Icall sig ros args res pc') ->
      find_function ros rs = Some f ->
      funsig f = sig ->
      rtl_step (State s c sp pc rs)
        TEtau (Callstate (Stackframe res c sp pc' rs :: s) f (rs##args))
  | exec_Icond_true:
      forall s c sp pc rs cond args ifso ifnot,
      c!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition cond rs##args = Some true ->
      rtl_step (State s c sp pc rs)
        TEtau (State s c sp ifso rs)
  | exec_Icond_false:
      forall s c sp pc rs cond args ifso ifnot,
      c!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition cond rs##args = Some false ->
      rtl_step (State s c sp pc rs)
        TEtau (State s c sp ifnot rs)
  | exec_Ireturn:
      forall s c sp pc rs or lab,
      c!pc = Some(Ireturn or) ->
      lab = (match sp with 
               None => TEtau | 
               Some stk => TEmem (MEfree stk MObjStack) end) ->
      rtl_step (State s c sp pc rs) lab
        (Returnstate s (regmap_optget or Vundef rs))
  | exec_Ithread_create:
      forall s c sp pc rs arg pc' fn pfn,
      c!pc = Some(Ithreadcreate fn arg pc') ->
      rs#fn = Vptr pfn ->
      rtl_step (State s c sp pc rs)
        (TEstart  pfn ((rs # arg) :: nil))
        (State s c sp pc' rs)
  | exec_Iatomic:
      forall s c sp pc rs op args res pc' v rs' lab
      (H : c!pc = Some(Iatomic op args res pc'))
      (ASME : atomic_statement_mem_event op rs##args v lab)
      (Ers' : rs' = (rs#res <- v))
      (HTv : Val.has_type v Tint),
      rtl_step 
        (State s c sp pc rs)
        (TEmem lab)
        (State s c sp pc' rs')
  | exec_Ifence:
      forall s c sp pc rs pc'
      (H : c!pc = Some(Ifence pc')),
      rtl_step 
        (State s c sp pc rs)
        (TEmem MEfence)
        (State s c sp pc' rs)
  | exec_function_internal_empty:
      forall s f args,
      f.(fn_stacksize) = Int.zero ->
      rtl_step (Callstate s (Internal f) args)
        TEtau
        (State s
          f.(fn_code)
          None
          f.(fn_entrypoint)
          (init_regs args f.(fn_params)))
  | exec_function_internal_nonempty:
      forall s f args stksize code epoint regs stk,
      stksize = f.(fn_stacksize) ->
      code = f.(fn_code) ->
      epoint = f.(fn_entrypoint) ->
      regs = init_regs args f.(fn_params) ->
      stksize <> Int.zero ->
      rtl_step (Callstate s (Internal f) args)
         (TEmem (MEalloc stk f.(fn_stacksize) MObjStack))
         (State s code (Some stk) epoint regs)
  | exec_function_external_call:
      forall s ef args eargs lab,
      args = map val_of_eval eargs ->
      lab = TEext (Ecall ef.(ef_id) eargs (*(Val.conv_list args (sig_args ef.(ef_sig)))*) ) ->
      rtl_step (Callstate s (External ef) args) lab 
         (Blockedstate s ef.(ef_sig))
  | exec_function_external_return:
      forall s efsig typ eres res,
      typ = (match sig_res efsig with Some x => x | None => Tint end) ->
      res = val_of_eval eres ->
      Val.has_type res typ ->
      rtl_step (Blockedstate s efsig)
         (TEext (Ereturn typ eres))
         (Returnstate s res)
  | exec_return:
      forall res c sp pc rs s vres,
      rtl_step (Returnstate (Stackframe res c sp pc rs :: s) vres)
        TEtau (State s c sp pc (rs#res <- vres))
  | exec_return_exit:
      forall vres,
      rtl_step (Returnstate nil vres)
        TEexit (Returnstate nil vres).

Inductive rtl_trace : state -> list thread_event -> state -> Prop :=
  | rtl_trace_refl: forall s, rtl_trace s nil s
  | rtl_trace_step : forall st1 lab st2 t st3
    (ST:  rtl_step st1 lab st2)
    (TR: rtl_trace st2 t st3),
    rtl_trace st1 (weakcons lab t) st3.

Lemma weakcons_app:
  forall l t1 t2,
    weakcons l t1 ++ t2 = weakcons l (t1 ++ t2).
Proof.
  by intros; destruct l.
Qed.

Lemma rtl_trace_step_one:
  forall st1 lab st2
    (ST: rtl_step st1 lab st2),
      rtl_trace st1 (weakcons lab nil) st2.
Proof.
  intros.
  by eapply rtl_trace_step, rtl_trace_refl.
Qed.

Lemma rtl_trace_trans: 
  forall st1 st2 st3 t1 t2 t
    (TR1: rtl_trace st1 t1 st2)
    (TR2: rtl_trace st2 t2 st3)
    (L: t = (t1 ++ t2)),
    rtl_trace st1 t st3.
Proof.
  intros. subst.
  induction TR1; [done|].
  rewrite weakcons_app; eapply rtl_trace_step; eauto.
Qed.

Lemma trace_step_right:
  forall s1 s2 s3 t1 e2 t,
  rtl_trace s1 t1 s2 ->
  rtl_step s2 e2 s3 ->
  t = t1 ++ (weakcons e2 nil) ->
  rtl_trace s1 t s3.
Proof.
  intros. subst. 
  eapply rtl_trace_trans. eassumption.
  eby eapply rtl_trace_step_one.  done.
Qed.

Inductive rtl_trace_plus: state -> list thread_event  -> state -> Prop :=
 | plus_left: forall s1 t1 s2 t2 s3 t
     (ST: rtl_step s1 t1 s2)
     (TR: rtl_trace s2 t2 s3)
     (E : t = (weakcons t1 nil) ++ t2),
       rtl_trace_plus s1 t s3.

Lemma plus_right: 
  forall s1 t s2 l s3 t'
    (TR: rtl_trace s1 t s2)
    (ST: rtl_step  s2 l s3)
    (E : t' = t ++ (weakcons l nil)),
    rtl_trace_plus s1 t' s3.
Proof.
  intros; subst.
  inv TR. econstructor. edone. vauto. by destruct l.
  econstructor. edone. eby eapply trace_step_right. 
  by rewrite !weakcons_app.
Qed.

Lemma step_one: 
  forall s1 t s2
    (ST: rtl_step s1 t s2),
      rtl_trace s1 (weakcons t nil) s2.
Proof.
  intros. eapply rtl_trace_step_one; eauto. 
Qed.

Lemma plus_one:
  forall s1 t s2
    (ST: rtl_step s1 t s2), 
      rtl_trace_plus s1 (weakcons t nil) s2.
Proof.
  intros. eapply plus_left. eauto. eapply rtl_trace_refl. 
  unfold weakcons; destruct t; by simpl.
Qed.

Lemma step_nonempty_weak:
 forall lab t,
  lab <> TEtau -> lab :: t = (weakcons lab t).
Proof.
  intros. unfold weakcons; destruct lab; try done. 
Qed.

Definition rtl_init  (p : pointer) (vs : list val) : option state :=
  match Genv.find_funct_ptr ge p with
   | Some (Internal f)  => 
       if beq_nat (length vs) (length f.(fn_sig).(sig_args))
         then Some (Callstate nil (Internal f) (Val.conv_list vs f.(fn_sig).(sig_args)))
         else None
       (* JS PARAM: match f.(fn_sig).(sig_args) with
         | nil => Some (Callstate nil (Internal f) nil)
         | _ => None
       end *)
   | _ => None
  end.

End RELSEM.

Tactic Notation "rtl_step_cases" tactic(first) tactic(c) :=
    first; [
      c "exec_Inop" |
      c "exec_Iop" |
      c "exec_Iload" |
      c "exec_Istore" |
      c "exec_Icall" |
      c "exec_Icond_true" |
      c "exec_Icond_false" |
      c "exec_Ireturn" |
      c "exec_Ithread_create" |
      c "exec_Iatomic" |
      c "exec_Ifence" |
      c "exec_function_internal_empty" |
      c "exec_function_internal_nonempty" |
      c "exec_function_external_call" |
      c "exec_function_external_return" |
      c "exec_return" |
      c "exec_return_exit"].

(** * Operations on RTL abstract syntax *)

(** Computation of the possible successors of an instruction.
  This is used in particular for dataflow analyses. *)

Definition successors_instr (i: instruction) : list node :=
  match i with
  | Inop s => s :: nil
  | Iop op args res s => s :: nil
  | Iload chunk addr args dst s => s :: nil
  | Istore chunk addr args src s => s :: nil
  | Icall sig ros args res s => s :: nil
  | Icond cond args ifso ifnot => ifso :: ifnot :: nil
  | Ireturn optarg => nil
  | Ithreadcreate _ _ s => s :: nil
  | Iatomic aop args res s => s :: nil
  | Ifence s => s :: nil
  end.

Definition successors (f: function) : PTree.t (list node) :=
  PTree.map (fun pc i => successors_instr i) f.(fn_code).

(** Transformation of a RTL function instruction by instruction.
  This applies a given transformation function to all instructions
  of a function and constructs a transformed function from that. *)

Section TRANSF.

Variable transf: node -> instruction -> instruction.

Definition transf_function (f: function) : function :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (PTree.map transf f.(fn_code))
    f.(fn_entrypoint).

End TRANSF.

Definition rtl_ge_init (p: program) (ge: genv) (m : Mem.mem) :=
  Genv.globalenv_initmem p ge low_mem_restr m.


(** * TSO machine set up *)

Section RTL_TSO.

Ltac atomic_dtac :=
  match goal with
    | H : atomic_statement_mem_event ?A ?B ?C ?D |- _ => inv H
  end.

Lemma rtl_receptive :
  forall ge l l' s s',
    rtl_step ge s l s' ->
    te_samekind l' l ->
    exists s'', rtl_step ge s l' s''.
Proof.
  intros g l l' s s' Step Te_Samekind.
  inversion Step; subst;
     destruct l'; try destruct ev;
     try destruct sp;
     simpl in *; clarify;
     try rewrite Te_Samekind; 
     try (decompose [and] Te_Samekind; subst);
     try (match goal with [H: _ = _ /\ _ |- _] => destruct H end; subst);
     try (by eexists; solve [ eassumption | econstructor; try edone; auto ]);
     atomic_dtac; try done; destruct Te_Samekind as (-> & -> & -> & HTI);
     eexists; (eapply exec_Iatomic; [edone | | reflexivity | apply HTI, HTv]).
   (* The following are necessary to get around silly handling
      of existential variables in Coq. *)
   eby rewrite <- H2; econstructor.
   eby rewrite <- H2; econstructor.
   eby rewrite <- H2; econstructor.
   eby rewrite <- H2; econstructor.
Qed.



Ltac determinate_aux_tac :=
  repeat match goal with
    | H' : ?a = _, H'' : ?a = _ |- _ => rewrite H' in H''; clarify; determinate_aux_tac
    | H : map val_of_eval ?x = map val_of_eval ?y |- _ => rewrite (map_val_of_eval_eq H); done
    | H :  atomic_statement_mem_event _ _ _ _,
      H' : atomic_statement_mem_event _ _ _ _ |- _ => 
      try (eby clarify'; eapply atomic_statement_determinate);
      rewrite (atomic_statement_determinate_eq H H') in *
  end.

Lemma rtl_determinate:
  forall ge s s' s'' l l',
    rtl_step ge s l s' ->
    rtl_step ge s l' s'' ->
    (te_samekind l l' /\ (l = l' -> s' = s'')).
Proof.
  intros g s s' s'' l l' ST1 ST2.
  split.

  by destruct ST1; inv ST2; simpl; clarify; determinate_aux_tac; 
     try destruct sp.

  intro; subst.
  by destruct ST1; inv ST2; clarify; determinate_aux_tac.
Qed.

Require Import Classical.

Lemma rtl_progress_dec:
  forall ge s, (forall s' l', ~ rtl_step ge s l' s') \/
    (exists l', exists s', rtl_step ge s l' s').
Proof.
  intros g s.
  set (P := exists l' : thread_event, exists s' : state, rtl_step g s l' s').
  by destruct (classic P) as [|N]; [|left; red; intros; case N]; vauto. 
Qed.

Definition rtl_sem : SEM := 
  mkSEM state genv program 
  rtl_ge_init 
  (@prog_main _ _) (@Genv.find_symbol _) 
  rtl_step rtl_init rtl_progress_dec rtl_receptive rtl_determinate.

End RTL_TSO.
