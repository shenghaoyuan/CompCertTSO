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

(** CminorPrime: for the correctness proof of the instruction
selection phase (in [Selection.v] and [SelectOp.v]), we introduce a
new semantics for Cminor.  This [CminorP.cmp_step] semantics is
inductive on expressions; it is a predicate over pairs of states and
"trace steps", the lists of events that can be followed from one to
the other.  The fact that it is inductive on expression structure (in
contrast to the small-step semantics for expressions we use in earlier
phases) makes it straightforward to adapt the CompCert
[SelectOpproof.v]. 
However, this does necessitate some plumbing, as outlined below, to
relate the trace-step result to the earlier small-step semantics.  We
do this by identifying the "clean" Cminor states, those without
expression or value continuations; CminorP trace-step transitions
correspond essentially to sequences of Cminor transitions between
clean states.  *)



Require Import Coqlib.
Require Import Libtactics.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Floats.
Require Import Pointers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Cminor.
Require Import Op.
Require Import SelectOp.
Require Import Cminorops.
Require Import Switch.

Section RELSEM.

Variable ge: Cminor.genv.

(** Proof structure from Cminor to CminorSel, and from CminorSel to RTL

The vertical arrows indicate forwards per-thread simulations of some kind.

<<

From Cminor to CminorSel...

Cminor.cm_step                                      .    .
  (small-step with expression                       |(5) |(6)
  continuations)                                    |    |
                                                    v    |
CminorP.small_step_cm                          .    .    |
  (constructed small-step built                |(4)      |
  from CminorP.cm_via_unclean)                 |         |
                                               |         |
CminorP.cm_via_unclean              .     .    |         |
  (sequences of Cminor.cm_step's    |(2)  |(3) |         |
  to clean states, with weakcons)   |     |    |         |
                                    v     |    |         |
CminorP.cmp_step                    .     |    |         |
  (trace steps, inductive           |(1)  |    |         |
  on expressions)                   |     |    |         |
                                    v     v    |         |
CminorSel.step                      .     .    |         |   .
  (trace steps, inductive                      |         |   |(7)
  on expressions)                              |         |   |
                                               v         v   |
Selectionproof.small_step_cs                   .         .   |   .
  (constructed receptive small-step built                    |   |(8)
  from CminorSel.step)                                       |   |
  (same as RTLgenproof.small_step_cs)                        |   |
                                                             |   |
...and from CminorSel to RTL                                 |   |
                                                             |   |
                                                             v   |
RTL.rtl_trace / rtl_trace_plus                               .   |
  (sequences of RTL.rtl_step's)                                  |
  (built with weakcons)                                          |
                                                                 v
RTL.rtl_step                                                     .
  (small-step)

>>

Cminor to CminorSel  
-------------------

(1) Selectionproof.sel_step_correct (this is the real work of the
selection proof, using many lemmas in SelectOpproof about the
CminorSel [eval_expr], making heavy use of its inductive-on-expressions nature)

(2) [CminorP.cmp_step_correct]

(3) [Selectionproof.cmp_step_correct_foo]  (just gluing (1) and (2))

(4) [Selectionproof.cmp_small_step_correct] (just lifting (3) to the 
constructed small-step relations)

(5) [CminorP.cm_small_step_correct] below, using added
[cm_ev_stuck] disjunct on the rhs of the simulation.

(6) [Selectionproof.small_step_correct_all], gluing together (5) and (4).


Some measuring is also needed here, as this step erases some
taus.  (3) is on-the-nose for trace steps, and the trace-step
semantics have no taus:

  CminorP.cm_via_unclean   
  CminorP.cmp_step         
  CminorSel.step           

The two constructions of a small-step (small_step and
small_step_Recep, below) introduce taus only for nil trace steps.
Moreover, (4) is on the nose (a strong simulation), so the only
measuring required is that for (5), and it should be routine to lift
that to the composition (6) of (4) and (5). 


CminorSel to RTL   
----------------

(7) [RTLgenproof.transl_step_correct], from [CminorSel.step] to
[RTL.rtl_trace]/[RTL.rtl_trace_plus].

(8) [RTLgenproof.fwsim], lifting (7) to the constructed small-step
relation for CminorSel and the original [rtl_step].


*)


(**

The Cminor.v semantics is, abstractly, something like this:
<<
                               .
                               .            
            Clean              .     Unclean
                               .    
                               .                  
    -----------SKexternal      .                                
   /              ^            .           _____________________
   |              |            .          /                     \
   |      external|            .         /                      |
   |              |      tau   .        /                       |
   |           SKcall <--------.-------/                        |
   |                |          .      /                         |
   |            tau |    tau   .     /                   tau    |
   |          alloc |    write .    /    _             _ read   |
   |                |    start .   /    / \           / \       |
   |                v <--------.--/     \ v    ---->  \ v       | 
   |       +-> SKstmt ---------.------> SKexpr       SKval -----/
   |   tau \___/  ^ |          .               <----   |         
   |   exit       | | tau      .                       |         
   |              | | free     .                       |         
   |              | v          .                       |         
   \---------> SKreturn  <-----.-----------------------/
                          tau  .                        
                          free .       
                               .
                               .
>>                              
(arrows are tau unless otherwise labelled)


The CminorPrime semantics defined here (CminorP.v) comprises:

  [cmp_eval_expr: list thread_event -> Cminor.expr -> val -> Prop] 

    (inductive on expressions, in contrast to the CompCertTSO Cminor semantics)

  [cmp_step : state -> list thread_event -> state -> Prop] 

    (for transitions between clean states only, and without any taus)


To express and prove the correspondence with the Cminor semantics, we also define:

  [cmp_istep_expr_cont  (v:val) : expr_cont -> list thread_event -> state -> Prop]

    (inductive on expr_cont, from the expr_cont of an unclean state
    (SKexpr or SKval) to the next clean state)

  [cmp_istep : state -> list thread_event -> state -> Prop]

    (wrapping cmp_istep_expr_cont, from an unclean state (SKexpr or
    SKval) to the next clean state)

  [cm_via_unclean : state -> list thread_event -> state -> Prop]

    (sequences of Cminor steps via unclean intermediate states to a
    clean state, erasing taus)


That correspondence result (Lemma cmp_step_correct below) says that any 
cm_via_unclean step from a clean state can be matched by a cmp_step.

*)

Definition clean (st : state) : bool := 
  match st with
    | SKexpr _ _ _ _ => false
    | SKval _ _ _ _ => false
    | SKstmt _ _ _ _ => true
    | SKcall _ _ => true
    | SKexternal _ _ => true
    | SKreturn _ _ => true 
  end.

(** ** Measure for [Cminor.cm_step] *)

(** We want measures for two purposes: to prove [stuck_or_via] below, and to
    build a measured forwards simulation from [Cminor.cm_step] to
    [Selectionproof.small_step_cs]. *)

(** Upper bound on the number of transitions to completely reduce
    [SKexpr e ...] to its ultimate [SKval ...] *)
Fixpoint measure_expr (e0 : expr) { struct e0 } : nat := 
  match e0 with
    | Evar _              => 1%nat
    | Econst _            => 1%nat
    | Eunop _ e           => (2+measure_expr e)%nat
    | Ebinop _ e1 e2      => (3+measure_expr e1+measure_expr e2)%nat
    | Eload _ e           => (2+measure_expr e)%nat
    | Econdition e1 e2 e3 => (2+measure_expr e1 + measure_expr e2 + measure_expr e3)%nat
  end.

(* Upper bound on the number of transitions to completely reduce
   the arguments of a function. *)
Fixpoint measure_list_expr (es0 : list expr) { struct es0 } : nat := 
  match es0 with
    | nil  => (0)%nat
    | e :: es => (2 + measure_expr e + measure_list_expr es )%nat
  end.

Fixpoint measure_stmt (s0 : stmt) : nat := 
  (match s0 with
     | Sskip                => 0
     | Sassign id e         => 2 + measure_expr e
     | Sstore _ e1 e2       => 3 + measure_expr e1 + measure_expr e2
     | Scall _ _ e es       => 2 + measure_expr e + measure_list_expr es
     | Sseq s1 s2           => 0
     | Sifthenelse e s1 s2  => 2 + measure_expr e + measure_stmt s1 + measure_stmt s2
     | Sloop s              => 0
     | Sblock s             => 0 
     | Sexit _              => 0
     | Sswitch e _ _        => 2 + measure_expr e
     | Sreturn (Some e)     => 2 + measure_expr e
     | Sreturn None         => 0
     | Slabel _ s           => 0
     | Sgoto _              => 0
     | Sthread_create e1 e2 => 3 + measure_expr e1 + measure_expr e2
     | Satomic _ _ es       => 1 + measure_list_expr es
     | Smfence              => 0
  end)%nat.

Fixpoint  measure_expr_cont (ek0 : expr_cont) { struct ek0 } : nat := 
  (match ek0 with
    | EKunop _ ek              => 1 + measure_expr_cont ek
    | EKbinop1 _ e2 ek         => 2 + measure_expr e2 + measure_expr_cont ek
    | EKbinop2 _ v ek          => 1 + measure_expr_cont ek
    | EKload _ ek              => 1 + measure_expr_cont ek
    | EKcall _ _ es k          => 1 + measure_list_expr es
    | EKargs _ v _ es vs k     => 1 + measure_list_expr es
    | EKatargs _ _ es _ _      => 2 + measure_list_expr es
    | EKcond e1 e2 ek          => 1 + measure_expr e1+measure_expr e2+measure_expr_cont ek
    | EKassign _ k             => 1
    | EKthread1 e k            => 2 + measure_expr e
    | EKthread2 _ k            => 1
    | EKcondstmt s1 s2 k       => 1 + measure_stmt s1 + measure_stmt s2
    | EKswitch cases default k => 1
    | EKreturn k               => 1
    | EKstoreaddr _ e k        => 2 + measure_expr e
    | EKstoreval _ v k         => 1
  end)%nat.

Definition  measure (st0: Cminor.state) : nat := 
  (match st0 with
    | SKexpr e _ _ ek          => measure_expr e + measure_expr_cont ek
    | SKval v _ _ ek           => measure_expr_cont ek
    | SKstmt s _ _ k           => measure_stmt s
    | SKcall args k            => 0
    | SKexternal efsig k       => 0
    | SKreturn v k             => 0
  end)%nat.

(** The two important properties that measures satisfy: *)

Lemma decreasing_measure_from_unclean: 
  forall st te st' (UC: clean st = false) (TRAN:cm_step ge st te st'),
    (measure st' < measure st)%nat.
Proof.
intros; (cm_step_cases (destruct TRAN) Case);
  try (by simpl; omega);
  try (by (simpl; unfold clean in  UC; done)).
Qed.

Lemma decreasing_measure_to_unclean: 
  forall st te st' (UC: clean st' = false) (TRAN:cm_step ge st te st'),
    (measure st' < measure st)%nat.
Proof.
intros; (cm_step_cases (destruct TRAN) Case);
  try (by simpl; omega);
  try (by (simpl; unfold clean in  UC; done)).
Qed.


(** ** CminorP semantics *)

Section CMINOR_EVAL_EXPR.


Variable sp: option Pointers.pointer.
Variable e: env.

(** Evaluation of an expression: [cmp_eval_expr ge sp env t e v]
  states that expression [e] evaluates to value [v].
  [ge] is the global environment, [env] the local environment,
  and [t] the list of memory reads (replacing the CompCert-1.5 m, the current memory state).  All except [t] are unchanged during expression evaluation.
  [sp] is the pointer to the memory block allocated for this function
  (stack frame).
*)


Inductive cmp_eval_expr: list thread_event -> Cminor.expr -> val -> Prop :=
  | eval_Evar: forall id v
      (EVAL : PTree.get id e = Some v),
      cmp_eval_expr nil (Cminor.Evar id) v
  | eval_Econst: forall cst v
      (EC : eval_constant ge sp cst = Some v),
      cmp_eval_expr nil (Cminor.Econst cst) v
  | eval_Eunop: forall op t1 a1 v1 v
      (EE : cmp_eval_expr t1 a1 v1)
      (EU : eval_unop op v1 = Some v),
      cmp_eval_expr t1 (Cminor.Eunop op a1) v
  | eval_Ebinop: forall op t1 t2 t a1 a2 v1 v2 v
      (EE1 : cmp_eval_expr t1 a1 v1)
      (EE2 : cmp_eval_expr t2 a2 v2)
      (EB : eval_binop op v1 v2 = Some v)
      (TT : t = t1++t2),
      cmp_eval_expr t (Cminor.Ebinop op a1 a2) v
  | eval_Eload: forall c taddr addr p v t
      (EE : cmp_eval_expr taddr addr (Vptr p))
      (HT : Val.has_type v (type_of_chunk c))
      (TT : t = taddr++((TEmem(MEread p c v)) :: nil)),
      cmp_eval_expr t (Cminor.Eload c addr) v
  | eval_Econdition: forall t1 t a1 a2 a3 v1 b1 v t'
      (EE1 : cmp_eval_expr t1 a1 v1)
      (EB : Val.bool_of_val v1 b1)
      (EE : cmp_eval_expr t (if b1 then a2 else a3) v)
      (TT : t' = t1++t),
      cmp_eval_expr t' (Cminor.Econdition a1 a2 a3) v.

Inductive cmp_eval_exprlist: list thread_event -> list Cminor.expr -> list val -> Prop :=
  | eval_Enil:
      cmp_eval_exprlist nil nil nil
  | eval_Econs: forall t1 tl a1 al v1 vl t
      (EE : cmp_eval_expr t1 a1 v1)
      (ES : cmp_eval_exprlist tl al vl)
      (TT : t = t1++tl),
      cmp_eval_exprlist t (a1 :: al) (v1 :: vl).

(* the above does not include taus (eg to match the Cminor taus on the
nose) as they will not be preserved by selection *)

End CMINOR_EVAL_EXPR.

(* adaption of CompCertTSO Cminor small-step semantics to
expression-trace-step, between clean states as defined above *)

Definition weakcons (lab:thread_event) (t: list thread_event) : list thread_event := 
  match lab with
    | TEtau => t
    | _     => lab::t
  end.


Inductive cmp_step : state -> list thread_event -> state -> Prop :=

(* Skip *)
| PStepSkipBlock:
  forall sp k env,
  cmp_step (SKstmt Sskip sp env (Kblock k))
          nil
          (SKstmt Sskip sp env k)
(* Assign *)
| PStepAssign:
  forall sp v id e env env' k t
  (E:cmp_eval_expr sp env t e v)
  (VLS : PTree.set id v env = env'),
  cmp_step (SKstmt (Sassign id e) sp env k)
           t
           (SKstmt Sskip sp env' k)
(* Store *)
| PStepStore:
  forall sp chunk e1 e2 env k t1 t2 lab ptr v
  (E1:cmp_eval_expr sp env t1 e1 (Vptr ptr))
  (E2:cmp_eval_expr sp env t2 e2 v)
  (LAB: lab = TEmem (MEwrite ptr chunk (cast_value_to_chunk chunk v))),
  cmp_step (SKstmt (Sstore chunk e1 e2) sp env k) 
           (t1 ++ t2 ++ (lab::nil))
           (SKstmt Sskip sp env k)
(* Call *)
| PStepCall:
  forall optid sig ef  args sp env k fd tf vf targs vargs t
  (EF: cmp_eval_expr sp env tf ef vf)
  (ES : cmp_eval_exprlist sp env targs args vargs)
  (TEQ : t = tf ++ targs)
  (GFF : Genv.find_funct ge vf = Some fd)
  (FSIG : funsig fd = sig),
  cmp_step (SKstmt (Scall optid sig ef args) sp env k)
          t
          (SKcall vargs (Kcall optid fd sp env k))
(* Atomic *)
| PStepAtomicNone: forall sp env k targs args vargs p rmwi v' t astmt 
  (ES : cmp_eval_exprlist sp env targs args vargs)
  (AS : Cminorops.sem_atomic_statement astmt vargs = Some (p, rmwi))
  (TY : Val.has_type v' (type_of_chunk Mint32))
  (Et : t = targs ++ (TEmem  (MErmw p Mint32 v' rmwi)) :: nil),
  cmp_step (SKstmt (Satomic None astmt  args) sp env k)
           t
           (SKstmt Sskip sp env k)
| PStepAtomicSome: forall sp env k targs args vargs p rmwi v' t astmt id env'
  (ES : cmp_eval_exprlist sp env targs args vargs)
  (AS : Cminorops.sem_atomic_statement astmt vargs = Some (p, rmwi))
  (TY : Val.has_type v' (type_of_chunk Mint32))
  (Ee : PTree.set id v' env = env')
  (Et : t= targs ++ (TEmem  (MErmw p Mint32 v' rmwi)) :: nil),
  cmp_step (SKstmt (Satomic (Some id) astmt  args) sp env k)
           t
           (SKstmt Sskip sp env' k)
(* Fence *)
| PStepFence:
  forall sp k env,
  cmp_step (SKstmt Smfence sp env k)
          (TEmem MEfence :: nil)
          (SKstmt Sskip sp env k)
(* Seq *)
| PStepSeq:
  forall sp s1 s2 env k,
  cmp_step (SKstmt (Sseq s1 s2) sp env k)
          nil
          (SKstmt s1 sp env (Kseq s2 k))
(* Conditional Statement *)
| PStepCond:
  forall sp e s1 s2 env k t v b
  (E:cmp_eval_expr sp env t e v)
  (BOV : Val.bool_of_val v b),
  cmp_step (SKstmt (Sifthenelse e s1 s2) sp env k)
           t
           (SKstmt  (if b then s1 else s2) sp env k) 
(* Loop *)
| PStepLoop:
  forall sp s env k,
  cmp_step (SKstmt (Sloop s) sp env k)
           nil
           (SKstmt s sp env (Kseq (Sloop s) k)) 
(* Block *)
| PStepBlock:
  forall sp s env k,
  cmp_step (SKstmt (Sblock s) sp env k)
           nil
           (SKstmt s sp env (Kblock k))
(* Exit *)
| PStepExitSeq:
  forall sp n s k env,
  cmp_step (SKstmt (Sexit n) sp env (Kseq s k))
           nil
           (SKstmt (Sexit n) sp env k)
| PStepExitBlock:
  forall sp env k,
  cmp_step (SKstmt (Sexit 0) sp env (Kblock k))
           nil
           (SKstmt Sskip sp env k)
| PStepExitBlock1:
  forall sp n env k,
  cmp_step (SKstmt (Sexit (S n)) sp env (Kblock k))
           nil
           (SKstmt (Sexit n) sp env k)
(* Switch *)
| PStepSwitch:
  forall sp e cases default env k t n
  (E:cmp_eval_expr sp env t e (Vint n)),
  cmp_step (SKstmt (Sswitch e cases default) sp env k)
           t
           (SKstmt (Sexit (switch_target n default cases)) sp env k)
(* Label *)
| PStepLabel:
  forall sp lbl s env k,
  cmp_step (SKstmt (Slabel lbl s) sp env k)
           nil
           (SKstmt s sp env k)
(* Goto *)
| PStepGoto:
  forall sp f lbl k s' k' k'' env
  (CC : call_cont k = k')
  (GFD : get_fundef k' = (Some (Internal f)))
  (FL : find_label lbl f.(fn_body) k' = Some (s', k'')),
  cmp_step (SKstmt (Sgoto lbl) sp env k)
           nil
           (SKstmt s' sp env k'')
(* Return *)
| PStepReturnNone:
  forall sp sp' f k k' env env' lab t
  (CC : call_cont k = (Kcall None (Internal f) sp' env' k'))
  (FSIG : f.(fn_sig).(sig_res) = None)
  (LAB: lab = (match sp with 
           None => TEtau | 
           Some stk => TEmem (MEfree stk MObjStack) end))
  (TEQ: t = weakcons lab nil),
  cmp_step (SKstmt (Sreturn None) sp env k)
           t
           (SKreturn Vundef k)

| PStepReturnSome:
  forall sp e f k env v t t' lab
  (CC : get_fundef (call_cont k) = Some (Internal f))
  (FSIG : f.(fn_sig).(sig_res) <> None)
  (EE : cmp_eval_expr sp env t e v)
  (LAB: lab = (match sp with 
           None => TEtau | 
           Some stk => TEmem (MEfree stk MObjStack) end))
  (TEQ: t' = (t++(weakcons lab nil))),
  cmp_step (SKstmt (Sreturn (Some e)) sp env k)
          t'
          (SKreturn v k)

| PStepReturnFinish:
  forall sp v fd optid k k' env' env''
  (CC : call_cont k = (Kcall optid fd sp env' k'))
  (VLS : set_optvar optid v env' = env''),
  cmp_step (SKreturn v k)
          nil
          (SKstmt Sskip sp env'' k')
(* Internal Call *)
| PStepFunctionInternalNoStack:
  forall sp optid f vs k env env' ck
  (CC : ck  = (Kcall optid (Internal f) sp env' k))
  (FZ : f.(fn_stackspace) = 0)
  (INIT : set_locals f.(fn_vars) (set_params vs f.(fn_params)) = env),
  cmp_step (SKcall vs ck)
          nil
          (SKstmt f.(fn_body) None env ck)
| PStepFunctionInternalWithStack:
  forall sp optid p f vs k env env' ck fsize
  (CC : ck  = (Kcall optid (Internal f) sp env' k))
  (EQfsize : fsize = f.(fn_stackspace))
  (FNZ : fsize <> 0)
  (INIT : set_locals f.(fn_vars) (set_params vs f.(fn_params)) = env),
  cmp_step (SKcall vs ck)
          ((TEmem (MEalloc p (Int.repr fsize) MObjStack))::nil)
          (SKstmt f.(fn_body) (Some p) env ck)
(* External Call *)
| PStepExternalCall:
  forall sp k ef vargs evargs tgt env id efsig ck
  (EARGS : vargs = map val_of_eval evargs),
  id = ef.(ef_id) ->
  efsig = ef.(ef_sig) ->
  ck = (Kcall tgt (External ef) sp env k) ->
  cmp_step (SKcall vargs ck)
          ((TEext (Ecall id evargs))::nil)
          (SKexternal efsig ck)
| PStepExternalReturn:
  forall efsig vres evres k typ
  (TYP : typ = (match sig_res efsig with Some x => x | None => Tint end))
  (HT : Val.has_type vres typ)
  (ERES : vres = val_of_eval evres),
  cmp_step (SKexternal efsig k)
          ((TEext (Ereturn typ evres))::nil)
          (SKreturn vres k)
(* Continuation Management *)
| PStepNext:
  forall sp s k env,
  cmp_step (SKstmt Sskip sp env (Kseq s k))
           nil
           (SKstmt s sp env k)
| PStepStop:
  forall sp env,
  cmp_step (SKstmt Sskip sp env Kstop)
           (TEexit::nil)
           (SKstmt Sskip sp env Kstop)
(* Thread *)
| PStepThread : 
  forall sp efn earg k env v p tfn targ t
  (EFN:cmp_eval_expr sp env tfn efn (Vptr p))
  (EARG:cmp_eval_expr sp env targ earg v)
  (TEQ: t = tfn ++ targ ++ ((TEstart p (v::nil)):: nil)),
  cmp_step (SKstmt (Sthread_create efn earg) sp env k)
           t
           (SKstmt Sskip sp env k).


Section CMP_ISTEP_EXPR_CONT.

Variable sp : option pointer.
Variable env:env.


(* cmp_istep_expr_cont gives the list of thread events from the
expr_cont of an unclean state (SKexpr or SKval) to the next clean
state, inductive on expression continuation structure *)

(* This is an auxilary definition to use in the proof that the CminorP
semantics simulates the Cminor semantics, not part of the CminorP
semantics itself. *)


Inductive cmp_istep_expr_cont  (v:val) : expr_cont -> list thread_event -> state -> Prop :=
  | IStep_EKunop : forall op v' k tr sr
      (EU : eval_unop op v = Some v')
      (REST : cmp_istep_expr_cont v' k tr sr),
      cmp_istep_expr_cont v (EKunop op k) tr sr

  | IStep_EKbinop1 : forall op e2 k t2 v2 v' tr sr
      (EE2 : cmp_eval_expr sp env t2 e2 v2)
      (EB : eval_binop op v v2 = Some v')
      (REST : cmp_istep_expr_cont v' k tr sr),
      cmp_istep_expr_cont v (EKbinop1 op e2 k) (t2++tr) sr

  | IStep_EKbinop2 : forall op v1 k v' tr sr              
      (EB : eval_binop op v1 v = Some v')
      (REST : cmp_istep_expr_cont v' k tr sr),
      cmp_istep_expr_cont v (EKbinop2 op v1 k) tr sr

  | IStep_EKload : forall c k p v' tr sr
      (VEQP: v = Vptr p)
      (HT : Val.has_type v' (type_of_chunk c))
      (REST : cmp_istep_expr_cont v' k tr sr),
      cmp_istep_expr_cont v (EKload c k) ((TEmem(MEread p c v')) :: tr) sr

  (* in Cminor, EKcall goes via StepEmptyCall to clean iff args=nil, otherwise via StepCallArgs1 to unclean *)
  | IStep_EKcall : forall fd sig optid k args vs t
      (GFF : Genv.find_funct ge v = Some fd)
      (ES : cmp_eval_exprlist sp env t args vs)
      (FSIG : funsig fd = sig),
      cmp_istep_expr_cont v (EKcall optid sig args k) t (SKcall vs (Kcall optid fd sp env k))

  (* in Cminor, EKargs goes via StepCallArgs to clean iff args=nil, otherwise via StepCallArgs2 to unclean *)
  | IStep_EKargs : forall vs vf fd optid k args vs' t vs'' sig
      (GFF: Genv.find_funct ge vf = Some fd)
      (ES : cmp_eval_exprlist sp env t args vs')
      (VSEQ : vs'' = vs ++ (v :: vs'))
      (FSIG : funsig fd = sig),
      cmp_istep_expr_cont v (EKargs optid vf sig args vs k) t (SKcall vs'' (Kcall optid fd sp env k))

  | IStep_EKatargsNone : forall vs k vs' t vs'' rmwi v' p astmt args t'
      (ES : cmp_eval_exprlist sp env t args vs')
      (VSEQ : vs'' = vs ++ (v :: vs'))
      (TY : Val.has_type v' (type_of_chunk Mint32))
      (ASTMT : Cminorops.sem_atomic_statement astmt vs'' = Some (p, rmwi))
      (Et' : t' = t ++ (TEmem (MErmw p Mint32 v' rmwi)) :: nil),
      cmp_istep_expr_cont v (EKatargs None astmt args vs k) t' (SKstmt Sskip sp env k)

  | IStep_EKatargsSome : forall vs k vs' t vs'' rmwi v' p astmt args env' id t'
      (ES : cmp_eval_exprlist sp env t args vs')
      (VSEQ : vs'' = vs ++ (v :: vs'))
      (TY : Val.has_type v' (type_of_chunk Mint32))
      (ASTMT : Cminorops.sem_atomic_statement astmt vs'' = Some (p, rmwi))
      (NE : env' = env ! id <- v')
      (Et' : t' = t ++ (TEmem (MErmw p Mint32 v' rmwi)) :: nil),
      cmp_istep_expr_cont v (EKatargs (Some id) astmt args vs k) t' (SKstmt Sskip sp env' k)

  | IStep_EKcond : forall e2 e3 k t tr sr b1 v'              
      (EB : Val.bool_of_val v b1)
      (EE : cmp_eval_expr sp env t (if b1 then e2 else e3) v')
      (REST : cmp_istep_expr_cont v' k tr sr),
      cmp_istep_expr_cont v (EKcond e2 e3 k) (t++tr) sr

  | IStep_EKassign : forall id env' k 
      (VLS : PTree.set id v env = env'),
      cmp_istep_expr_cont v (EKassign id k) nil (SKstmt Sskip sp env' k)

  | IStep_EKthread1 : forall earg k targ v' p
      (VEQP: v = Vptr p)               
      (EARG:cmp_eval_expr sp env targ earg v'),
      cmp_istep_expr_cont v (EKthread1 earg k) 
           (targ ++ ((TEstart p (v'::nil)):: nil))
           (SKstmt Sskip sp env k)

  | IStep_EKthread2 : forall p k,
      cmp_istep_expr_cont v (EKthread2 p k)
           (((TEstart p (v::nil)):: nil))
           (SKstmt Sskip sp env k)

  | IStep_EKcondstmt : forall s1 s2 k b s    
      (BOV : Val.bool_of_val v b)
      (SEQ : s = (if b then s1 else s2)),
      cmp_istep_expr_cont v (EKcondstmt s1 s2 k) nil (SKstmt  s sp env k) 

  | IStep_EKswitch : forall cases default k n
      (VEQN: v = Vint n),
      cmp_istep_expr_cont v (EKswitch cases default k) nil  (SKstmt (Sexit (switch_target n default cases)) sp env k)

  | IStep_EKreturn : forall k t
  (LAB: t = (match sp with 
           None => nil | 
           Some stk => (TEmem (MEfree stk MObjStack)::nil) end)),
      cmp_istep_expr_cont v (EKreturn k) t
          (SKreturn v k)

  | IStep_EKstoreaddr : forall chunk e2 k t2 lab ptr v'
     (VEQP: v = Vptr ptr)               
     (E2:cmp_eval_expr sp env t2 e2 v')
     (LAB: lab = TEmem (MEwrite ptr chunk (cast_value_to_chunk chunk v'))),
     cmp_istep_expr_cont v (EKstoreaddr chunk e2 k) (t2 ++ (lab::nil)) (SKstmt Sskip sp env k)

  | IStep_EKstoreval : forall chunk ptr k lab
     (LAB: lab = TEmem (MEwrite ptr chunk (cast_value_to_chunk chunk v))),
      cmp_istep_expr_cont v (EKstoreval chunk (Vptr ptr) k) (lab::nil) (SKstmt Sskip sp env k)
.


End CMP_ISTEP_EXPR_CONT.


Inductive cmp_istep : state -> list thread_event -> state -> Prop :=
| Istep_SKexpr :
  forall sp env e ek te v tek t' s'
  (E:cmp_eval_expr sp env te e v)
  (EK: cmp_istep_expr_cont sp env v ek tek s')
  (TT: t'=te++tek),
  cmp_istep (SKexpr e sp env ek)  t' s'

| Istep_SKval :
  forall sp env ek v tek s'
  (EK: cmp_istep_expr_cont sp env v ek tek s'),
  cmp_istep (SKval v sp env ek) tek  s'

| Istep_clean :
  forall s
  (CL : clean s),
  cmp_istep s nil s.



  

Lemma bool_of_val_functional: forall v' b' b'', 
  Val.bool_of_val v' b' -> Val.bool_of_val v' b'' -> b'=b''.
Proof.
  by inversion 1; clarify; inversion 1; clarify. 
Qed.

Ltac step_correct_dtac :=
  match goal with
    H : cmp_eval_expr _ _ _ (?X _) _ |- _ => inv H
  end.

Lemma app_nil_end2 : forall (A:Type)  (l:list A), nil ++ l = l.
Proof. done. Qed.



Lemma step_correct_unclean:
  forall st1 (t:list thread_event) lab st2 
  (UC: clean st1 = false)
  (T: Cminor.cm_step ge st1 lab st2),
  (forall t st, cmp_istep st2 t st <-> cmp_istep st1 (weakcons lab t) st).
Proof. 
(* prove by case analysis on Cminor.cm_step *)
intros; unfold weakcons.
(cm_step_cases (destruct T) Case); 
   simpl in *; try done; 
   first [Case "StepReturnSome1"; destruct sp | idtac];
     split; inversion 1; clarify; vauto;
       try (by inv EK; vauto).

Case "StepVar". 
- by repeat step_correct_dtac; econstructor; clarify'. 
- by repeat step_correct_dtac; econstructor; clarify'. 

Case "StepUnop1". 
- by inv E; vauto.

Case "StepUnop". 
- change Cminor.eval_unop with eval_unop in EU.
  by inv EK; clarify'; vauto.

Case "StepBinop1". 
- by inv EK; econstructor; try edone; vauto; rewrite -> ?app_ass. 
- by inv E; econstructor; try edone; vauto; rewrite -> ?app_ass. 

Case "StepBinop". 
- change Cminor.eval_binop with eval_binop in EB.
  by inv EK; clarify'; vauto.

Case "StepLoad1". 
- by inv EK; econstructor; try edone; vauto; rewrite -> ?app_ass. 
- by inv E; econstructor; try edone; vauto; rewrite -> ?app_ass. 

Case "StepIfThenElse". 
- by inv EK; econstructor; try edone; vauto; rewrite -> ?app_ass. 
- by inv E; econstructor; try edone; vauto; rewrite -> ?app_ass. 

Case "StepIfThenElseTrue". 
- by inv EK; assert (b1=true); [eby eapply bool_of_val_functional|vauto].

Case "StepIfThenElseFalse". 
- by inv EK; assert (b1=false); [eby eapply bool_of_val_functional|vauto].

Case "StepEmptyCall".
- by repeat step_correct_dtac; econstructor; try edone; vauto; clarify'.
- by inv EK; try done; inv ES; clarify'; vauto.

Case "StepCallArgs1".
- by inv EK; rewrite -> ?app_ass, <- ?app_nil_end, ?app_nil_end2; econstructor; vauto.
- inv EK; inv ES; vauto.

Case "StepCallArgs2".
- by inv EK; rewrite -> ?app_ass, <- ?app_nil_end, ?app_nil_end2; econstructor; vauto.
- inv EK; inv ES. econstructor; try edone; eapply IStep_EKargs; try edone.
  by rewrite -> ?app_ass, <- ?app_nil_end.

Case "StepCallArgs".
- by econstructor; vauto. 
- by inv EK; inv ES; simpl in *; clarify'; vauto.

Case "StepAtomicArgs".
- inv EK; rewrite app_ass in ASTMT;
    econstructor; econstructor; vauto; try edone; by rewrite app_ass.

- eby inv EK; inv ES; (econstructor; [edone| |eby rewrite app_ass]);
   [eapply IStep_EKatargsNone with (vs'' := ((vs ++ v :: nil) ++ v1 :: vl))|
    eapply IStep_EKatargsSome with (vs'' := ((vs ++ v :: nil) ++ v1 :: vl))]; 
   try edone; rewrite app_ass.

Case "StepAtomicFinishNone".
- by econstructor; vauto. 
- by inv EK; inv ES; inv Et'; vauto.

Case "StepAtomicFinishSome".
- eby econstructor; inv EK; vauto.
- by inv EK; inv ES; inv Et'; vauto.

Case "StepCondTrue".
- by inv EK; replace b with true; [vauto|eby eapply bool_of_val_functional].

Case "StepCondFalse".
- by inv EK; replace b with false; [vauto|eby eapply bool_of_val_functional].
Qed.


Inductive cm_via_unclean : state -> list thread_event -> state -> Prop :=
| cm_via_unclean_one : forall st1 st2 lab
    (CL: clean st2)
    (CMSTEP: Cminor.cm_step ge st1 lab st2),
    cm_via_unclean st1 (weakcons lab nil) st2
| cm_via_unclean_cons : forall st1 st2 st3 lab t
    (UC: clean st2 = false)
    (CMSTEP: Cminor.cm_step ge st1 lab st2)
    (VIA : cm_via_unclean st2 t st3),
    cm_via_unclean st1 (weakcons lab t) st3.

Tactic Notation "cm_via_unclean_cases" tactic(first) tactic(c) :=
    first; [
      c "cm_via_unclean_one" |
      c "cm_via_unclean_cons" ].

Lemma cm_via_unclean_one_tau : forall st1 st2
    (CL: clean st2)
    (CMSTEP: Cminor.cm_step ge st1 TEtau st2),
    cm_via_unclean st1 nil st2.
Proof. eby intros; exploit cm_via_unclean_one. Qed.

Lemma cm_via_unclean_cons_tau : forall st1 st2 st3 t
    (UC: clean st2 = false)
    (CMSTEP: Cminor.cm_step ge st1 TEtau st2)
    (VIA : cm_via_unclean st2 t st3),
  cm_via_unclean st1 t st3.
Proof. eby intros; exploit cm_via_unclean_cons. Qed.

Lemma cm_via_unclean_one_nontau : forall st1 st2 lab
    (CL: clean st2)
    (CMSTEP: Cminor.cm_step ge st1 lab st2)
    (NONTAU: lab <> TEtau),
    cm_via_unclean st1 (lab :: nil) st2.
Proof. by intros; exploit cm_via_unclean_one; try edone; destruct lab. Qed.

Lemma cm_via_unclean_cons_nontau : forall st1 st2 st3 lab t
    (UC: clean st2 = false)
    (CMSTEP: Cminor.cm_step ge st1 lab st2)
    (VIA : cm_via_unclean st2 t st3)
    (NONTAU: lab <> TEtau),
  cm_via_unclean st1 (lab :: t) st3.
Proof. by intros; exploit cm_via_unclean_cons; try edone; destruct lab. Qed.

Hint Resolve cm_via_unclean_one_tau cm_via_unclean_cons_tau.
Hint Resolve cm_via_unclean_one_nontau cm_via_unclean_cons_nontau.

Lemma via_unclean_is_to_clean: forall st1 (t:list thread_event) st2
  (VIA: cm_via_unclean st1 t st2),
  clean st2.
Proof.
  by induction 1.
Qed.

Lemma cm_via_unclean_weakcons: forall st1 te t st2 t'
  (VIA:cm_via_unclean st1 t' st2)
  (TT: t'=te::t),
  te::t = weakcons te t.
Proof. 
  induction 1; intros; destruct te; destruct lab; simpl; try done; auto.
Qed.

Lemma step_correct_unclean_forwards:
  forall st1 (t:list thread_event) lab st2 
  (UC: clean st1 = false)
  (T: Cminor.cm_step ge st1 lab st2),
  (forall t st, cmp_istep st2 t st -> cmp_istep st1 (weakcons lab t) st).
Proof. 
  eby intros; apply -> step_correct_unclean.
Qed.

(** forwards correctness of cmp_istep from unclean (and via unclean) to clean *)

Lemma via_unclean_cmp_istep_correct_forwards:
  forall t st1 st2
  (UC: clean st1 = false)
  (VIA: cm_via_unclean st1 t st2),
  cmp_istep st1 t st2 .
Proof. 
  intros; induction VIA. 
  - by eapply step_correct_unclean_forwards; vauto.
  by eapply step_correct_unclean_forwards, IHVIA; vauto.
Qed.


(** Correctness of cmp_step from clean (via unclean) to clean *)

Lemma cmp_step_correct:
  forall st1 t st2
  (CL: clean st1)
  (VIA: cm_via_unclean st1 t st2),
  cmp_step st1 t st2 .
(* prove by case analysis on the first step, using previous lemma if it's not to clean *)
Proof.
intros; (cm_via_unclean_cases (destruct VIA) Case). 

Case "cm_via_unclean_one".
  by (cm_step_cases (destruct CMSTEP) SCase); unfold weakcons; simpl in *; clarify; vauto. 

Case "cm_via_unclean_cons".
  (cm_step_cases (destruct CMSTEP) SCase); unfold weakcons; simpl in *; clarify;
    first [SCase "StepReturnSome"; destruct sp | idtac];
      (eapply via_unclean_cmp_istep_correct_forwards in VIA; try done; 
        inv VIA; try done; inv EK; vauto; rewrite -> ?app_ass, <- ?app_nil_end; vauto;
          rewrite <- app_ass; vauto).
Qed.

Lemma cmp_step_to_clean:
  forall st1 t st2 (STEP:cmp_step st1 t st2), clean st2.
Proof. induction 1; clarify. Qed.

(* construct small-step transitions from Cminor.cm_via_unclean *)
Definition small_step_cm := (small_step_Recep Cminor.state cm_via_unclean).

Lemma small_step_cm_intro: forall s te s',
  small_step_Recep Cminor.state cm_via_unclean s te s' -> 
  small_step_cm s te s'.
Proof. done. Qed.

(* instantiate Simulations.ev_stuck_or_error to Cminor.cm_step (absent
general transition-system machinery *)

Definition cm_stuck s  : Prop :=
  forall s' l, Cminor.cm_step ge s l s' -> False.

Inductive te_read : thread_event -> Prop :=
  te_read_read: forall p c v, te_read (TEmem (MEread p c v)).

(** Eventually will get stuck *)
Inductive cm_ev_stuck s: Prop :=
  | cm_ev_stuck_stuck: 
    cm_stuck s -> cm_ev_stuck s
  | cm_ev_stuck_tau:
    forall {s'}, 
      Cminor.cm_step ge s TEtau s' ->
      cm_ev_stuck s' -> 
      cm_ev_stuck s
  | cm_ev_stuck_te_read:
    forall {l s'},
      te_read l ->
      Cminor.cm_step ge s l s' ->
      (forall l s',
        te_read l ->
        Cminor.cm_step ge s l s' ->
        cm_ev_stuck s') ->
      cm_ev_stuck s.

(* sequences of Cminor tau-erased small-step transitions from clean to
clean-or-unclean via unclean, used to define the match_cm relation below *)

Definition weaksnoc (t: list thread_event) (lab:thread_event) : list thread_event := 
  match lab with
    | TEtau => t
    | _     => t++(lab::nil)
  end.

Inductive cm_to : Cminor.state -> list thread_event -> Cminor.state -> Prop :=
| cm_to_one : forall st1 lab st2 
   (CL: clean st1)
   (CMSTEP: Cminor.cm_step ge st1 lab st2),
   cm_to st1 (weaksnoc nil lab) st2
| cm_to_cons : forall st1 t st2 lab st3 
   (TO : cm_to st1 t st2)
   (UC: clean st2 = false)
   (CMSTEP: Cminor.cm_step ge st2 lab st3),
   cm_to st1 (weaksnoc t lab) st3.

Lemma cm_to_one_tau : forall st1 st2 
    (CL: clean st1)
    (CMSTEP: Cminor.cm_step ge st1 TEtau st2),
  cm_to st1 nil st2.
Proof. eby intros; exploit cm_to_one. Qed.

Lemma cm_to_cons_tau: forall st1 t st2 st3 
   (TO : cm_to st1 t st2)
   (UC: clean st2 = false)
   (CMSTEP: Cminor.cm_step ge st2 TEtau st3),
  cm_to st1 t st3.
Proof. intros; change t with (weaksnoc t TEtau); vauto. Qed.

Inductive match_cm : Cminor.state -> small_step_state Cminor.state -> Prop :=
| Match_cm_zero: forall st0 
   (CL:clean st0),
   match_cm st0 (SSState Cminor.state st0 nil)
| Match_cm_left: forall st0 t st1 te t' st2 
   (CL: clean st0)
   (UC: clean st1 = false)
   (TO: cm_to st0 t st1)
   (TS: cm_via_unclean st1 (te::t') st2),
   match_cm st1 (SSState Cminor.state st0 t)
| Match_cm_right: forall st0 t st1 st2 
   (CL: clean st0)
   (TO: cm_to st0 t st1)
   (UC: clean st1 = false)
   (TS: cm_via_unclean st1 nil st2),
   match_cm st1 (SSState Cminor.state st2 nil).

Tactic Notation "match_cm_cases" tactic(first) tactic(c) :=
    first; [
      c "Match_cm_zero" |
      c "Match_cm_left" |
      c "Match_cm_right" ].

Hint Constructors match_cm. 
Hint Resolve cm_to_one_tau cm_to_cons_tau.

Lemma app_cons_nil: forall A t (lab:A) t1,  (t ++ (lab :: nil)) ++ t1 = t ++ (lab :: t1).
Proof.
  by induction t; intros; simpl; try rewrite IHt.
Qed.

Lemma weaksnoc_weakcons: forall t t1 lab, weaksnoc t lab ++ t1 = t ++ weakcons lab t1.
Proof.
  by destruct lab; simpl; try rewrite app_cons_nil.
Qed.

Lemma to_and_via_TO_via: forall st0 t1 st1 
  (TO : cm_to st0 t1 st1) 
  t2 st2 
  (VIA: cm_via_unclean st1 t2 st2)
  (UC1 : clean st1 = false),
  cm_via_unclean st0 (t1++t2) st2.
Proof.
  induction 1; intros; [|by rewrite weaksnoc_weakcons; eapply IHTO; vauto].
  replace (weaksnoc nil lab ++ t2) with (weakcons lab t2) by (destruct lab; done).
  vauto. 
Qed.

Lemma to_and_step_TO_via: forall st0 t st1 
  (TO : cm_to st0 t st1) 
  te st2 
  (CMSTEP : cm_step ge st1 te st2)
  (NotEqual : te <> TEtau)
  (CL0 : clean st0)
  (UC : clean st1 = false)
  (CL2 : clean st2),
  cm_via_unclean st0 (t++te::nil) st2.
Proof.
  intros; eapply to_and_via_TO_via; eauto.
Qed.

Lemma to_step_via_TO_via: forall st0 t1 st1 te st2 t3 st3
  (TO : cm_to st0 t1 st1) 
  (CMSTEP : cm_step ge st1 te st2)
  (VIA: cm_via_unclean st2 t3 st3)
  (NotEqual : te <> TEtau)
  (CL0 : clean st0)
  (UC1 : clean st1 = false)
  (UC2 : clean st2 = false),
  cm_via_unclean st0 (t1++te::t3) st3.
Proof.
  intros; eapply to_and_via_TO_via; eauto.
Qed.

(**
<<
cm_step    C --tau->U--l1-->U--l2-->U--tau->U--tau-->C'       C --tau--> C'

match_cm   C,[]     C,[]    C,[l1]  C',[]   C',[]    C',[]    []         []
           zero     left    left    right   right    zero     zero       zero


cm_to      .--[]--->.                                         . --[]---> .
           .--[l1]--------->.
           .--[l1;l2]-------------->.
           .--[l1;l2]---------------------->.
           .--[l1;l2]------------------------------->.
 
cm_via_unclean                               .--[]-->.
                                     . ---[l2]------>.
                             .---------[l1;l2]------>.
                    .------------------[l1;l2]------>.
           .---------------------------[l1;l2]------>.

small_step C,[] -----l1-------> C,[l1] -----l2------>C',[]    C,[] --Tau-> C',[]
                     Step1                Step2                     Step3

(which is (small_step cm_via_unclean) )
>>
*)


(* expressions with measure > 1 cannot write *)
Lemma  cm_no_expr_write: forall st1 te st2
  (NZM: ~(measure st1 = 0%nat))
  (NOM: ~(measure st1 = 1%nat))
  (TRAN:cm_step ge st1 te st2),
  te_read te \/ te = TEtau \/ match te with TEmem (MErmw _ _ _ _) => True | _ => False end.
Proof. intros; inv TRAN; vauto. Qed.

Lemma minimum_measure_of_expr: forall e, measure_expr e <> 0%nat.
Proof. by induction e. Qed. 

Lemma minimum_measure_of_expr_cont: forall ek, measure_expr_cont  ek<> 0%nat.
Proof. by induction ek. Qed. 

Lemma nonzero_plus: forall (n m : nat) (NZ:n<>0%nat), (n + m)%nat <>0%nat.
Proof. intros; omega. Qed.

Lemma minimum_measure_of_unclean: forall st
  (UC: clean st = false),
  measure st <> 0%nat. 
Proof.
destruct st; simpl; intros; try done; 
eauto using nonzero_plus, minimum_measure_of_expr, minimum_measure_of_expr_cont.
Qed.

Lemma measure_zero_is_clean: forall st
  (MZ: measure st = 0%nat),
  clean st.
Proof.
intros; pose proof (minimum_measure_of_unclean st); destruct (measure st); try done.
by destruct (clean st); [| elim H].
Qed.

Require Import Classical.

Lemma stuck_or_via: forall st1
  (UC: clean st1 = false),
  (cm_ev_stuck st1) \/ (exists st2, exists t, cm_via_unclean st1 t st2).
Proof.
(* Prepare statement for induction *)
intro st1; generalize (refl_equal (measure st1)).
generalize (measure st1) at 2; intro n; revert st1.
(* Do induction *)
induction n using lt_wf_ind; intros.
destruct (cm_progress_dec ge st1) as [|(l & st1' & STEP)]; [by vauto|].
case_eq (clean st1'); intro C.
- eby right; eexists; eexists; eapply cm_via_unclean_one.

(* the case where measure st1 = 1 is special, as there there might be
a non-{tau,read} label, so let's deal with that first *)

assert (measure st1 <> 0%nat) by (eapply minimum_measure_of_unclean; done).

assert (H2: (measure st1 = 0%nat)%nat + ((measure st1 = 1%nat) + (1%nat < measure st1)%nat)). 
  by destruct (measure st1) as [|[]] ; auto with arith.

destruct H2 as [H2|[H2|H2]]; try done.

Case "measure st1 = 1".
assert (measure st1' < measure st1)%nat. eby eapply decreasing_measure_from_unclean. 
rewrite measure_zero_is_clean in C; try done; omega.

Case "measure st1 > 1".
exploit cm_no_expr_write; try eassumption; try omega; intros [READ | [TAU | RMW]]; clarify.

SCase "read".
destruct (classic (forall l' st1'',
        te_read l' ->
        cm_step ge st1 l' st1'' ->
        cm_ev_stuck st1'')). 
- eby left; eapply cm_ev_stuck_te_read.

assert (X: exists l', exists st1'', te_read l' /\ cm_step ge st1 l' st1'' /\ ~cm_ev_stuck st1'').
  by apply NNPP; intro; case H0; intros; apply NNPP; intro; case H3; vauto.
destruct X as (l' & st1'' & READ' & STEP' & NSTUCK).
case_eq (clean st1''); intro C'; [eby right; eexists; eexists; eapply cm_via_unclean_one|].
exploit (H (measure st1'')); try done; try eby eapply decreasing_measure_from_unclean.
by intros [STUCK|(st2 & t & VIA)]; try done; right; eexists; eexists; vauto.

SCase "TEtau".
exploit (H (measure st1')); try done; try eby eapply decreasing_measure_from_unclean.
by intros [STUCK|(st2 & t & STEP')]; [left |right; eexists; eexists]; vauto. 

SCase "Rmw".
destruct l as [|[]| | | | | |]; clarify.
assert (exists st2', cm_step ge st1' TEtau st2' /\ clean st2')
  by (inv STEP; clarify; eexists; vauto).
des; right; eexists; eexists; vauto.
Qed.

Hint Resolve small_step_cm_intro.
Hint Constructors small_step_Recep.
Hint Resolve decreasing_measure_from_unclean.
Hint Resolve decreasing_measure_to_unclean.
Hint Resolve te_samekind_nottau.

Lemma cm_small_step_correct_helper:
 forall st1 te st2 st0 t te0 t' st5
    (S : cm_step ge st1 te st2)
    (NotEqual : te <> TEtau)
    (CL : clean st0)
    (UC : clean st1 = false)
    (TO : cm_to st0 t st1)
    (TS : cm_via_unclean st1 (te0 :: t') st5)
    (C : clean st2 = false),
    exists sst2, small_step_cm (SSState state st0 t) te sst2.
Proof.
  intros; inv TS; simpl in *; [by inv S; try done; inv CMSTEP|].

  exploit Cminor.cm_determinate; [eapply CMSTEP | eapply S|intros (? & ?)].
  exploit Cminor.cm_determinate; [eapply S | eapply CMSTEP|intros (? & _)].

  assert (X: lab = te0 /\ t0 = t') by (destruct lab; simpl in *; clarify); destruct X; clarify.
  assert (te0 <> TEtau) by eauto.
  destruct (thread_event_eq_dec te0 te) as [|N]; clarify.
  - by destruct t'; eexists; eauto 8 using to_and_via_TO_via.

  destruct (classic (exists stB : state,
    exists tb : list thread_event,
      cm_via_unclean st0 (t ++ te :: tb) stB)) as [(stB & tb & X)|].
  - by destruct tb; eexists; eauto 8 using to_and_via_TO_via.

  eby destruct t'; eexists; eauto;
      [eapply StepRecep2r | eapply StepRecep1r]; try eapply N; try done;
      (try do 3 eexists); eapply to_and_via_TO_via; try edone;
      eapply cm_via_unclean_cons_nontau.
Qed.

Lemma cm_small_step_correct:
  forall st1 te st2 sst1
  (S: cm_step ge st1 te st2)
  (M: match_cm st1 sst1),
  (exists sst2, 
      ( (te=TEtau /\ (sst2=sst1 /\ (measure st2 < measure st1)%nat)) \/
        small_step_cm sst1 te sst2) /\
      (match_cm st2 sst2 \/ cm_ev_stuck st2)).
Proof.  
  intros; destruct sst1 as [st0 t|]; [|by inv M]. 
  destruct (thread_event_eq_dec te TEtau) as [->|NotEqual]. 

  (* CASE Tau *)
  (match_cm_cases (inversion M; subst) Case).

    Case "Match_cm_zero".
    (* case split on clean(st2)
        - if yes, then use Step3 to Match_cm_zero
        - if no, case split on whether st2 is stuck or has a --via--> somewhere:
          - if stuck, then done
          - if via, then case split on whether that via has a visible label
             - if no, use Step3 to Match_cm_right
             - if yes, stutter to Match_cm_left *)

    case_eq (clean st2); intro C. 
      (* Case clean st2 *)
      by eauto 9 using Step3.

      (* Case ~clean st2 *)
      destruct (stuck_or_via st2 C) as [|(st3 & t & VIA)].
      - by eauto 10.
      by destruct t; clarify; eauto 10 using Step3.

    Case "Match_cm_left".
    (* stutter to Match_cm_left (using determinacy to stay in the same to/via sequence) *)

    (* decompose the start of the via sequence *)
    inv TS.  

      (* cm_via_unclean_one *)  (* find a contradiction *) 
      by destruct (Cminor.cm_determinate _ _ _ _ _ _ S CMSTEP); simpl in *; clarify.

      (* cm_via_unclean_cons *) (* stutter *)
      destruct (Cminor.cm_determinate _ _ _ _ _ _ S CMSTEP) as [? X]; simpl in *; clarify.
      by specialize (X (refl_equal _)); simpl in *; clarify; eauto 12.

    Case "Match_cm_right".
      inv TS; destruct (Cminor.cm_determinate _ _ _ _ _ _ S CMSTEP) as [? X]; simpl in *; clarify;
      by specialize (X (refl_equal _)); simpl in *; clarify; eauto 12.

  (* CASE Non-Tau *)
  (match_cm_cases (inv M) Case).

    Case "Match_cm_zero".
    (* Case "Match_cm_zero"  and Case "Match_cm_left".*)
    (* case split on clean(st2)
       - if yes, then use Step2 to Match_cm_zero
       - if no, case split on whether st2 stuck or  --via--> somewhere:
          - if stuck, then done
          - if via, then case_split on whether that via has a visible label
             - if no, use Step2 to Match_cm_right
             - if yes, use Step1 to Match_cm_left *)
    case_eq (clean st2); intro C. 

      (* Case clean st2 *)
      exists (SSState _ st2 nil); split; auto.
      by right; eapply StepRecep2; simpl; eauto.

      (* Case ~clean st2 *)
      destruct (stuck_or_via st2 C) as [|(st3 & t & VIA)]; [by destruct S|]. 
        destruct t. 

          (* t=nil *)
          assert (cm_via_unclean st0 (weakcons te nil) st3) by vauto.
          assert (cm_to st0 (weaksnoc nil te) st2) by vauto.
          eexists; split.
          - right; eapply StepRecep2; try done.
            by replace (te::nil) with (weakcons te nil) by (destruct te; done); vauto. 
          by left; eapply (Match_cm_right st0 (weaksnoc nil te) st2 st3).

          (* t <> nil *)
          eexists; split.
          - right; eapply StepRecep1; try done; simpl; eexists; exists t; exists t0.
            by replace (te::t::t0) with (weakcons te (t::t0)) by (destruct te; done); vauto. 
          left; eapply (Match_cm_left); try edone. 
          replace (te::nil) with (weaksnoc nil te) by (destruct te; done); vauto.

    Case "Match_cm_left". (* a lot like the Match_cm_zero case *)
    case_eq (clean st2); intro C. 

      (* Case clean st2 *)
      eexists; split. 
      - eby right; eapply StepRecep2; try edone; eapply (to_and_step_TO_via).
      - by auto.

      (* Case ~clean st2 *)
      destruct (stuck_or_via st2 C) as [STUCK|(st3 & t2 & VIA)].
      - by exploit cm_small_step_correct_helper; try eassumption; []; intros [? ?]; eauto.

      destruct t2 as [|te' t3]. 
        (* t2=nil *)
        assert (cm_via_unclean st0 (t++te::nil) st3). eby  eapply to_step_via_TO_via.
        assert (cm_to st0 (weaksnoc t te) st2). vauto.
        eexists; split; [eby right; eapply StepRecep2|]. 
        left; eby eapply Match_cm_right.

        (* t2 <> nil *)
        eexists; split. right; eapply StepRecep1; try done.
        eby eexists; eexists; eexists; eapply to_step_via_TO_via.
        left; eapply Match_cm_left; try edone.
        replace (t++te::nil) with (weaksnoc t te) by (by destruct te); vauto. 

    Case "Match_cm_right". 
    (* contradict determinacy *)
    by inv TS; assert (lab=TEtau) by (destruct lab; clarify); clarify;
       destruct (Cminor.cm_determinate _ _ _ _ _ _ CMSTEP S); simpl in *; clarify. 
Qed.

End RELSEM.
