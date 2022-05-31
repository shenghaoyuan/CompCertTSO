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



(** CminorSelPrime: new semantics for CminorSel, inductive on expressions,
to use in proof of instruction selection phase (and perhaps also for CminorSel -> RTL) *)


(** The Cminor language after instruction selection. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Floats.
Require Import Pointers.
Require Import Events.
Require Import Values.
Require Import Mem.
Require Import Cminor.
Require Import Op.
Require Import Globalenvs.
Require Import Switch.
Require Import Memcomp.
Require Import Smallstep.
Require Import Libtactics.

(* this should be pulled out into Events *)
Definition weakcons (lab:thread_event) (t: list thread_event) : list thread_event := 
 match lab with
   | TEtau => t
   | _     => lab::t
end.


(** * Abstract syntax *)

(** CminorSel programs share the general structure of Cminor programs:
  functions, statements and expressions.  However, CminorSel uses
  machine-dependent operations, addressing modes and conditions,
  as defined in module [Op] and used in lower-level intermediate
  languages ([RTL] and below).  Moreover, to express sharing of
  sub-computations, a "let" binding is provided (constructions
  [Elet] and [Eletvar]), using de Bruijn indices to refer to "let"-bound
  variables.  Finally, a variant [condexpr] of [expr]
  is used to represent expressions which are evaluated for their
  boolean value only and not their exact value.
*)

(** VV: Note I haven't given semantics to [Elet] 
    and [Eletvar] -- I think they should be removed. *)

(** PS: I've removed [Eletvar] and renamed [Elet] to [Ediscard] -
keeping that so that this phase can have an on-the-nose expression
trace preservation proof *)

Inductive expr : Type :=
  | Evar : ident -> expr
  | Eop : operation -> exprlist -> expr
  | Eload : memory_chunk -> addressing -> exprlist -> expr
  | Econdition : condexpr -> expr -> expr -> expr
  | Ediscard : expr -> expr -> expr 
(*  | Eletvar : nat -> expr *)

with condexpr : Type :=
  | CEtrue: condexpr
  | CEfalse: condexpr
  | CEcond: condition -> exprlist -> condexpr
  | CEcondition : condexpr -> condexpr -> condexpr -> condexpr

with exprlist : Type :=
  | Enil: exprlist
  | Econs: expr -> exprlist -> exprlist.

Infix ":::" := Econs (at level 60, right associativity) : cminorsel_scope.

(** Statements are as in Cminor, except that the condition of an
  if/then/else conditional is a [condexpr], and the [Sstore] construct
  uses a machine-dependent addressing mode. *)

Inductive stmt : Type :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sstore : memory_chunk -> addressing -> exprlist -> expr -> stmt
  | Scall : option ident -> signature -> expr -> exprlist -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: condexpr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: expr -> list (int * nat) -> nat -> stmt
  | Sreturn: option expr -> stmt
  | Slabel: label -> stmt -> stmt
  | Sgoto: label -> stmt
  | Sthread_create: expr -> expr -> stmt 
  | Satomic: option ident -> atomic_statement -> exprlist -> stmt
  | Sfence: stmt.

Record function : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list ident;
  fn_stackspace: Z;
  fn_body: stmt
}.

Definition fundef := Ast.fundef function.
Definition program := Ast.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.

(** * Operational semantics *)

(** Three kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [env]: local environments, map local variables to values;
*)

Definition genv := Genv.t fundef.
(*Definition letenv := list val.*)

(** Continuations *)

Inductive cont: Type :=
  | Kstop: cont                         (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kblock: cont -> cont                (**r exit a block, then do cont *)
  | Kcall: option ident -> fundef -> option pointer -> env -> cont -> cont.
                                        (**r return to caller *)

(*
Inductive expr_cont : Type :=
  | EKlist : exprlist -> list val -> exprlist_cont -> expr_cont
  | EKcall : option ident -> signature -> exprlist -> cont -> expr_cont
  | EKassign : ident -> cont -> expr_cont
  | EKthread1 : expr -> cont -> expr_cont
  | EKthread2 : pointer -> cont -> expr_cont
  | EKswitch: list (int * nat) -> nat -> cont -> expr_cont
  | EKreturn:  cont -> expr_cont
  | EKstoreval: memory_chunk -> pointer -> cont -> expr_cont

with condexpr_cont : Type := 
  | CEKcondition : expr -> expr -> expr_cont -> condexpr_cont
  | CEKcondition2 : condexpr -> condexpr -> condexpr_cont -> condexpr_cont
  | CEKifthenelse: stmt -> stmt -> cont -> condexpr_cont

with exprlist_cont : Type :=
  | LEKop : operation -> expr_cont -> exprlist_cont
  | LEKload : memory_chunk -> addressing -> expr_cont -> exprlist_cont
  | LEKcond : condition -> condexpr_cont -> exprlist_cont
  | LEKstoreaddr: memory_chunk -> addressing -> expr -> cont -> exprlist_cont
  | LEKcall : option ident -> fundef -> cont -> exprlist_cont.
*)

(** States *)

Inductive state: Type :=
(*   | SKexpr:                      (**r Execution of an expression *) *)
(*       forall (e: expr)                  (**r expression under consideration *) *)
(*              (sp: option pointer)       (**r current stack pointer *) *)
(*              (env: env)                 (**r current local environment *) *)
(*              (k: expr_cont),            (**r its continuation -- what to do next *) *)
(*       state *)
(*   | SKcondexpr:                  (**r Execution of a conditional expression *) *)
(*       forall (e: condexpr)              (**r conditional expression under consideration *) *)
(*              (sp: option pointer)       (**r current stack pointer *) *)
(*              (env: env)                 (**r current local environment *) *)
(*              (k: condexpr_cont),        (**r its continuation -- what to do next *) *)
(*       state *)
(*   | SKexprlist:                      (**r Execution of an expression *) *)
(*       forall (el: exprlist)             (**r expressions under consideration *) *)
(*              (vl: list val)             (**r values computed so far *) *)
(*              (sp: option pointer)       (**r current stack pointer *) *)
(*              (env: env)                 (**r current local environment *) *)
(*              (k: exprlist_cont),        (**r its continuation -- what to do next *) *)
(*       state *)
(*   | SKval:                       (**r Execution that has returned a value *) *)
(*       forall (v: val)                   (**r value under consideration *) *)
(*              (sp: option pointer)       (**r current stack pointer *) *)
(*              (env: env)                 (**r current local environment *) *)
(*              (k: expr_cont),            (**r its continuation -- what to do next *) *)
(*       state *)

  | SKstmt:                      (**r Execution of a statement *)
      forall (s: stmt)                  (**r statement under consideration *)
             (sp: option pointer)       (**r current stack pointer *)
             (env: env)                 (**r current local environment *)
             (k: cont),                 (**r its continuation -- what to do next *)
      state
  | SKcall:                      (**r Invocation of a function *)
      forall (args: list val)           (**r arguments provided by caller *)
             (k: cont),                 (**r what to do next  *)
      state
  | SKexternal:                    (**r Waiting for result of external function *)
      forall (efsig: signature)         (**r Return value *)
             (k: cont),                 (**r what to do next *)
      state
  | SKreturn:                    (**r Return from a function *)
      forall (v: val)                   (**r Return value *)
             (k: cont),                 (**r what to do next *)
      state.


Section RELSEM.

Variable ge: genv.

Section EVAL_EXPR.


Variable sp: option Pointers.pointer.
Variable env: env.


Inductive eval_expr: list thread_event -> expr -> val -> Prop :=
  | eval_Evar: forall id v
      (EVAL : PTree.get id env = Some v),
      eval_expr nil (Evar id) v
  | eval_Eop: forall op tl el vl v
      (EE : eval_exprlist tl el vl)
      (EVAL: eval_operation ge sp op vl = Some v),
      eval_expr tl (Eop op el) v
  | eval_Eload: forall c addressing el v t tl vl p
      (EE : eval_exprlist tl el vl)
      (EVAL: eval_addressing ge sp addressing vl = Some (Vptr p))
      (HT : Val.has_type v (type_of_chunk c))
      (TT : t = tl++((TEmem(MEread p c v)) :: nil)),
      eval_expr t (Eload c addressing el) v
  | eval_Econdition: forall t1 t23 ce1 e2 e3 vb1 v23 t
      (EC : eval_condexpr t1 ce1 vb1)
      (EE : eval_expr t23 (if vb1 then e2 else e3) v23)
      (TT : t = t1++t23),
      eval_expr t (Econdition ce1 e2 e3) v23
  | eval_Ediscard: forall e1 t1 v1 e2 t2 v2 t
      (EE : eval_expr t1 e1 v1)
      (EE : eval_expr t2 e2 v2)
      (TT : t = t1 ++ t2),
      eval_expr t (Ediscard e1 e2) v2

with eval_condexpr: list thread_event -> condexpr -> bool -> Prop :=
  | eval_CEtrue: 
      eval_condexpr nil CEtrue true
  | eval_CEfalse: 
      eval_condexpr nil CEfalse false
  | eval_CEcond: forall t cond al vl b
      (EE: eval_exprlist t al vl )
      (EC: eval_condition cond vl = Some b),
      eval_condexpr t (CEcond cond al) b
  | eval_CEcondition: forall t t1 t23 ce1 ce2 ce3 vb1 vb23
      (CE1: eval_condexpr t1 ce1 vb1)
      (CE23: eval_condexpr t23 (if vb1 then ce2 else ce3) vb23)
      (TT: t = t1++t23),
      eval_condexpr t (CEcondition ce1 ce2 ce3) vb23

with eval_exprlist: list thread_event -> exprlist -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist nil Enil nil
  | eval_Econs: forall t1 tl e1 el v1 vl t
      (EE : eval_expr t1 e1 v1)
      (EL : eval_exprlist tl el vl)
      (TT : t = t1++tl),
      eval_exprlist t (Econs e1 el) (v1 :: vl).


(* the above does not include taus (eg to match the Cminor taus on the
nose) as they will not be preserved by selection *)

Scheme eval_expr_ind3 := Minimality for eval_expr Sort Prop
  with eval_condexpr_ind3 := Minimality for eval_condexpr Sort Prop
  with eval_exprlist_ind3 := Minimality for eval_exprlist Sort Prop.

End EVAL_EXPR.


(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kblock k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

(** Find the statement and manufacture the continuation  *)
(*   corresponding to a label *)

Fixpoint find_label (lbl: label) (s: stmt) (k: cont)
                    {struct s}: option (stmt * cont) :=
  match s with
  | Sseq s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sloop s1 =>
      find_label lbl s1 (Kseq (Sloop s1) k)
  | Sblock s1 =>
      find_label lbl s1 (Kblock k)
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end.

Definition get_fundef (k: cont) : option fundef :=
  match k with
   | Kcall _ fd _ _ _ => (Some fd)
   | _ => None
  end.

(** * Operational semantics *)

(* Open Scope cminorsel_scope. *)


Inductive step : state -> list thread_event -> state -> Prop :=
(* Skip *)
| StepSkipBlock:
  forall sp k env,
  step (SKstmt Sskip sp env (Kblock k))
          nil
          (SKstmt Sskip sp env k)
(* Assign *)
| StepAssign:
  forall sp v id e env env' k t
  (E:eval_expr sp env t e v)
  (VLS : PTree.set id v env = env'),
  step (SKstmt (Sassign id e) sp env k)
           t
           (SKstmt Sskip sp env' k)
(* Store *)
| StepStore:
  forall sp chunk el e2 env k tl lab ptr vl t2 v2 addressing
  (EL:eval_exprlist sp env tl el vl)
  (E2:eval_expr sp env t2 e2 v2)
  (EVAL: eval_addressing ge sp addressing vl = Some (Vptr ptr))
  (LAB: lab = TEmem (MEwrite ptr chunk 
                (cast_value_to_chunk chunk (Val.conv v2 (type_of_chunk chunk))))),
  step (SKstmt (Sstore chunk addressing el e2) sp env k) 
           (tl ++ t2 ++ (lab::nil))
           (SKstmt Sskip sp env k)
(* Call *)
| StepCall:
  forall optid sig ef  args sp env k fd tf vf targs vargs t
  (EF: eval_expr sp env tf ef vf)
  (ES : eval_exprlist sp env targs args vargs)
  (TEQ : t = tf ++ targs)
  (SIG: funsig fd = sig)
  (GFF : Genv.find_funct ge vf = Some fd),
  step (SKstmt (Scall optid sig ef args) sp env k)
          t
          (SKcall vargs (Kcall optid fd sp env k))
(* Atomic *)
| StepAtomicNone: forall sp env k targs args vargs v' t astmt lab
  (ES : eval_exprlist sp env targs args vargs)
  (ASME : atomic_statement_mem_event astmt vargs v' lab)
  (TY : Val.has_type v' (type_of_chunk Mint32))
  (Et : t = targs ++ (TEmem lab) :: nil),
  step     (SKstmt (Satomic None astmt args) sp env k)
           t
           (SKstmt Sskip sp env k)
| StepAtomicSome: forall sp env k targs args vargs v' t astmt id env' lab
  (ES : eval_exprlist sp env targs args vargs)
  (ASME : atomic_statement_mem_event astmt vargs v' lab)
  (TY : Val.has_type v' (type_of_chunk Mint32))
  (Ee : PTree.set id v' env = env')
  (Et : t = targs ++ (TEmem lab) :: nil),
  step     (SKstmt (Satomic (Some id) astmt  args) sp env k)
           t
           (SKstmt Sskip sp env' k)
| StepFence:
  forall sp k env,
  step (SKstmt Sfence sp env k)
       (TEmem MEfence :: nil)
       (SKstmt Sskip sp env k)
(* Seq *)
| StepSeq:
  forall sp s1 s2 env k,
  step (SKstmt (Sseq s1 s2) sp env k)
          nil
          (SKstmt s1 sp env (Kseq s2 k))
(* Conditional Statement *)
| StepCond:
  forall sp ce s1 s2 env k t vb
  (E:eval_condexpr sp env t ce vb),
  step (SKstmt (Sifthenelse ce s1 s2) sp env k)
           t
           (SKstmt  (if vb then s1 else s2) sp env k) 
(* Loop *)
| StepLoop:
  forall sp s env k,
  step (SKstmt (Sloop s) sp env k)
          nil
          (SKstmt s sp env (Kseq (Sloop s) k)) 
(* Block *)
| StepBlock:
  forall sp s env k,
  step (SKstmt (Sblock s) sp env k)
          nil
          (SKstmt s sp env (Kblock k))
(* Exit *)
| StepExitSeq:
  forall sp n s k env,
  step (SKstmt (Sexit n) sp env (Kseq s k))
          nil
          (SKstmt (Sexit n) sp env k)
| StepExitBlock:
  forall sp env k,
  step (SKstmt (Sexit 0) sp env (Kblock k))
          nil
          (SKstmt Sskip sp env k)
| StepExitBlock1:
  forall sp n env k,
  step (SKstmt (Sexit (S n)) sp env (Kblock k))
          nil
          (SKstmt (Sexit n) sp env k)
(* Switch *)
| StepSwitch:
  forall sp e cases default env k t n
  (E:eval_expr sp env t e (Vint n)),
  step (SKstmt (Sswitch e cases default) sp env k)
           t
           (SKstmt (Sexit (switch_target n default cases)) sp env k)
(* Label *)
| StepLabel:
  forall sp lbl s env k,
  step (SKstmt (Slabel lbl s) sp env k)
          nil
          (SKstmt s sp env k)
(* Goto *)
| StepGoto:
  forall sp f lbl k s' k' k'' env
  (CC : call_cont k = k')
  (GFD : get_fundef k' = (Some (Internal f)))
  (FL : find_label lbl f.(fn_body) k' = Some (s', k'')),
  step (SKstmt (Sgoto lbl) sp env k)
          nil
          (SKstmt s' sp env k'')
(* Return *)
| StepReturnNone:
  forall sp sp' f k k' env env' lab t
  (CC : call_cont k = (Kcall None (Internal f) sp' env' k'))
  (FSIG : f.(fn_sig).(sig_res) = None)
  (LAB: lab = (match sp with 
           None => TEtau | 
           Some stk => TEmem (MEfree stk MObjStack) end))
  (TEQ: t = weakcons lab nil),
  step (SKstmt (Sreturn None) sp env k)
           t
           (SKreturn Vundef k)
| StepReturnSome:
  forall sp e f k env v t t' lab
  (CC : get_fundef (call_cont k) = Some (Internal f))
  (FSIG : f.(fn_sig).(sig_res) <> None)
  (EE : eval_expr sp env t e v)
  (LAB: lab = (match sp with 
           None => TEtau | 
           Some stk => TEmem (MEfree stk MObjStack) end))
  (TEQ: t' = (t++(weakcons lab nil))),
  step (SKstmt (Sreturn (Some e)) sp env k)
          t'
          (SKreturn v k)

| StepReturnFinish:
  forall sp v fd optid k k' env' env''
  (CC : call_cont k = (Kcall optid fd sp env' k'))
  (VLS : set_optvar optid v env' = env''),
  step (SKreturn v k)
          nil
          (SKstmt Sskip sp env'' k')
(* Internal Call *)
| StepFunctionInternalNoStack:
  forall sp optid f vs k env env' ck
  (CC : ck  = (Kcall optid (Internal f) sp env' k))
  (FZ : f.(fn_stackspace) = 0)
  (INIT : set_locals f.(fn_vars) (set_params vs f.(fn_params)) = env),
  step (SKcall vs ck)
          nil
          (SKstmt f.(fn_body) None env ck)
| StepFunctionInternalWithStack:
  forall sp optid p f vs k env env' ck fsize
  (CC : ck  = (Kcall optid (Internal f) sp env' k))
  (EQfsize : fsize = f.(fn_stackspace))
  (FNZ : fsize <> 0)
  (INIT : set_locals f.(fn_vars) (set_params vs f.(fn_params)) = env),
  step (SKcall vs ck)
          ((TEmem (MEalloc p (Int.repr fsize) MObjStack))::nil)
          (SKstmt f.(fn_body) (Some p) env ck)
(* External Call *)
| StepExternalCall:
  forall sp k ef vargs evargs tgt env id efsig ck
  (EARGS : vargs = map val_of_eval evargs),
  id = ef.(ef_id) ->
  efsig = ef.(ef_sig) ->
  ck = (Kcall tgt (External ef) sp env k) ->
  step (SKcall vargs ck)
          ((TEext (Ecall id evargs))::nil)
          (SKexternal efsig ck)
| StepExternalReturn:
  forall efsig vres evres k typ
  (TYP : typ = (match sig_res efsig with Some x => x | None => Tint end))
  (HT : Val.has_type vres typ)
  (ERES : vres = val_of_eval evres),
  step (SKexternal efsig k)
          ((TEext (Ereturn typ evres))::nil)
          (SKreturn vres k)
(* Continuation Management *)
| StepNext:
  forall sp s k env,
  step (SKstmt Sskip sp env (Kseq s k))
          nil
          (SKstmt s sp env k)
| StepStop:
  forall sp env,
  step (SKstmt Sskip sp env Kstop)
          (TEexit::nil)
         (SKstmt Sskip sp env Kstop)
(* Thread *)
| StepThread : 
  forall sp efn earg k env v p tfn targ t
  (EFN:eval_expr sp env tfn efn (Vptr p))
  (EARG:eval_expr sp env targ earg v)
  (TEQ: t = tfn ++ targ ++ ((TEstart p (v::nil)):: nil)),
  step (SKstmt (Sthread_create efn earg) sp env k)
           t
           (SKstmt Sskip sp env k)
.

Definition cms_init  (p : pointer) (vs : list val) :=
  match Genv.find_funct_ptr ge p with
   | Some (Internal f)  => 
       if beq_nat (length vs) (length f.(fn_sig).(sig_args))
         then Some (SSState _ (SKcall (Val.conv_list vs f.(fn_sig).(sig_args))
                                      (Kcall None (Internal f) None (PTree.empty _) Kstop)) nil)
         else None
   | _ => None
  end.

End RELSEM.


Hint Constructors eval_expr eval_condexpr eval_exprlist: evalexpr.

Hint Constructors step: cminorsel. 

Definition small_step_cs ge := small_step_Recep state (step ge).

Definition cms_ge_init (p : program) (ge : genv) (m : Mem.mem) := 
  Genv.globalenv_initmem p ge low_mem_restr m.


(** * TSO machine setup *)

Section CminorSel_TSO.

(*
Fixpoint measure_e (e : expr) : nat :=
  match e with
    | Evar _ => 2
    | Eop _ es => 2 + measure_el es
    | Eload _ _ es => 2 + measure_el es
    | Econdition ce e1 e2 => 2 + measure_c ce + measure_e e1 + measure_e e2
    | Ediscard e1 e2 => 2 + measure_e e1 + measure_e e2
  end%nat
with measure_c (e : condexpr) : nat :=
  match e with
    | CEtrue => 2
    | CEfalse => 2
    | CEcond _ el => 2 + measure_el el
    | CEcondition e1 e2 e3 => 2 + measure_c e1 + measure_c e2 + measure_c e3
  end%nat
with measure_el (es : exprlist) : nat :=
  match es with
    | Enil => 2
    | Econs e es => 2 + measure_e e + measure_el es
  end%nat.

Definition measure_stmt (s : stmt) :=
  match s with
  | Sassign id e => 1 + measure_e e
  | Sstore _ _ es e => 1 + measure_el es + measure_e e
  | Scall _ _ e es => 1 + measure_el es + measure_e e
  | Stailcall _ e es => 1 + measure_el es + measure_e e
  | Sifthenelse c s1 s2 => 1 + measure_c c
  | Sswitch e _ _ => 1 + measure_e e
  | Sreturn (Some e) => 1 + measure_e e
  | Sthread_create e1 e2 => measure_e e1 + measure_e e2 
  | Satomic _ _ es => measure_el es
  | _ => 0
  end%nat.
*)

Scheme expr_ind3 := Induction for expr Sort Prop
  with exprlist_ind3 := Induction for exprlist Sort Prop
  with exprcond_ind3 := Induction for condexpr Sort Prop.

Definition traces_deter (t1 t2 : list thread_event) :=
  forall t t1' t2'
    (Et1 : t1 = t ++ t1')
    (Et2 : t2 = t ++ t2'),
    match t1', t2' with
      | te1 :: r1, te2 :: r2 => te_samekind te1 te2
      | nil, nil => True
      | _, _ => False
    end.

Lemma traces_deter_refl: forall t, traces_deter t t.
Proof.
  red; intros; clarify.
  rewrite (app_inv_head _ _ _ H0); destruct t2'; try done.
  by destruct t as [[]|[]| | | | | |].
Qed.

Hint Resolve traces_deter_refl.

Lemma eq_app_cases:
  forall {A} {l1 : list A} {l2 l3 l4}
  (E : l1 ++ l2 = l3 ++ l4),
  (exists l', l3 = l1 ++ l' /\ l2 = l' ++ l4) \/
  (exists l', l1 = l3 ++ l' /\ l4 = l' ++ l2).
Proof.
  induction l1; simpl; intros; clarify; eauto.
  destruct l3; simpl in *; clarify; eauto.
  exploit IHl1; [eassumption|intro; des; clarify; eauto].
Qed.

Lemma deter_eq:
  forall t1 t2 t1' t2', 
    traces_deter t1 t2 ->
    t1 ++ t1' = t2 ++ t2' ->
    t1 = t2 /\ t1' = t2'.
Proof.
  induction t1; destruct t2; simpl; intros; clarify;
    try (by specialize (H nil _ _ (refl_equal _) (refl_equal _))). 
  exploit IHt1; try eassumption; [|intuition congruence].
  by red; intros; clarify; eapply (H (_ :: _)). 
Qed.

Lemma traces_deter_app: 
  forall l1 l2 l1' l2',
    traces_deter l1 l2 ->
    (l1 = l2 -> traces_deter l1' l2') ->
    traces_deter (l1 ++ l1') (l2 ++ l2').
Proof.
  red; intros.
  destruct (eq_app_cases Et1); des; clarify.
  - rewrite app_ass in Et2; symmetry in Et2; eapply deter_eq in Et2; try done.
    eby des; clarify; eapply H0. 
  destruct (eq_app_cases Et2); des; clarify.
  - rewrite app_ass in H; specialize (H l2 _ _ (refl_equal _) (app_nil_end _)); 
    destruct x; try done; destruct l'; try done; simpl in *.
    rewrite <- !app_nil_end in *.
    by apply (H0 (refl_equal _) nil).
  - specialize (H _ _ _ (refl_equal _) (refl_equal _)); destruct x; destruct l'; try done.
    by apply (H0 (refl_equal _) nil).
Qed.

Lemma traces_deter_single: 
  forall a b,
    te_samekind a b ->
    traces_deter (a :: nil) (b :: nil).
Proof.
  red; intros.
  repeat match goal with 
    | H : nil = ?t1 ++ ?t2 |- _ =>
       destruct (app_eq_nil _ _ (sym_eq H)); clear H; clarify
    | t : list _ |- _ => destruct t; simpl in *; clarify; [] end.
Qed.

Lemma traces_deter_cons: 
  forall a b l1 l2,
    te_samekind a b ->
    (a = b -> traces_deter l1 l2) ->
    traces_deter (a :: l1) (b :: l2).
Proof.
  intros; eapply (traces_deter_app (a :: nil) (b :: nil) l1 l2);
  intros; clarify; eauto using traces_deter_single.
Qed.

Section DETER.

Variables (ge : genv)
          (sp : option pointer)
          (env : env).

Let eval_expr_wf e :=
  forall t v (E : eval_expr ge sp env t e v), 
  forall te, In te t -> te_wf te.

Let eval_exprlist_wf e :=
  forall t v (E : eval_exprlist ge sp env t e v), 
  forall te, In te t -> te_wf te.

Let eval_condexpr_wf e :=
  forall t v (E : eval_condexpr ge sp env t e v), 
  forall te, In te t -> te_wf te.

Definition eval_expr_deter e :=
  forall t1 t2 v1 v2
         (E1 : eval_expr ge sp env t1 e v1)
         (E2 : eval_expr ge sp env t2 e v2),
  traces_deter t1 t2 /\
  forall (Et: t1 = t2), v1 = v2.

Definition eval_exprlist_deter e :=
  forall t1 t2 v1 v2
         (E1 : eval_exprlist ge sp env t1 e v1)
         (E2 : eval_exprlist ge sp env t2 e v2),
  traces_deter t1 t2 /\
  forall (Et: t1 = t2), v1 = v2.

Definition eval_condexpr_deter e :=
  forall t1 t2 v1 v2
         (E1 : eval_condexpr ge sp env t1 e v1)
         (E2 : eval_condexpr ge sp env t2 e v2),
  traces_deter t1 t2 /\
  forall (Et: t1 = t2), v1 = v2.


Ltac dtac N := 
 eapply (N eval_expr_deter eval_exprlist_deter eval_condexpr_deter); intros; red; 
 inversion 1; inversion 1; clarify';
 repeat 
   (match goal with
    | H : traces_deter ?l1 ?l2, H2: ?l1 ++ _ = ?l2 ++ _ |- _ =>
        eapply deter_eq in H2; des; clarify
    | H : eval_exprlist_deter ?e,
      E1: eval_exprlist ?ge ?sp ?env ?t1 ?e ?l1,
      E2: eval_exprlist ?ge ?sp ?env ?t2 ?e ?l2 |- _ =>
         destruct (H _ _ _ _ E1 E2); clear H
    | H : eval_condexpr_deter ?e,
      E1: eval_condexpr ?ge ?sp ?env ?t1 ?e ?l1,
      E2: eval_condexpr ?ge ?sp ?env ?t2 ?e ?l2 |- _ =>
         destruct (H _ _ _ _ E1 E2); clear H
    | H : eval_expr_deter ?e,
      E1: eval_expr ?ge ?sp ?env ?t1 ?e ?l1,
      E2: eval_expr ?ge ?sp ?env ?t2 ?e ?l2 |- _ =>
         destruct (H _ _ _ _ E1 E2); clear H
    | b : bool, H : context[if ?b then _ else _] |- _ => destruct b 
    | _ => try eapply traces_deter_app; try eapply traces_deter_single; intuition clarify'
    end).

Lemma deter_expr_traces: forall e, eval_expr_deter e.         Proof. dtac expr_ind3. Qed.
Lemma deter_exprlist_traces: forall e, eval_exprlist_deter e. Proof. dtac exprlist_ind3. Qed.
Lemma deter_condexpr_traces: forall e, eval_condexpr_deter e. Proof. dtac exprcond_ind3. Qed.

Ltac wf_tac N :=
  eapply (N eval_expr_wf
                    eval_exprlist_wf
                    eval_condexpr_wf); 
  intros; red; inversion 1; intros; clarify;
  repeat match goal with 
    | H: In _ (_ ++ _) |- _ => eapply in_app in H; destruct H
    | H: In _ (_ :: _) |- _ => inv H; clarify
    | H: In _ nil      |- _ => inv H; clarify
    | b: bool, H: context[if ?b then _ else _] |- _ => destruct b
  end; eauto.

Lemma wf_expr_traces: forall e, eval_expr_wf e.         Proof. wf_tac expr_ind3. Qed.
Lemma wf_exprlist_traces: forall e, eval_exprlist_wf e. Proof. wf_tac exprlist_ind3. Qed.
Lemma wf_condexpr_traces: forall e, eval_condexpr_wf e. Proof. wf_tac exprcond_ind3. Qed.

End DETER.    

Hint Resolve traces_deter_refl.

Ltac tac' := 
 inversion 1; inversion 1; clarify';
 repeat 
   (match goal with
    | H : traces_deter ?l1 ?l2, H2: ?l1 ++ _ = ?l2 ++ _ |- _ =>
        eapply deter_eq in H2; des; clarify
    | E1: eval_exprlist ?ge ?sp ?env ?t1 ?e ?l1,
      E2: eval_exprlist ?ge ?sp ?env ?t2 ?e ?l2 |- _ =>
         destruct (deter_exprlist_traces _ _ _ _ _ _ _ _ E1 E2); clear E1 E2
    | E1: eval_condexpr ?ge ?sp ?env ?t1 ?e ?l1,
      E2: eval_condexpr ?ge ?sp ?env ?t2 ?e ?l2 |- _ =>
         destruct (deter_condexpr_traces _ _ _ _ _ _ _ _ E1 E2); clear E1 E2
    | E1: eval_expr ?ge ?sp ?env ?t1 ?e ?l1,
      E2: eval_expr ?ge ?sp ?env ?t2 ?e ?l2 |- _ =>
         destruct (deter_expr_traces _ _ _ _ _ _ _ _ E1 E2); clear E1 E2
    | H' : ?a = ?b, H'' : ?a = ?c |- ?P => rewrite H' in H''; clarify
    | H' : Kcall _ _ _ _ _ = Kcall _ _ _ _ _ |- _ => inv H'; clarify
    | H : map val_of_eval ?x = map val_of_eval ?y |- _ => rewrite (map_val_of_eval_eq H); done
    | _ => try eapply traces_deter_app; try eapply traces_deter_single; intuition clarify'
    end).

Lemma step_deter:
  forall {ge s t1 t2 s1 s2}
         (E1 : step ge s t1 s1)
         (E2 : step ge s t2 s2),
  traces_deter t1 t2 /\
  forall (Et: t1 = t2), s1 = s2.
Proof.
  tac'; try (by inv ASME; inv ASME0).
Qed.

Lemma step_wf:
  forall {ge s t s'} (E : step ge s t s')
    te (X: In te t), te_wf te.
Proof.
  inversion 1; intros; clarify;
  repeat match goal with 
    | H: In _ (_ ++ _) |- _ => eapply in_app in H; destruct H
    | H: In _ (_ :: _) |- _ => inv H; clarify
    | H: In _ nil      |- _ => inv H; clarify
    | b: bool, H: context[if ?b then _ else _] |- _ => destruct b
  end; 
  try (eby eapply wf_expr_traces);
  try (eby eapply wf_exprlist_traces);
  try (eby eapply wf_condexpr_traces);
  try (by inv ASME).
- by destruct sp; simpl in *; destruct X; clarify.
- by destruct sp; simpl in *; destruct H; clarify.
- eby eapply (wf_expr_traces _ _ _ _ tfn).
Qed.

Lemma cms_determinate:
  forall ge s s' s'' l l',
    small_step_cs ge s l s' ->
    small_step_cs ge s l' s'' ->
    (te_samekind l l' /\ (l = l' -> s' = s'')).
Proof.
intros ge; eapply (small_step_determinate _ (step ge));
intros; try destruct (step_deter H H0); clarify; eauto.
- by specialize (H1 t _ _ (refl_equal _) (app_nil_end _)).
- by specialize (H1 t _ _ (refl_equal _) (refl_equal _)).
- eapply step_wf, in_app; try edone; vauto.
Qed.

Require Import Classical.

Lemma cms_progress_dec:
    forall ge s, (forall s' l', ~ small_step_cs ge s l' s') \/
      (exists l', exists s', small_step_cs ge s l' s').
Proof.
  intros; case (classic (exists l', exists s', small_step_cs ge s l' s')); eauto 7.
Qed.

Definition cms_sem : SEM := 
  mkSEM (small_step_state state) _ program 
  cms_ge_init (@prog_main _ _) (fun ge => Genv.find_symbol ge) 
  small_step_cs cms_init cms_progress_dec (fun ge => small_step_receptive _ (step ge)) cms_determinate.

End CminorSel_TSO.
