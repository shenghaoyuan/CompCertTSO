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

(** Abstract syntax and semantics for the Csharpminor language. *)

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Pointers.
Require Import Events.
Require Import Globalenvs.
Require Import Memcomp.
Require Import Mergesort.
Require Cminorops.
Require Import Libtactics.

Definition unary_operation := Cminorops.unary_operation.
Definition binary_operation := Cminorops.binary_operation.
Definition atomic_statement := Cminorops.atomic_statement.
Definition eval_unop := Cminorops.eval_unop.
Definition eval_binop := Cminorops.eval_binop.

(** Abstract syntax *)

(** Csharpminor is a low-level imperative language structured in expressions,
  statements, functions and programs.  Expressions include
  reading global or local variables, reading store locations,
  arithmetic operations, function calls, and conditional expressions
  (similar to [e1 ? e2 : e3] in C). 

  Unlike in Cminor (the next intermediate language of the back-end),
  Csharpminor local variables reside in memory, and their addresses can
  be taken using [Eaddrof] expressions.
*)

Inductive constant : Type :=
  | Ointconst: int -> constant          (**r integer constant *)
  | Ofloatconst: float -> constant.     (**r floating-point constant *)

Inductive expr : Type :=
  | Evar : ident -> expr                (**r reading a scalar variable  *)
  | Eaddrof : ident -> expr             (**r taking the address of a variable *)
  | Econst : constant -> expr           (**r constants *)
  | Eunop : unary_operation -> expr -> expr  (**r unary operation *)
  | Ebinop : binary_operation -> expr -> expr -> expr (**r binary operation *)
  | Eload : memory_chunk -> expr -> expr (**r memory read *)
  | Econdition : expr -> expr -> expr -> expr. (**r conditional expression *)

(** Statements include expression evaluation, variable assignment,
  memory stores, function calls, an if/then/else conditional,
  infinite loops, blocks and early block exits, and early function returns.
  [Sexit n] terminates prematurely the execution of the [n+1] enclosing
  [Sblock] statements, and thread creation. *)

Definition label := ident.

Inductive stmt : Type :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sstore : memory_chunk -> expr -> expr -> stmt
  | Scall : option ident -> signature -> expr -> list expr -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: expr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: expr -> lbl_stmt -> stmt
  | Sreturn: option expr -> stmt
  | Slabel: label -> stmt -> stmt
  | Sgoto: label -> stmt
  | Sthread_create : expr -> expr -> stmt
  | Satomic : option ident -> atomic_statement -> list expr -> stmt
  | Smfence : stmt
with lbl_stmt : Type :=
  | LSdefault: stmt -> lbl_stmt
  | LScase: int -> stmt -> lbl_stmt -> lbl_stmt.

(** The variables can be either scalar variables
  (whose type, size and signedness are given by a [memory_chunk]
  or array variables (of the indicated sizes).  The only operation
  permitted on an array variable is taking its address. *)

Inductive var_kind : Type :=
  | Vscalar: memory_chunk -> var_kind
  | Varray: Z -> var_kind.

(** Functions are composed of a signature, a list of parameter names
  with associated memory chunks (parameters must be scalar), a list of
  local variables with associated [var_kind] description, and a
  statement representing the function body.  *)

Record function : Type := mkfunction {
  fn_sig: signature;
  fn_params: list (ident * memory_chunk);
  fn_vars: list (ident * var_kind);
  fn_body: stmt
}.


Definition fundef := Ast.fundef function.

Definition program : Type := Ast.program fundef var_kind.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.



(** * Operational semantics *)

(** Three kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [gvarenv]: map global variables to variable informations (type [var_kind]);
- [env]: local environments, map local variables 
    to memory blocks and variable informations.
*)

Definition sizeof (lv: var_kind) : Z :=
  match lv with
  | Vscalar chunk => size_chunk chunk
  | Varray sz => Zmax 1 sz
  end.

Definition fn_variables (f: function) :=
  List.map
    (fun id_chunk => (fst id_chunk, Vscalar (snd id_chunk))) f.(fn_params)
  ++ f.(fn_vars).

Definition fn_params_names (f: function) :=
  List.map (@fst ident memory_chunk) f.(fn_params).

Definition fn_vars_names (f: function) :=
  List.map (@fst ident var_kind) f.(fn_vars).


Section RELSEM.

Definition genv := Genv.t fundef.

Definition gvarenv := PTree.t var_kind.
Definition env := PTree.t (pointer * var_kind).
Definition empty_env : env := PTree.empty (pointer * var_kind).


(** Continuations *)

Inductive cont: Type :=
  | Kstop: cont                         (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kblock: cont -> cont                (**r exit a block, then do cont *)
  | Kcall: option ident -> fundef -> env -> cont -> cont (**r return to caller *)
  | Kfree: list pointer -> option val -> cont -> cont.

Inductive expr_cont : Type :=
  | EKunop : unary_operation ->  expr_cont -> expr_cont
  | EKbinop1 : binary_operation -> expr -> expr_cont -> expr_cont
  | EKbinop2 : binary_operation -> val -> expr_cont -> expr_cont
  | EKload : memory_chunk -> expr_cont -> expr_cont
  | EKcall : option ident -> signature -> list expr -> cont -> expr_cont
  | EKargs : option ident -> val -> signature -> list expr -> list val -> cont -> expr_cont
  | EKatargs : option ident -> atomic_statement -> list expr -> list val -> cont -> expr_cont
  | EKcond : expr -> expr -> expr_cont -> expr_cont
  | EKassign : ident -> cont -> expr_cont
  | EKthread1 : expr -> cont -> expr_cont
  | EKthread2 : pointer -> cont -> expr_cont
  | EKcondstmt : stmt -> stmt -> cont -> expr_cont
  | EKswitch: lbl_stmt -> cont -> expr_cont
  | EKreturn: cont -> expr_cont
  | EKstoreaddr: memory_chunk -> expr -> cont -> expr_cont
  | EKstoreval: memory_chunk -> val -> cont -> expr_cont.

Inductive state : Type :=
  | SKexpr : expr -> env -> expr_cont -> state
  | SKval : val -> env -> expr_cont -> state
  | SKstmt : stmt -> env -> cont -> state 
  | SKcall : list val -> cont -> state
  | SKbind: function -> list val -> list ident ->  env -> cont -> state
  | SKalloc: list val ->  (list (ident * var_kind)) ->  env -> cont -> state
  | SKexternal: signature -> option ident -> env -> cont -> state
  | SKexternalReturn: option ident -> val -> env -> cont -> state.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kblock k => call_cont k
  | Kfree ps v k =>  call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ => True
  | _ => False
  end.

Definition get_fundef (k: cont) : option fundef :=
  match k with
   | Kcall op fd e k => (Some fd)
   | _ => None
  end.

(** Resolve [switch] statements. *)

Fixpoint select_switch (n: int) (sl: lbl_stmt) {struct sl} : lbl_stmt :=
  match sl with
  | LSdefault _ => sl
  | LScase c s sl' => if Int.eq c n then sl else select_switch n sl'
  end.

Fixpoint seq_of_lbl_stmt (sl: lbl_stmt) : stmt :=
  match sl with
  | LSdefault s => s
  | LScase c s sl' => Sseq s (seq_of_lbl_stmt sl')
  end.

(** Find the statement and manufacture the continuation 
  corresponding to a label *)

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
  | Sswitch a sl =>
      find_label_ls lbl sl k
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end

with find_label_ls (lbl: label) (sl: lbl_stmt) (k: cont) 
                   {struct sl}: option (stmt * cont) :=
  match sl with
  | LSdefault s => find_label lbl s k
  | LScase _ s sl' =>
      match find_label lbl s (Kseq (seq_of_lbl_stmt sl') k) with
      | Some sk => Some sk
      | None => find_label_ls lbl sl' k
      end
  end.

(** Evaluation of operator applications. *)

Definition eval_constant (cst: constant) : option val :=
  match cst with
  | Ointconst n => Some (Vint n)
  | Ofloatconst n => Some (Vfloat n)
  end.

(** List of pointers mentioned in an environment *)

Definition pointers_of_env (e:env) : list pointer :=
  List.map (fun id_b_lv => match id_b_lv with (id, (b, lv)) => b end)
           (PTree.elements e).


Definition sorted_pointers_of_env (e:env) : list pointer :=
 let (l,_) := mergesort _ 
                (fun x y => Ple (fst x) (fst y)) 
                (fun x y z => Ple_trans (fst x) (fst y) (fst z)) 
                (fun x y => Ple_total (fst x) (fst y))
                (fun x y => ple (fst x) (fst y))
                (PTree.elements e)
 in List.map (fun idpk => fst (snd idpk)) l.

(** Initialization of local variables that are parameters.  The value
  of the corresponding argument is stored into the memory block
  bound to the parameter. *)


Variable globenv : genv * gvarenv.
Definition ge : genv := fst globenv.
Definition gvare : gvarenv := snd globenv.

(* Evaluation of the address of a variable: 
   [eval_var_addr prg ge e id b] states that variable [id] 
   in environment [e] evaluates to block [b]. *)

Inductive eval_var_addr: env -> ident -> pointer -> Prop :=
  | eval_var_addr_local:
      forall e id p vi,
      PTree.get id e = Some (p, vi) ->
      eval_var_addr e id p
  | eval_var_addr_global:
      forall e id p,
      PTree.get id e = None ->
      Genv.find_symbol ge id = Some p ->
      eval_var_addr e id p.

(* Evaluation of a reference to a scalar variable:
   [eval_var_ref prg ge e id b chunk] states
   that variable [id] in environment [e] evaluates to pointer [p]
   and is associated with the memory chunk [chunk]. *)

Inductive eval_var_ref: env -> ident -> pointer -> memory_chunk -> Prop :=
  | eval_var_ref_local:
      forall e id p chunk,
      PTree.get id e = Some (p, Vscalar chunk) ->
      eval_var_ref e id p chunk
  | eval_var_ref_global:
      forall e id p chunk,
      PTree.get id e = None ->
      Genv.find_symbol ge id = Some p ->
      PTree.get id gvare = Some (Vscalar chunk) ->
      eval_var_ref e id p chunk.

Inductive cs_step : state -> thread_event -> state -> Prop :=
(* Var *)
| StepVar:
  forall id p chunk v env k,
  eval_var_ref env id p chunk ->
  Val.has_type v (type_of_chunk chunk) ->
  cs_step (SKexpr (Evar id) env k)
          (TEmem (MEread p chunk v))
          (SKval v env k)
(* Addrof *)
| StepAddrOf:
  forall id p env k,
  eval_var_addr env id p ->
  cs_step (SKexpr (Eaddrof id) env k)
          TEtau
          (SKval (Vptr p) env k)
(* Const *)
| StepConst:
  forall cst v env k,
  eval_constant cst = Some v ->
  cs_step (SKexpr (Econst cst) env k)
          TEtau
          (SKval v env k)
(* Unop *)
| StepUnop1:
  forall op e k env,
  cs_step (SKexpr (Eunop op e) env k)
          TEtau
          (SKexpr e env (EKunop op k))
| StepUnop:
  forall v v' op k env,
  eval_unop op v = Some v' ->
  cs_step (SKval v env (EKunop op k))
          TEtau
          (SKval v' env k)
(* Binop *)
| StepBinop1:
  forall op e1 e2 env k,
  cs_step (SKexpr (Ebinop op e1 e2) env k)
          TEtau
          (SKexpr e1 env (EKbinop1 op e2 k))
| StepBinop2:
  forall op v e2 env k,
  cs_step (SKval v env (EKbinop1 op e2 k))
          TEtau
          (SKexpr e2 env (EKbinop2 op v k))
| StepBinop:
  forall op v v1 v2 env k,
  eval_binop op v1 v2 = Some v -> 
  cs_step (SKval v2 env (EKbinop2 op v1 k))
          TEtau
          (SKval v env k)
(* Load *)
| StepLoad1:
  forall c e env k,
  cs_step (SKexpr (Eload c e) env k)
          TEtau
          (SKexpr e env (EKload c k))
| StepLoad:
  forall p v c env k,
  Val.has_type v (type_of_chunk c) ->
  cs_step (SKval (Vptr p) env (EKload c k))
          (TEmem (MEread p c v))
          (SKval v env k)
(* Conditional *)
| StepIfThenElse:
  forall e1 e2 e3 k env,
  cs_step (SKexpr (Econdition e1 e2 e3) env k)
          TEtau
          (SKexpr e1 env (EKcond e2 e3 k)) 
| StepIfThenElseTrue:
  forall v e1 e2 k env,
  (Val.bool_of_val v true) ->
  cs_step (SKval v env (EKcond e1 e2 k))
       TEtau
       (SKexpr e1 env k)
| StepIfThenElseFalse:
  forall v e1 e2 k env,
  (Val.bool_of_val v false) ->
  cs_step (SKval v env (EKcond e1 e2 k))
          TEtau
          (SKexpr e2 env k)
(* Skip *)
| StepSkipBlock:
  forall k env,
  cs_step (SKstmt Sskip env (Kblock k))
          TEtau
          (SKstmt Sskip env k)
(* Assign *)
| StepAssign1:
  forall id e env k,
  cs_step (SKstmt (Sassign id e) env k)
          TEtau
          (SKexpr e env (EKassign id k))
| StepAssign:
  forall v id p chunk env k,
  eval_var_ref env id p chunk ->
  cs_step (SKval v env (EKassign id k))
          (TEmem (MEwrite p chunk (cast_value_to_chunk chunk v)))
          (SKstmt Sskip env k)
(* Store *)
| StepStore1:
  forall chunk e1 e2 env k,
  cs_step (SKstmt (Sstore chunk e1 e2) env k)
          TEtau
          (SKexpr e1 env (EKstoreaddr chunk e2 k))
| StepStore2:
  forall ptr chunk e2 env k,
  cs_step (SKval ptr env (EKstoreaddr chunk e2 k))
          TEtau
          (SKexpr e2 env (EKstoreval chunk ptr k))
| StepStore:
  forall v chunk ptr env k,
  cs_step (SKval v env (EKstoreval chunk (Vptr ptr) k))
          (TEmem (MEwrite ptr chunk (cast_value_to_chunk chunk v)))
          (SKstmt Sskip env k)
(* Call *)
| StepCall:
  forall optid sig e args env k,
  cs_step (SKstmt (Scall optid sig e args) env k)
          TEtau
          (SKexpr e env (EKcall optid sig args k))
| StepEmptyCall:
  forall vf fd sig optid env k,
  Genv.find_funct ge vf = Some fd ->
  funsig fd = sig -> 
  cs_step (SKval vf env (EKcall optid sig nil k))
          TEtau
          (SKcall nil (Kcall optid fd env k))
| StepCallArgs1:
  forall vf optid sig arg1 args env k,
  cs_step (SKval vf env (EKcall optid sig (arg1 :: args) k))
          TEtau
          (SKexpr arg1 env (EKargs optid vf sig args nil k))
| StepCallArgs2:
  forall v vs vf sig optid arg1 args env k,
  cs_step (SKval v env (EKargs optid vf sig (arg1 :: args) vs k))
          TEtau
          (SKexpr arg1 env (EKargs optid vf sig args (List.app vs (v::nil)) k))
| StepCallArgs:
  forall v vs vf sig fd optid env k,
  Genv.find_funct ge vf = Some fd ->  
  funsig fd = sig -> 
  cs_step (SKval v env (EKargs optid vf sig nil vs k))
          TEtau
          (SKcall (List.app vs (v :: nil)) (Kcall optid fd env k))
 (* Atomics *)
 | StepAtomic : forall optid astmt e es k env,
   cs_step (SKstmt (Satomic optid astmt  (e :: es)) env k)  
           TEtau
           (SKexpr e env  (EKatargs optid astmt es nil k )  )
 | StepAtomicArgs : forall v optid astmt vs e es k env,
   cs_step (SKval v env  (EKatargs optid astmt (e :: es) vs  k))  
           TEtau
           (SKexpr e env  (EKatargs optid astmt es (vs ++ v :: nil) k)) 
 | StepAtomicFinishNone : forall v astmt vs k env p v' rmwi,
   Cminorops.sem_atomic_statement astmt ( vs ++ v :: nil ) = Some (p, rmwi)  ->
   Val.has_type v' (type_of_chunk Mint32)  ->
   cs_step  (SKval v env  (EKatargs  None  astmt nil vs k))  
            (TEmem  (MErmw p Mint32 v' rmwi))  
            (SKstmt Sskip env k)
 | StepAtomicFinishSome : forall v id astmt vs k env p v' rmwi,
   Cminorops.sem_atomic_statement astmt ( vs ++ v :: nil ) = Some (p, rmwi)  ->
   Val.has_type v' (type_of_chunk Mint32)  ->
   cs_step  (SKval v env  (EKatargs  (Some id)  astmt nil vs k))  
            (TEmem  (MErmw p Mint32 v' rmwi))  
            (SKval v' env (EKassign id k) )
 | StepFence : forall k env,
   cs_step (SKstmt Smfence env k)  
           (TEmem MEfence)
           (SKstmt Sskip env k)
(* Seq *)
| StepSeq:
  forall s1 s2 env k,
  cs_step (SKstmt (Sseq s1 s2) env k)
          TEtau
          (SKstmt s1 env (Kseq s2 k))
(* Conditional Statement *)
| StepCond:
  forall e s1 s2 env k,
  cs_step (SKstmt (Sifthenelse e s1 s2) env k)
          TEtau
          (SKexpr e env (EKcondstmt s1 s2 k))
| StepCondTrue:
  forall v s1 s2 env k,
  (Val.bool_of_val v true) ->
  cs_step (SKval v env (EKcondstmt s1 s2 k))
          TEtau
          (SKstmt s1 env k) 
| StepCondFalse:
  forall v s1 s2 env k,
  (Val.bool_of_val v  false) ->
  cs_step (SKval v env (EKcondstmt s1 s2 k))
          TEtau
          (SKstmt s2 env k) 
(* Loop *)
| StepLoop:
  forall s env k,
  cs_step (SKstmt (Sloop s) env k)
          TEtau
          (SKstmt s env (Kseq (Sloop s) k)) 
(* Block *)
| StepBlock:
  forall s env k,
  cs_step (SKstmt (Sblock s) env k)
          TEtau
          (SKstmt s env (Kblock k))
(* Exit *)
| StepExitSeq:
  forall n s k env,
  cs_step (SKstmt (Sexit n) env (Kseq s k))
          TEtau
          (SKstmt (Sexit n) env k)
| StepExitBlock:
  forall env k,
  cs_step (SKstmt (Sexit 0) env (Kblock k))
          TEtau
          (SKstmt Sskip env k)
| StepExitBlock1:
  forall n env k,
  cs_step (SKstmt (Sexit (S n)) env (Kblock k))
          TEtau
          (SKstmt (Sexit n) env k)
(* Switch *)
| StepSwitch:
  forall e cases env k,
  cs_step (SKstmt (Sswitch e cases) env k)
          TEtau
          (SKexpr e env (EKswitch cases k))
(* Select *)
| StepSelect:
  forall n cases env k,
  cs_step (SKval (Vint n) env (EKswitch cases k))
          TEtau
          (SKstmt (seq_of_lbl_stmt (select_switch n cases)) env k)
(* Label *)
| StepLabel:
  forall lbl s env k,
  cs_step (SKstmt (Slabel lbl s) env k)
          TEtau
          (SKstmt s env k)
(* Goto *)
| StepGoto:
  forall f lbl k s' k' k'' env env' opt,
  call_cont k = (Kcall opt (Internal f) env' k') ->
  find_label lbl f.(fn_body) (call_cont k) = Some (s', k'') ->
  cs_step (SKstmt (Sgoto lbl) env k)
          TEtau
          (SKstmt s' env k'')
(* Return *)
| StepReturnNone:
   forall f k env env' k',
   call_cont k = (Kcall None (Internal f) env' k') ->
   f.(fn_sig).(sig_res) = None ->
   cs_step (SKstmt (Sreturn None) env k)
           TEtau
           (SKstmt Sskip env (Kfree (sorted_pointers_of_env env) None k))
| StepReturnNoneFinish:
  forall env env' k' k fd opt_v,
  call_cont k = (Kcall None fd env' k') ->
  cs_step (SKstmt Sskip env (Kfree nil opt_v k))
          TEtau
          (SKstmt Sskip env' k')
| StepReturnSome:
  forall e f k env,
  get_fundef (call_cont k) = Some (Internal f) ->
  f.(fn_sig).(sig_res) <> None ->
  cs_step (SKstmt (Sreturn (Some e)) env k)
          TEtau
          (SKexpr e env (EKreturn k))
| StepReturnSome1:
  forall v k env pl,
  pl = sorted_pointers_of_env env ->
  cs_step (SKval v env (EKreturn k))
          TEtau
          (SKstmt Sskip env (Kfree pl (Some v) k))
| StepReturnSomeFinish:
  forall v c fd p id k k' env env',
  call_cont k = (Kcall (Some id) fd env' k') ->
  eval_var_ref env' id p c -> 
  cs_step (SKstmt Sskip env (Kfree nil (Some v) k))
          (TEmem (MEwrite p c (cast_value_to_chunk c v)))
          (SKstmt Sskip env' k')
(* Internal Call *)  (* List.map (@fst ident var_kind) (fn_variables f)) *)
| StepFunctionInternal:
  forall optid f vs k env ck,
  ck  = (Kcall optid (Internal f) env k) ->
  NoDup ((fn_params_names f) ++ (fn_vars_names f)) ->
  cs_step (SKcall vs ck)
          TEtau
          (SKalloc vs (fn_variables f) empty_env ck)
| StepAllocLocal:
  forall id p vs vi args k env optid env' f,
  cs_step (SKalloc vs ((id,vi) :: args) env 
                         (Kcall optid (Internal f) env' k))
          (TEmem (MEalloc p (Int.repr(sizeof vi)) MObjStack))
          (SKalloc vs args (PTree.set id (p,vi) env) 
              (Kcall optid (Internal f) env' k))
| StepBindArgsStart:
  forall f vs env env' opt k,
  cs_step (SKalloc vs nil env (Kcall opt (Internal f) env' k))
          TEtau
          (SKbind f vs (map (@fst _ _) f.(fn_params)) env 
                  (Kcall opt (Internal f) env' k))
| StepBindArgs:
  forall f id args p env v c vs k ,
  (PTree.get id env) = Some (p,(Vscalar c)) ->
  cs_step (SKbind f (v::vs) (id::args) env k)
          (TEmem (MEwrite p c (cast_value_to_chunk c v)))
          (SKbind f vs args env k)
| StepTransferFun:
  forall f k env,
  cs_step (SKbind f nil nil env k)
          TEtau
          (SKstmt f.(fn_body) env k)
(* External *)
| StepExternalCall:
  forall k ef vargs evargs tgt env,
  (* event_match ef vargs t vres -> *)
  vargs = map val_of_eval evargs ->
  cs_step (SKcall vargs (Kcall tgt (External ef) env k))
          (TEext (Ecall ef.(ef_id) evargs))
          (SKexternal ef.(ef_sig) tgt env k)
| StepExternalReturn:
  forall efsig tgt vres evres env k typ,
  typ = (match sig_res efsig with Some x => x | None => Tint end) ->
  Val.has_type vres typ ->
  vres = val_of_eval evres ->
  cs_step (SKexternal efsig tgt env k)
          (TEext (Ereturn typ evres))
          (SKexternalReturn tgt vres env k)
| StepExternalStoreSome:
  forall vres env c p k tgt,
  eval_var_ref env tgt p c ->
  cs_step (SKexternalReturn (Some tgt) vres env k)
          (TEmem (MEwrite p c (cast_value_to_chunk c vres)))
          (SKstmt Sskip env k)
| StepExternalStoreNone:
  forall vres env k,
  cs_step (SKexternalReturn None vres env k)
          TEtau
          (SKstmt Sskip env k)
(* Continuation Management *)
| StepNext:
  forall s k env,
  cs_step (SKstmt Sskip env (Kseq s k))
          TEtau
          (SKstmt s env k)
| StepFree:
  forall p ps k env opt_v,
  cs_step (SKstmt Sskip env (Kfree (p :: ps) opt_v k))
          (TEmem (MEfree p MObjStack))
          (SKstmt Sskip env (Kfree ps opt_v k))
| StepStop:
  forall env,
  cs_step (SKstmt Sskip env Kstop)
          TEexit
         (SKstmt Sskip env Kstop)
(* Thread *)
| StepThread : 
  forall efn earg k env,
  cs_step (SKstmt (Sthread_create efn earg) env k)
          TEtau
          (SKexpr efn env (EKthread1 earg k))
| StepThreadFn:
  forall earg p k env,
  cs_step (SKval (Vptr p) env (EKthread1 earg k))
          TEtau
          (SKexpr earg env (EKthread2 p k))
| StepThreadEvt : 
  forall p v k env,
  cs_step (SKval v env (EKthread2 p k))
          (TEstart p (v::nil))
          (SKstmt Sskip env k).

Definition cs_init  (p : pointer) (vs : list val) : option state :=
  match Genv.find_funct_ptr ge p with
   | Some (Internal f)  => 
       if beq_nat (length vs) (length f.(fn_sig).(sig_args))
         then Some (SKcall (Val.conv_list vs f.(fn_sig).(sig_args))
                           (Kcall None (Internal f) empty_env Kstop))
         else None
   | _ => None
  end.

End RELSEM.

Tactic Notation "cs_step_cases" tactic(first) tactic(c) :=
    first; [
      c "StepVar" |
      c "StepAddrOf" |
      c "StepConst" |
      c "StepUnop1" |
      c "StepUnop" |
      c "StepBinop1" |
      c "StepBinop2" |
      c "StepBinop" |
      c "StepLoad1" |
      c "StepLoad" |
      c "StepIfThenElse" |
      c "StepIfThenElseTrue" |
      c "StepIfThenElseFalse" |
      c "StepSkipBlock" |
      c "StepAssign1" |
      c "StepAssign" |
      c "StepStore1" |
      c "StepStore2" |
      c "StepStore" |
      c "StepCall" |
      c "StepEmptyCall" |
      c "StepCallArgs1" |
      c "StepCallArgs2" |
      c "StepCallArgs" |
      c "StepAtomic" |
      c "StepAtomicArgs" |
      c "StepAtomicFinishNone" |
      c "StepAtomicFinishSome" |
      c "StepFence" |
      c "StepSeq" |
      c "StepCond" |
      c "StepCondTrue" |
      c "StepCondFalse" |
      c "StepLoop" |
      c "StepBlock" |
      c "StepExitSeq" |
      c "StepExitBlock" |
      c "StepExitBlock1" |
      c "StepSwitch" |
      c "StepSelect" |
      c "StepLabel" |
      c "StepGoto" |
      c "StepReturnNone" |
      c "StepReturnNoneFinish" |
      c "StepReturnSome" |
      c "StepReturnSome1" |
      c "StepReturnSomeFinish" |
      c "StepFunctionInternal" |
      c "StepAllocLocal" |
      c "StepBindArgsStart" |
      c "StepBindArgs" |
      c "StepTransferFun" |
      c "StepExternalCall" |
      c "StepExternalReturn" |
      c "StepExternalStoreSome" |
      c "StepExternalStoreNone" |
      c "StepNext" |
      c "StepFree" |
      c "StepStop" |
      c "StepThread" |
      c "StepThreadFn" |
      c "StepThreadEvt"].

Definition global_var_env (p: program): gvarenv :=
  List.fold_left
    (fun gve x => match x with (id, init, k) => PTree.set id k gve end)
    p.(prog_vars) (PTree.empty var_kind).

Definition cs_ge_init (p : program) (ge : genv * gvarenv) (m : Mem.mem) := 
  Genv.globalenv_initmem p (fst ge) no_mem_restr m /\ snd ge = global_var_env p.

(** * TSO machine set up *)

Section Cshp_TSO.

Lemma cs_receptive :
  forall ge l l' s s', 
    cs_step ge s l s' -> 
    te_samekind l' l ->
    exists s'', cs_step ge s l' s''.
Proof. 
  intros g l l' s s' Step Te_Samekind. 
  (cs_step_cases (inversion Step) Case);
     subst;
     destruct l'; try destruct ev;
     simpl in *;
     try done;
     try rewrite Te_Samekind; 
     try (decompose [and] Te_Samekind; subst);
     econstructor;
     try (by econstructor; eauto);
     try apply StepVar;
     try edone;
     eby econstructor; try (eby apply H1).  
Qed.

Ltac rewrite_right_aux_tac :=
  match goal with
    | H' : ?a = ?b, H'' : ?a = ?c |- ?P => 
      rewrite H' in H''; (discriminate || (inversion H''; subst; auto))
  end.

Lemma eval_var_ref_det:
  forall g e id c p c' p',
    eval_var_ref g e id c p ->
    eval_var_ref g e id c' p' ->
    c' = c /\ p' = p.
Proof.
  intros g e id c p c' p' EV1 EV2.
  destruct EV1; inv EV2; repeat rewrite_right_aux_tac.
Qed.

Lemma eval_var_addr_det:
  forall g e id p p',
    eval_var_addr g e id p ->
    eval_var_addr g e id p' ->
    p' = p.
Proof.
  intros g e id p p' EV1 EV2.
  destruct EV1; inv EV2; repeat rewrite_right_aux_tac.
Qed.

Lemma bool_of_val_contr:
  forall v,
    Val.bool_of_val v true -> Val.bool_of_val v false -> False.
Proof.
  intros v BVT BVF.
  inversion BVT; inversion BVF as [ | EQ |]; subst; try done. inv EQ. done.
Qed.

Ltac determinate_aux_tac :=
  repeat match goal with
    | H' : eval_var_ref ?g ?e ?id _ _,
      H'': eval_var_ref ?g ?e ?id _ _ |- ?P =>
        destruct (eval_var_ref_det _ _ _ _ _ _ _ H' H''); subst; done
    | H' : eval_var_addr ?g ?e ?id _,
      H'': eval_var_addr ?g ?e ?id _ |- ?P =>
        rewrite (eval_var_addr_det _ _ _ _ _ H' H'') in *; done
    | H' : Val.bool_of_val ?v true,
      H'' : Val.bool_of_val ?v false |- ?P =>
        pose proof (bool_of_val_contr _ H' H''); contradiction
    | H' : ?a = ?b, H'' : ?a = ?c |- ?P => 
      rewrite H' in H''; (discriminate || (inversion H''; subst; auto))
    | H' : Vscalar ?a = Vscalar ?b |- ?P => (inv H'; auto)
    | H' : Kcall _ _ _ _ = Kcall _ _ _ _ |- ?P => inv H'; done
    | H : map val_of_eval ?x = map val_of_eval ?y |- _ => 
        rewrite (map_val_of_eval_eq H); done
  end.

Lemma cs_determinate:
  forall ge s s' s'' l l',
    cs_step ge s l s' ->
    cs_step ge s l' s'' ->
    (te_samekind l l' /\ (l = l' -> s' = s'')).
Proof.
  intros g s s' s'' l l' ST1 ST2; split.
  by  destruct ST1; inv ST2; simpl; try done; determinate_aux_tac.
  intro; subst; destruct ST1; inversion ST2; subst; try done; determinate_aux_tac.
Qed.  

Require Import Classical.

Lemma cs_progress_dec:
    forall ge s, (forall s' l', ~ cs_step ge s l' s') \/
      (exists l', exists s', cs_step ge s l' s').
Proof.
  intros g s.
  set (P := exists l' : thread_event, exists s' : state, cs_step g s l' s').
  destruct (classic P). auto. 
  left. intros s' l'. revert s'. apply not_ex_all_not. 
  revert l'. apply not_ex_all_not. auto.
Qed.

Definition cs_sem : SEM := 
  mkSEM state (genv * gvarenv)%type program 
  cs_ge_init (@prog_main _ _) (fun ge => Genv.find_symbol (fst ge)) 
  cs_step cs_init cs_progress_dec cs_receptive cs_determinate.


End Cshp_TSO.
