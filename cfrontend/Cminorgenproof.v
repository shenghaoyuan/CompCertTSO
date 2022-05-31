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

(** Correctness proof for Cminor generation. *)

Require Import FSets.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Floats.
Require Import Pointers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Csharpminor.
Require Import Cstacked.
Require Import Op.
Require Import Cminor.
Require Import Cminorops.
Require Import Cminorgen.
Require Import Simulations.
Require Import TSOmachine.
Require Import TSOsimulation.
Require Import Memcomp Traces.
Require Import Libtactics.
Require Import Switch.

Open Local Scope error_monad_scope.

Section TRANSLATION.

Variable prog: Csharpminor.program.

Let gce := build_global_compilenv prog.
Let gvare : gvarenv := global_var_env prog.

(* Hypothesis TRANSL: transl_program prog = OK tprog. *)
Variable ge : Cstacked.genv.
Variable tge : Cminor.genv.
Definition genv_rel :=
  Genv.genv_match (fun a b => transl_fundef gce a = OK b) tge ge.
Hypothesis TRANSF: genv_rel.
Hypothesis FINDS: 
  forall id, In id (map (fun x => fst (fst x)) (prog_vars prog)) -> 
             Genv.find_symbol ge id <> None.
                         

(** ** Simulation relations *)

(** Consistency of Cstacked environment with compilenv and Cminor env *)
Inductive match_env_item : ident ->           (* var name *)
                           var_info ->        (* var stack kind in compilenv *)
                           option env_item -> (* var stack kind in Cstacked *)
                           option val ->      (* var value in Cminor *)
                           option pointer ->  (* stack pointer *)
                           Prop :=
  | match_env_item_local: forall id c v v' anysp
      (LD : Val.lessdef v v'),
      match_env_item id    (Var_local c)
                           (Some (Env_local v c))
                           (Some v')
                           anysp
  | match_env_item_scalar: forall id c ofs anyv anyp,
      match_env_item id    (Var_stack_scalar c ofs)
                           (Some (Env_stack_scalar c ofs))
                           anyv (Some anyp)
  | match_env_item_array: forall id n anyv anyp,
      match_env_item id    (Var_stack_array n)
                           (Some (Env_stack_array n))
                           anyv (Some anyp)
  | match_env_item_global_scalar: forall id c anyv anysp p
      (GVE :  gvare ! id = Some (Vscalar c))
      (GVP :  Genv.find_symbol ge id = Some p),
      match_env_item id (Var_global_scalar c) None anyv anysp
  | match_env_item_global_array: forall id anyv anysp
      (GVE :  match gvare ! id with 
                | Some (Vscalar c) => False  
                | _ => True 
              end),
      match_env_item id Var_global_array None anyv anysp.

Tactic Notation "match_env_item_cases" tactic(first) tactic(c) :=
    first; [
      c "match_env_item_local" |
      c "match_env_item_scalar" |
      c "match_env_item_array" |
      c "match_env_item_global_scalar" |
      c "match_env_item_global_array"].

(** Environments are related if they agree on values *)

Definition match_env (cenv : compilenv)
                     (senv : Cstacked.env)
                     (tenv : Cminor.env) : Prop :=
  
  forall i, match_env_item i
                           (cenv !! i) 
                           (senv.(csenv_env) ! i) 
                           (tenv ! i)
                           senv.(csenv_sp).

Definition match_env_except (cenv : compilenv)
                            (senv : Cstacked.env)
                            (tenv : Cminor.env) 
                            (eid  : list ident) : Prop :=
  forall i, match_env_item i
                           (cenv !! i) 
                           (senv.(csenv_env) ! i) 
                           (tenv ! i)
                           senv.(csenv_sp) \/
            In i eid.

Definition get_cenv (k : Cstacked.cont) :=
  match Cstacked.call_cont k with
    | Cstacked.Kcall _ (Internal fd) _ _ => fst (build_compilenv gce fd)
    | _ => gce
  end.

Fixpoint get_cenv_ek (k : Cstacked.expr_cont) :=
  match k with
    | Cstacked.EKunop _ ek       => get_cenv_ek ek
    | Cstacked.EKbinop1 _ _ ek   => get_cenv_ek ek
    | Cstacked.EKbinop2 _ _ ek   => get_cenv_ek ek
    | Cstacked.EKload _ ek       => get_cenv_ek ek
    | Cstacked.EKcall _ _ _ k'   => get_cenv k'
    | Cstacked.EKargs _ _ _ _ _ k' => get_cenv k'
    | Cstacked.EKatargs _ _ _ _ k' => get_cenv k'
    | Cstacked.EKcond _ _ ek     => get_cenv_ek ek
    | Cstacked.EKassign _ k'     => get_cenv k'
    | Cstacked.EKthread1 _ k'    => get_cenv k'
    | Cstacked.EKthread2 _ k'    => get_cenv k'
    | Cstacked.EKcondstmt _ _ k' => get_cenv k'
    | Cstacked.EKswitch _ k'     => get_cenv k'
    | Cstacked.EKreturn k'       => get_cenv k'
    | Cstacked.EKstoreaddr _ _ k' => get_cenv k'
    | Cstacked.EKstoreval _ _ k' => get_cenv k'
  end.

Definition make_cast_cont (chunk: memory_chunk) (ek: expr_cont) : expr_cont :=
  match chunk with
  | Mint8signed => EKunop Ocast8signed ek
  | Mint8unsigned => EKunop Ocast8unsigned ek
  | Mint16signed => EKunop Ocast16signed ek
  | Mint16unsigned => EKunop Ocast16unsigned ek
  | Mint32 => ek
  | Mfloat32 => EKunop Osingleoffloat ek
  | Mfloat64 => ek
  end.

(** Continuation relation. *)
Inductive match_cont : Cstacked.cont -> 
                       Cminor.cont -> 
                       exit_env -> 
                       Prop :=
  | match_Kstop: forall xenv,
    match_cont Cstacked.Kstop 
               Cminor.Kstop
               xenv
  | match_Kseq: forall xenv s ts sk tk
      (TS : transl_stmt (get_cenv sk) xenv s = OK ts)
      (MK : match_cont sk tk xenv),
      match_cont (Cstacked.Kseq s sk)
                 (Cminor.Kseq ts tk)
                 xenv
  | match_Kseq2: forall s1 s2 sk ts1 tk xenv
      (TS : transl_stmt (get_cenv sk) xenv s1 = OK ts1)
      (MK : match_cont (Cstacked.Kseq s2 sk) tk xenv),
      match_cont (Cstacked.Kseq (Csharpminor.Sseq s1 s2) sk)
                 (Cminor.Kseq ts1 tk)  
                 xenv
  | match_Kblock: forall sk tk xenv
      (MK : match_cont sk tk xenv),
      match_cont (Cstacked.Kblock sk) 
                 (Cminor.Kblock tk) 
                 (true :: xenv)
  | match_Kblock2: forall sk tk xenv
      (MK : match_cont sk tk xenv),
      match_cont sk 
                 (Cminor.Kblock tk) 
                 (false :: xenv)
  | match_Kcall_none: forall fn e sk tfn te tk cenv xenv sz
      (Ecenv : cenv = fst (build_compilenv gce fn))
      (TB : transl_funbody cenv sz fn = OK tfn)
      (MK : match_cont sk tk xenv)
      (ME : match_env (get_cenv sk) e te),
      match_cont (Cstacked.Kcall None (Internal fn)  e sk)
                 (Cminor.Kcall   None (Internal tfn) e.(csenv_sp) te tk)
                 nil
  | match_Kcall_some: forall id fn e sk tfn s te tk cenv xenv sz
      (Ecenv : cenv = fst (build_compilenv gce fn))
      (TB : transl_funbody cenv sz fn = OK tfn)
      (VS : Cminorgen.var_set (get_cenv sk) id (Evar id) = OK s)
      (ME : match_env (get_cenv sk) e te)
      (MK : match_cont sk tk xenv),
      match_cont (Cstacked.Kcall (Some id) (Internal fn) e sk)
                 (Cminor.Kcall (Some id) (Internal tfn) e.(csenv_sp) 
                               te (Cminor.Kseq s tk))
                 nil.

Tactic Notation "match_cont_cases" tactic(first) tactic(c) :=
    first; [
      c "match_Kstop" |
      c "match_Kseq" |
      c "match_Kseq2" |
      c "match_Kblock" |
      c "match_Kblock2" |
      c "match_Kcall_none" |
      c "match_Kcall_some"].

Inductive transl_lblstmt_cont (cenv: compilenv) (xenv: exit_env)
                              : lbl_stmt -> cont -> cont -> Prop :=
  | tlsc_default: forall s k ts,
      transl_stmt cenv (switch_env (LSdefault s) xenv) s = OK ts ->
      transl_lblstmt_cont cenv xenv (LSdefault s) k (Kblock (Kseq ts k))
  | tlsc_case: forall i s ls k ts k',
      transl_stmt cenv (switch_env (LScase i s ls) xenv) s = OK ts ->
      transl_lblstmt_cont cenv xenv ls k k' ->
      transl_lblstmt_cont cenv xenv (LScase i s ls) k (Kblock (Kseq ts k')).

Inductive cast_chunk_eq : unary_operation ->
                          memory_chunk ->
                          Prop :=
| cast_chunk_eq_8signed:
    cast_chunk_eq Ocast8signed Mint8signed
| cast_chunk_eq_8unsigned:
    cast_chunk_eq Ocast8unsigned Mint8unsigned
| cast_chunk_eq_16signed:
    cast_chunk_eq Ocast16signed Mint16signed
| cast_chunk_eq_16unsigned:
    cast_chunk_eq Ocast16unsigned Mint16unsigned
| cast_chunk_eq_singlefloat:
    cast_chunk_eq Osingleoffloat Mfloat32.

Inductive match_assign_chunk_cont : Cstacked.expr_cont ->
                                    Cminor.expr_cont ->
                                    memory_chunk ->
                                    option pointer ->
                                    list bool ->
                                    Prop :=
| match_assign_chunk_local: forall sk tk xenv osp c ofs sp id
      (CID : (get_cenv sk) !! id = Var_stack_scalar c ofs)
      (SP  : osp = Some sp)
      (MK  : match_cont sk tk xenv),
  match_assign_chunk_cont (Cstacked.EKassign id sk)
                          (Cminor.EKstoreval c (Vptr (Ptr.add sp (Int.repr ofs))) tk)
                          c osp xenv
| match_assign_chunk_global: forall sk tk xenv c id p osp
       (CID : (get_cenv sk) !! id = Var_global_scalar c)
       (GID : Genv.find_symbol ge id = Some p)
       (MK  : match_cont sk tk xenv),
  match_assign_chunk_cont (Cstacked.EKassign id sk)
                          (Cminor.EKstoreval c (Vptr p) tk) c osp xenv
| match_assign_chunk_store: forall sk tk xenv c v v' osp
       (LD  : Val.lessdef v v')
       (MK  : match_cont sk tk xenv),
  match_assign_chunk_cont (Cstacked.EKstoreval c v sk)
                          (Cminor.EKstoreval c v' tk) c osp xenv.

Inductive match_var_set_cont : Cstacked.cont ->
                               Cminor.cont ->
                               option ident ->
                               list bool ->
                               Prop :=
| match_var_set_cont_none: forall sk tk xenv
    (MK : match_cont sk tk xenv),
      match_var_set_cont sk tk None xenv
| match_var_set_cont_some: forall sk tk id xenv s
    (VS  : Cminorgen.var_set (get_cenv sk) id (Evar id) = OK s)
    (MK : match_cont sk tk xenv),
      match_var_set_cont sk (Kseq s tk) (Some id) xenv.
 
(** Continuation relation for expressions. *)
Inductive match_expr_cont : Cstacked.expr_cont -> 
                            Cminor.expr_cont -> 
                            option pointer ->
                            exit_env -> 
                            Prop :=
  | match_EKunop : forall op sk tk xenv osp 
      (MEK : match_expr_cont sk tk osp xenv),
      match_expr_cont (Cstacked.EKunop op sk)
                      (Cminor.EKunop op tk)
                      osp xenv
  | match_EKbinop1 : forall op sk tk sex tex xenv osp 
      (MEK : match_expr_cont sk tk osp xenv)
      (TEX : transl_expr (get_cenv_ek sk) sex = OK tex),
      match_expr_cont (Cstacked.EKbinop1 op sex sk)
                      (Cminor.EKbinop1 op tex tk)
                      osp xenv
  | match_EKbinop2 : forall op sk tk v v' xenv osp 
      (MEK : match_expr_cont sk tk osp xenv)
      (LD : Val.lessdef v v'),
      match_expr_cont (Cstacked.EKbinop2 op v sk)
                      (Cminor.EKbinop2 op v' tk)
                      osp xenv
  | match_EKload : forall sk tk xenv c osp 
      (MEK : match_expr_cont sk tk osp xenv),
      match_expr_cont (Cstacked.EKload c sk)
                      (Cminor.EKload c tk)
                      osp xenv
  | match_EKcall : forall sk tk xenv oid sg sexs texs osp 
      (MEK : match_var_set_cont sk tk oid xenv)
      (TEXL: transl_exprlist  (get_cenv sk) sexs = OK texs),
      match_expr_cont (Cstacked.EKcall oid sg sexs sk)
                      (Cminor.EKcall oid sg texs tk)
                      osp xenv
  | match_EKargs : forall sk tk xenv oid sexs texs lv v lv' v' osp sig
      (MEK : match_var_set_cont sk tk oid xenv)
      (TEXL: transl_exprlist (get_cenv sk) sexs = OK texs)
      (LD : Val.lessdef v v')
      (LDV : Val.lessdef_list lv lv'),
      match_expr_cont (Cstacked.EKargs oid v sig sexs lv sk)
                      (Cminor.EKargs oid v' sig texs lv' tk)
                      osp xenv
  | match_EKatargs : forall sk tk xenv oid sexs texs lv lv' osp astmt
      (MEK : match_var_set_cont sk tk oid xenv)
      (TEXL: transl_exprlist (get_cenv sk) sexs = OK texs)
      (LDV : Val.lessdef_list lv lv'),
      match_expr_cont (Cstacked.EKatargs oid astmt sexs lv sk)
                      (Cminor.EKatargs oid astmt texs lv' tk)
                      osp xenv
  | match_EKcond : forall sk tk sex1 sex2 tex1 tex2 xenv osp 
      (MEK : match_expr_cont sk tk osp xenv)
      (TEX : transl_expr (get_cenv_ek sk) sex1 = OK tex1)
      (TEX : transl_expr (get_cenv_ek sk) sex2 = OK tex2),
      match_expr_cont (Cstacked.EKcond sex1 sex2 sk)
                      (Cminor.EKcond tex1 tex2 tk)
                      osp xenv
  | match_EKassign: forall sk tk xenv s osp id
      (VS : var_set (get_cenv sk) id (Evar id) = OK s)
      (MEK : match_cont sk tk xenv),
      match_expr_cont (Cstacked.EKassign id sk)
                      (Cminor.EKassign id (Kseq s tk))
                      osp xenv
  | match_EKassign_local : forall sk tk xenv id c osp 
      (CID : (get_cenv sk) !! id = Var_local c)
      (MEK : match_cont sk tk xenv),
      match_expr_cont (Cstacked.EKassign id sk)
                      (make_cast_cont c (Cminor.EKassign id tk))
                      osp xenv
  | match_EKassign_chunk : forall sk tk c osp xenv
      (MACK : match_assign_chunk_cont sk tk c osp xenv),
      match_expr_cont sk tk osp xenv
  | match_EKthread1 : forall sk tk xenv sex tex osp 
      (MEK : match_cont sk tk xenv)
      (TEX : transl_expr (get_cenv sk) sex = OK tex),
      match_expr_cont (Cstacked.EKthread1 sex sk)
                      (Cminor.EKthread1 tex tk)
                      osp xenv
  | match_EKthread2 : forall sk tk xenv p osp 
      (MEK : match_cont sk tk xenv),
      match_expr_cont (Cstacked.EKthread2 p sk)
                      (Cminor.EKthread2 p tk)
                      osp xenv
  | match_EKcondstmt : forall sk tk s1 s2 ts1 ts2 xenv osp 
      (MEK : match_cont sk tk xenv)
      (TEX : transl_stmt (get_cenv sk) xenv s1 = OK ts1)
      (TEX : transl_stmt (get_cenv sk) xenv s2 = OK ts2),
      match_expr_cont (Cstacked.EKcondstmt s1 s2 sk)
                      (Cminor.EKcondstmt ts1 ts2 tk)
                      osp xenv
  | match_EKswitch : forall sk tk tk' xenv l tbl osp 
      (STBL: switch_table l 0%nat = tbl)
      (MEK : match_cont sk tk xenv)
      (TLS : transl_lblstmt_cont (get_cenv sk) xenv l tk tk'),
      match_expr_cont (Cstacked.EKswitch l sk)
                      (Cminor.EKswitch tbl (length tbl) tk')
                      osp xenv
  | match_EKreturn : forall sk tk xenv osp f 
      (CC  : Cstacked.get_fundef (Cstacked.call_cont sk) = Some (Internal f))
      (FSIG: sig_res (Csharpminor.fn_sig f) <> None)
      (MEK : match_cont sk tk xenv),
      match_expr_cont (Cstacked.EKreturn sk)
                      (Cminor.EKreturn tk)
                      osp xenv
  | match_EKstoreaddr : forall sk tk xenv c sex tex osp 
      (MEK : match_cont sk tk xenv)
      (TEX : transl_expr (get_cenv sk) sex = OK tex),
      match_expr_cont (Cstacked.EKstoreaddr c sex sk)
                      (Cminor.EKstoreaddr c (store_arg c tex) tk)
                      osp xenv
(*  | match_EKstoreval : forall sk tk cenv xenv c v v' osp 
      (MEK : match_cont sk tk cenv xenv)
      (LD : Val.lessdef v v'),
      match_expr_cont (Cstacked.EKstoreval c v sk)
                      (Cminor.EKstoreval c v' tk)
                      osp cenv xenv *)
  | match_cast_assign: forall sk tk xenv c cst osp
      (CCE : cast_chunk_eq cst c)
      (MACK: match_assign_chunk_cont sk tk c osp xenv),
      match_expr_cont (Cstacked.EKunop cst sk) tk osp xenv.

Tactic Notation "match_expr_cont_cases" tactic(first) tactic(c) :=
    first; [
      c "match_EKunop" |
      c "match_EKbinop1" |
      c "match_EKbinop2" |
      c "match_EKload" |
      c "match_EKcall" |
      c "match_EKargs" |
      c "match_EKatargs" |
      c "match_EKcond" |
      c "match_EKassign" |
      c "match_EKassign_local" |
      c "match_EKassign_chunk" |
      c "match_EKthread1" |
      c "match_EKthread2" |
      c "match_EKcondstmt" |
      c "match_EKswitch" |
      c "match_EKreturn" |
      c "match_EKstoreaddr" |
      c "match_cast_assign"].

Fixpoint bind_in_env (ids : list ident) (vs : list val)
                     (te : Cminor.env) : Prop :=
  match ids with
    | id :: idr =>
        match vs with 
          | v :: vr => 
             bind_in_env idr vr te /\
             match te ! id with
               | Some v' => Val.lessdef v v'
               | None => False
             end
          | nil => bind_in_env idr nil te
        end
    | nil => True
  end.

(** State relation. *)
Inductive match_states : Cstacked.state -> Cminor.state -> Prop := 
  | match_SKexpr: forall sex se sk tex te tk xenv sp
      (TEX : transl_expr (get_cenv_ek sk) sex = OK tex)
      (ME  : match_env (get_cenv_ek sk) se te)
      (Esp : sp = se.(csenv_sp))
      (MK  : match_expr_cont sk tk se.(csenv_sp) xenv),
      match_states (Cstacked.SKexpr sex se sk)
                   (Cminor.SKexpr tex sp te tk)
  | match_SKexpr_assign: forall sex se sk tex te tk xenv c cst sp
      (TEX : transl_expr (get_cenv_ek sk) sex = OK (Eunop cst tex))
      (ME  : match_env  (get_cenv_ek sk) se te)
      (CCE : cast_chunk_eq cst c)
      (Esp : sp = se.(csenv_sp))
      (MACK: match_assign_chunk_cont sk tk c se.(csenv_sp) xenv),
      match_states (Cstacked.SKexpr sex se sk)
                   (Cminor.SKexpr tex sp te tk)
  | match_SKval: forall se sk te tk xenv v v' sp
      (ME  : match_env  (get_cenv_ek sk) se te)
      (LD : Val.lessdef v v')
      (Esp : sp = se.(csenv_sp))
      (MK  : match_expr_cont sk tk se.(csenv_sp) xenv),
      match_states (Cstacked.SKval v se sk)
                   (Cminor.SKval v' sp te tk)
  | match_SKval_assign: forall se sk te tk xenv c v v' sp
      (ME  : match_env (get_cenv_ek sk) se te)
      (CVC : Val.lessdef (cast_value_to_chunk c v)
                         (cast_value_to_chunk c v'))
      (Esp : sp = se.(csenv_sp))
      (MACK: match_assign_chunk_cont sk tk c sp xenv),
      match_states (Cstacked.SKval v se sk)
                   (Cminor.SKval v' se.(csenv_sp) te tk)
  | match_SKstmt: forall s se sk ts te tk xenv sp
      (TEX : transl_stmt (get_cenv sk) xenv s = OK ts)
      (ME  : match_env (get_cenv sk) se te)
      (Esp : sp = se.(csenv_sp))
      (MK  : match_cont sk tk xenv),
      match_states (Cstacked.SKstmt s se sk)
                   (Cminor.SKstmt ts sp te tk)
  | match_SKstmt_seq:
      forall s1 s2 sk se ts1 tk sp te xenv 
      (TR: transl_stmt (get_cenv sk) xenv s1 = OK ts1)
      (ME  : match_env (get_cenv sk) se te)
      (Esp : sp = se.(csenv_sp))
      (MK: match_cont (Cstacked.Kseq s2 sk) tk xenv),
      match_states (Cstacked.SKstmt (Csharpminor.Sseq s1 s2) se sk)
                   (Cminor.SKstmt ts1 sp te tk)
  | match_SKcall_none: forall sk tk xenv args args' e te fn tfn 
      (TF : transl_fundef gce fn = OK tfn)
      (LD : Val.lessdef_list args args')
      (ME : match_env (get_cenv sk) e te)
      (MK : match_cont sk tk xenv),
      match_states 
        (Cstacked.SKcall args (Cstacked.Kcall None fn e sk))
        (Cminor.SKcall args'  (Cminor.Kcall   None tfn e.(csenv_sp) te tk))
  | match_SKcall: forall sk tk xenv args args' e te fn tfn s id
      (TF : transl_fundef gce fn = OK tfn)
      (LD : Val.lessdef_list args args')
      (VS : Cminorgen.var_set (get_cenv sk) id (Evar id) = OK s)
      (ME : match_env (get_cenv sk) e te)
      (MK : match_cont sk tk xenv),
      match_states 
        (Cstacked.SKcall args (Cstacked.Kcall (Some id) fn e sk))
        (Cminor.SKcall args' (Cminor.Kcall (Some id) tfn e.(csenv_sp) 
                               te (Cminor.Kseq s tk)))
  | match_SKexternal: forall sk tk xenv sg oid se te fn ck
      (MK : match_var_set_cont sk tk oid xenv)
      (ME : match_env (get_cenv sk) se te)
      (Eck : ck = Cminor.Kcall oid (External fn) se.(csenv_sp) te tk),
      match_states (Cstacked.SKexternal sg oid se sk)
                   (Cminor.SKexternal sg ck)
  | match_SKexternalReturn: forall sk tk xenv oid se v fn ck te
      (MK : match_var_set_cont sk tk oid xenv)
      (ME : match_env (get_cenv sk) se te)
      (Eck : ck = Cminor.Kcall oid (External fn) se.(csenv_sp) te tk),
      match_states (Cstacked.SKexternalReturn oid v se sk)
                   (Cminor.SKreturn v ck)
  | match_SKreturn: forall sk tk xenv v ov
      (RV : match ov with | Some v' => Val.lessdef v' v 
                          | None    => v = Vundef end)
      (MK : match_cont sk tk xenv),
      match_states (Cstacked.SKreturn ov sk)
                   (Cminor.SKreturn v tk)
  | match_SKbind: forall pars parids vs te se cenv xenv sk tk fn ts ps sp
      (Ecenv : cenv = get_cenv sk)
      (Eparids : parids = map (@fst _ _) pars)
      (ND  : NoDup parids)
      (BIE : bind_in_env parids vs te)  
      (*ME  : match_env_except cenv se te parids*)
      (ME  : match_env cenv se te)
      (Eps : store_parameters cenv pars = OK ps)
      (Ets : transl_stmt cenv xenv fn.(Csharpminor.fn_body) = OK ts)
      (Esp : sp = se.(csenv_sp))
      (MK  : match_cont sk tk xenv),    
      match_states (Cstacked.SKbind fn vs parids se sk)
                   (Cminor.SKstmt ps sp te (Cminor.Kseq ts tk))
  | match_SKfree_none: forall sp sk tk te xenv f env' k'
      (CC  : Cstacked.call_cont sk = Cstacked.Kcall None (Internal f) env' k')
      (FSIG: sig_res (Csharpminor.fn_sig f) = None)
      (MK  : match_cont sk tk xenv),    
        match_states (Cstacked.SKfree sp None sk)
                   (Cminor.SKstmt (Sreturn None) sp te tk)
  | match_SKfree_some: forall sp sk tk te xenv v v' f env' k' oid 
      (CC  : Cstacked.call_cont sk = Cstacked.Kcall oid (Internal f) env' k')
      (FSIG: sig_res (Csharpminor.fn_sig f) <> None)
      (LD  : Val.lessdef v v')
      (MK  : match_cont sk tk xenv),    
      match_states (Cstacked.SKfree sp (Some v) sk)
                   (Cminor.SKval v' sp te (Cminor.EKreturn tk)).

Tactic Notation "match_states_cases" tactic(first) tactic(c) :=
    first; [
      c "match_SKexpr" |
      c "match_SKval" |
      c "match_SKstmt" |
      c "match_SKcall" |
      c "match_SKexternal" |
      c "match_SKexternalReturn" |
      c "match_SKreturn" |
      c "match_SKbind" |
      c "match_SKfree_none" |
      c "match_SKfree_some"].

(*
Fixpoint measure_expr_cont (ek : Cstacked.expr_cont) :=
  match ek with 
    | Cstacked.EKunop _ ek' => S (measure_expr_cont ek')
    | Cstacked.EKbinop1 _ _ ek' => measure_expr_cont ek'
    | Cstacked.EKbinop2 _ _ ek' => measure_expr_cont ek'
    | Cstacked.EKload _ ek' => measure_expr_cont ek'
    | _ => 0%nat
  end.
*)

Fixpoint seq_left_depth (s: Csharpminor.stmt) : nat :=
  match s with
  | Csharpminor.Sseq s1 s2 => S (seq_left_depth s1)
  | _ => O
  end.

Definition measure (s : Cstacked.state) : nat :=
  match s with
    | Cstacked.SKbind fn l _ _ _ => 
      (length l + S (S (seq_left_depth fn.(Csharpminor.fn_body)))) %nat
    | Cstacked.SKexpr _ _ (Cstacked.EKassign _ _) => 1%nat
    | Cstacked.SKexpr _ _ (Cstacked.EKstoreval _ _ _) => 1%nat
    | Cstacked.SKval _ _ (Cstacked.EKunop _ _) => 1%nat
    | Cstacked.SKval _ _ (Cstacked.EKreturn _) => 1%nat
    | Cstacked.SKexternalReturn _ _ _ _ => 2%nat
    | Cstacked.SKstmt s _ _ => S (seq_left_depth s)
    | _ => 0%nat
  end.

Definition order := ltof _ measure.

Let slts := (mklts thread_labels (cst_step (ge, gvare))).
Let tlts := (mklts thread_labels (cm_step tge)).

Lemma match_StepSkipBlock:
  forall st env k
    (MS : match_states
           (Cstacked.SKstmt Csharpminor.Sskip env (Cstacked.Kblock k))
           st),
      exists st' : St tlts,
        weakstep tlts st TEtau st' /\
        match_states (Cstacked.SKstmt Csharpminor.Sskip env k) st'.
Proof. 
  intros.  inv MS. 
  revert ts k tk ME TEX MK.
  induction xenv as [|x xenv IH]; intros; inv MK. 
  (* True block *)
  inv TEX.
  eexists. split. by apply step_weakstep; constructor.
  eby econstructor.
  (* False block *)
  destruct (IH _ _ _ ME TEX MK0) as [st' [WS MS]].
  exists st'.
  split; [|done].
  eapply steptau_weakstep; [|edone].
  inv TEX. constructor.
Qed.

Lemma make_cast_taustar_cont:
  forall c x sp te k,
    taustar tlts (SKexpr (make_cast c x) sp te k)
                 (SKexpr x sp te (make_cast_cont c k)).
Proof.
  intros; destruct c; simpl;
    try (by apply steptau_taustar; constructor); constructor.
Qed.

Lemma cast_val_to_chunk_unop:
  forall op v v' c
    (EU : eval_unop op v = Some v')
    (CCE : cast_chunk_eq op c),
      cast_value_to_chunk c v = cast_value_to_chunk c v'.
Proof.
  intros.
  by inv CCE; inv EU; destruct v; simpl in *; 
    try done; rewrite ?Int.zero_ext_idem, ?Float.singleoffloat_idem, 
        ?Int.zero_ext_sign_ext.
Qed.  

Lemma transl_is_store_arg_dest:
  forall {cenv e x} c
    (TEX : transl_expr cenv e = OK x),
      store_arg c x = x \/
      exists s, exists cst, e = Csharpminor.Eunop cst s /\
                cast_chunk_eq cst c.
Proof.
  intros.
  destruct e; simpl in *; try by monadInv TEX; left.

  (* Var *)
  unfold var_get in TEX; destruct (cenv !! i); inv TEX; by left.
  (* AddrOf *)
  unfold var_addr in TEX; destruct (cenv !! i); inv TEX; by left.
  (* Unop *)
  monadInv TEX.
  destruct u; destruct c; simpl; try (by left);
    right; eexists; eexists; (split; [edone|constructor]).
Qed.

Lemma step_var_stack_correct:
  forall env id p c v s' k
  (EVR : eval_var_ref (ge, gvare) env id p c)
  (HT : Val.has_type v (type_of_chunk c))
  (MS : match_states (Cstacked.SKexpr (Csharpminor.Evar id) env k) s'),
   exists t' : St tlts,
     weakstep tlts s' (TEmem (MEread p c v)) t' /\
     (forall v' : val,
      Val.lessdef v' v ->
      exists s'' : St slts,
        stepr slts (Cstacked.SKexpr (Csharpminor.Evar id) env k)
          (TEmem (MEread p c v')) s'' /\ match_states s'' t').
Proof.
  intros.
  inv MS; simpl in TEX; unfold var_get in TEX; 
    try (by destruct ((get_cenv_ek k) !! id)); [].
  pose proof (ME id) as VM. 
  inv EVR; remember ((get_cenv_ek k) !! id) as cid; clear Heqcid;
      inv VM; rewrite EG in *; try done; clarify.
    (* Stack scalar *)
    eexists. split.
      rewrite EB in *; clarify.
      eapply steptau_weakstep. constructor.
      eapply steptau_weakstep. eby constructor.
      apply step_weakstep. eby econstructor.
    eby intros v' LD; inv LD; 
      [exists (Cstacked.SKval v env k) | exists (Cstacked.SKval Vundef env k)];
      split; try replace (Some anyp) with (csenv_sp env); econstructor; vauto.
  (* Global *)
  eexists. split.
    eapply steptau_weakstep. constructor.
    eapply steptau_weakstep. constructor. simpl in *. 
      eby rewrite <- (proj1 TRANSF), GFF.
    apply step_weakstep. 
    simpl in *; rewrite GVE in EGS; clarify. 
    rewrite Ptr.add_zero_r. eby econstructor.
  eby intros v' LD; inv LD; 
    [exists (Cstacked.SKval v env k) | exists (Cstacked.SKval Vundef env k)]; 
      split; econstructor; vauto.
Qed.

Lemma step_addr_correct:
  forall env k s' p id
    (EVA : eval_var_addr (ge, gvare) env id p)
    (MS : match_states (Cstacked.SKexpr (Eaddrof id) env k) s'),
      exists t' : St tlts,
        weakstep tlts s' TEtau t' /\
        match_states (Cstacked.SKval (Vptr p) env k) t'.
Proof.
  intros.
  inv MS; simpl in TEX; unfold var_addr in TEX; 
    try (by destruct ((get_cenv_ek k) !! id)); [].
  pose proof (ME id) as VM.
  remember ((get_cenv_ek k) !! id) as cid; clear Heqcid.
  inv EVA; try rewrite EG in VM.
  (* Stack scalar *) 
  inv VM. rewrite EB in *; clarify. 
  eexists. split. eapply step_weakstep. eby constructor. 
  rewrite <- EB; econstructor; eby try rewrite EB.
  (* Stack array *)
  inv VM. rewrite EB in *; clarify. 
  eexists. split. eapply step_weakstep. eby constructor. 
  rewrite <- EB; econstructor; eby try rewrite EB.
  (* Global cases *)
  rewrite EGN in VM; inv VM; inv TEX; eexists;
    (split; [eby eapply step_weakstep; constructor; simpl in *; 
      rewrite <- (proj1 TRANSF), GFF|]).
  eby rewrite Ptr.add_zero_r; econstructor.
  eby rewrite Ptr.add_zero_r; econstructor.
Qed.

Lemma step_var_local_correct:
  forall env id v k s'
  (EVL : eval_var_local env id v)
  (MS : match_states (Cstacked.SKexpr (Csharpminor.Evar id) env k) s'),
   exists t',
      weakstep tlts s' TEtau t' /\ match_states (Cstacked.SKval v env k) t'.
Proof.
  intros.
  inv MS; simpl in TEX; unfold var_get in TEX; 
    try (by destruct ((get_cenv_ek k) !! id)); [].
  pose proof (ME id) as VM. 
  inv EVL.
  remember ((get_cenv_ek k) !! id) as cid; clear Heqcid.
  inv VM; rewrite EG in *; try done; []. clarify.
  eexists. 
  split. apply step_weakstep. simpl. econstructor. eby symmetry.
  eby econstructor.
Qed.

Lemma eval_unop_lessdef:  forall {op x y x'}
    (EU : eval_unop op x = Some y)
    (LD : Val.lessdef x x'),
      exists y', eval_unop op x' = Some y' /\
                 Val.lessdef y y'.
Proof.
  intros. inv LD. eby eexists.
  destruct op; simpl in *; try done; inv EU; eby eexists.
Qed.

Lemma eval_binop_lessdef:  forall {op x y x' y' z}
    (EU  : eval_binop op x y = Some z)
    (LDx : Val.lessdef x x')
    (LDy : Val.lessdef y y'),
      exists z', eval_binop op x' y' = Some z' /\
                 Val.lessdef z z'.                  
Proof.
  intros. 
  by inv LDx; inv LDy; try (eby eexists);
    destruct op; try done; destruct x'; destruct y'. 
Qed.

Lemma step_unop_correct:
  forall op v v' env k s'
  (EU : eval_unop op v = Some v')
  (MS : match_states (Cstacked.SKval v env (Cstacked.EKunop op k)) s'),
   order (Cstacked.SKval v' env k)
     (Cstacked.SKval v env (Cstacked.EKunop op k)) /\
   match_states (Cstacked.SKval v' env k) s' \/
   (exists t',
      weakstep tlts s' TEtau t' /\ match_states (Cstacked.SKval v' env k) t').
Proof.
  intros.
  inv MS; [|by inv MACK].
  destruct (eval_unop_lessdef EU LD) as [x (EU' & LD')].
  inv MK. 
    by right; eexists; split; [apply step_weakstep|]; vauto.
  inv MACK.
  (* Cast-assign elimination *)
  inv MACK; left; (split; [done|]);
    eapply match_SKval_assign; vauto.
      rewrite <- (cast_val_to_chunk_unop _ _ _ _ EU CCE).
      by apply cast_value_to_chunk_lessdef.
    rewrite <- (cast_val_to_chunk_unop _ _ _ _ EU CCE).
    by apply cast_value_to_chunk_lessdef.
  rewrite <- (cast_val_to_chunk_unop _ _ _ _ EU CCE).
  by apply cast_value_to_chunk_lessdef.
Qed.

Lemma step_assign_correct:
  forall id e env k s'
    (MS : match_states (Cstacked.SKstmt (Csharpminor.Sassign id e) env k) s'),
      exists t' : St tlts,
        weakstep tlts s' TEtau t' /\
        match_states (Cstacked.SKexpr e env (Cstacked.EKassign id k)) t'.
Proof.
  intros.
  inv MS. monadInv TEX.
  unfold var_set in *. 
  pose proof (ME id) as VM.
  destruct ((get_cenv k) !! id) as [] _eqn : Ecid; inv VM; try done.
  (* Local variable *)
  inv EQ0.
  eexists. split.
  eexists; eexists; split; [constructor|split].
  constructor. apply make_cast_taustar_cont. by vauto. 
  (* Stack scalar *)
  inv EQ0.
  eexists. split.
    eapply steptau_weakstep. constructor.
    eapply steptau_weakstep. eby constructor. 
    apply step_weakstep. constructor.
  replace (Some anyp) with (csenv_sp env).
  destruct (transl_is_store_arg_dest m EQ) as [-> | [e' [o' (-> & CCE)]]].
    econstructor; try edone; eby eapply match_EKassign_chunk; vauto.
  simpl in EQ. monadInv EQ.
  eapply  match_SKexpr_assign; [| edone | edone | edone | ].
  by simpl; rewrite EQ0; inv CCE.
  eby econstructor.
  (* Global scalar *)
  inv EQ0.
  eexists. split.
    eapply steptau_weakstep. constructor.
    eapply steptau_weakstep.
      constructor. simpl.
      eby rewrite <- (proj1 TRANSF), GVP, Ptr.add_zero_r.
    apply step_weakstep. constructor.
  destruct (transl_is_store_arg_dest m EQ) as [-> | [e' [o' (-> & CCE)]]].
    by econstructor; try edone; eapply match_EKassign_chunk; vauto.
  simpl in EQ. monadInv EQ.
  eapply  match_SKexpr_assign; [| edone | edone | edone | ].
  by simpl; rewrite EQ0; inv CCE.
  eby econstructor.
Qed.

Lemma step_assign_env_correct:
  forall env id p c k s' v
    (EVR : eval_var_ref (ge, gvare) env id p c)
    (MS : match_states (Cstacked.SKval v env (Cstacked.EKassign id k)) s'),
     exists t' : St tlts,
        exists v' : val,
          Val.lessdef (cast_value_to_chunk c v) v' /\
          weakstep tlts s' (TEmem (MEwrite p c v')) t' /\
          match_states (Cstacked.SKstmt Csharpminor.Sskip env k) t'.
Proof.
  intros.
  inv MS; pose proof (ME id) as VM; simpl in VM. 
    inv MK.
        unfold var_set in VS.
        inv EVR; rewrite EG in *. 
        (* Stack scalar *)
        rewrite EB in *; clarify.
        inv VM. rewrite <- H1 in VS; inv VS.
        eexists; eexists; split.
          eby eapply cast_value_to_chunk_lessdef.
        split. 
          (* Assign *)
          eapply steptau_weakstep. eby econstructor. 
          (* Seq *)
          eapply steptau_weakstep. eby econstructor. 
          (* Sstore *)
          eapply steptau_weakstep. eby econstructor.
          (* Address computation *)
          eapply steptau_weakstep. eby econstructor.
          eapply steptau_weakstep. eby econstructor.
          (* Value retrieval *)
          eapply steptau_weakstep. econstructor. eby rewrite PTree.gss.
          (* Finally, do the store *)
          apply step_weakstep. eby rewrite <- EB; econstructor.
        econstructor; try edone.
        intro id'. specialize (ME id').
        destruct (peq id' id) as [-> | N].
          rewrite EG, <- H1, EB. by constructor.
        by rewrite PTree.gso.
        (* Global *)
        inv VM; simpl in EGS; rewrite EGS in GVE; [|done].
        rewrite <- H1 in VS; inv VS. 
        simpl in EGS. rewrite GVE in EGS.
        simpl in GFF. rewrite GVP in GFF. clarify. 
        pose proof GVP as GVP'. rewrite (proj1 TRANSF) in GVP.
        eexists; eexists; split.
          eby eapply cast_value_to_chunk_lessdef.
        split. 
          (* Assign *)
          eapply steptau_weakstep. eby econstructor. 
          (* Seq *)
          eapply steptau_weakstep. eby econstructor. 
          (* Sstore *)
          eapply steptau_weakstep. eby econstructor.
          (* Address computation *)
          eapply steptau_weakstep. econstructor. simpl. eby rewrite GVP.
          eapply steptau_weakstep. eby econstructor.
          (* Value retrieval *)
          eapply steptau_weakstep. econstructor. eby rewrite PTree.gss.
          (* Finally, do the store *)
        apply step_weakstep. rewrite Ptr.add_zero_r. by constructor.
        econstructor; try edone.
        intro id'. specialize (ME id').
        destruct (peq id' id) as [-> | N].
          rewrite EG, <- H1. eby econstructor.
        by rewrite PTree.gso.
      by inv EVR; rewrite EG, CID in VM; inv VM. 
    inv MACK; rewrite CID in VM; inv VM.
      (* Stack *)
      inv EVR; rewrite EG in *; clarify; []; rewrite EB in *; clarify.
      eexists; eexists; split.
        eby eapply cast_value_to_chunk_lessdef.
      split. apply step_weakstep. constructor.
      eby rewrite <- EB; econstructor.
    (* Global *)
    inv EVR; rewrite EG in *; clarify; []; simpl in *; 
      rewrite GVE, GID in *; clarify.
    eexists; eexists; split.
      eby eapply cast_value_to_chunk_lessdef.
    split. apply step_weakstep. constructor.
    vauto.
  (* Now the cases with eliminated cast... *)
  inv MACK; rewrite CID in VM; inv VM.
    inv EVR; rewrite EG in *; clarify; []; rewrite EB in *; clarify.
    eexists; eexists; split; [edone | split].
      apply step_weakstep. constructor.
    eby rewrite <- EB; econstructor.
  inv EVR; rewrite EG in *; clarify; []; simpl in *; 
    rewrite GVE, GID in *; clarify.
  eexists; eexists; split; [edone | split].
    apply step_weakstep. constructor.
  vauto.
Qed.

Lemma make_cast_cont_taustar:
  forall c k osp v e,
    exists v', 
      taustar tlts (SKval v osp e (make_cast_cont c k))
                   (SKval v' osp e k) /\
      Val.lessdef (Val.load_result c v) v'.
Proof.
  intros.
  destruct c; simpl; 
    try (eexists; split; 
      [eby apply steptau_taustar; econstructor | destruct v; vauto]);
    eexists; (split; [by apply taustar_refl | destruct v; vauto]).
Qed.

Lemma update_env_match:
  forall cenv env te v v' c id
  (ME : match_env cenv env te)
  (LOC: cenv !! id = Var_local c)
  (LD : Val.lessdef v v'),
    match_env cenv
      (mkcsenv (csenv_sp env) (csenv_env env) ! id <- (Env_local v c))
      te ! id <- v'.
Proof.
  intros.
  pose proof (ME id) as VM. inv VM; rewrite LOC in *; clarify; [].
  intro id'. simpl.
  destruct (peq id' id) as [<- | N].
    simpl; rewrite !@PTree.gss, LOC.
    eby eapply match_env_item_local.
  specialize (ME id').
  eby rewrite !@PTree.gso.
Qed.

Lemma lessdef_trans:
  forall v1 v2 v3
    (LD1 : Val.lessdef v1 v2)
    (LD2 : Val.lessdef v2 v3),
    Val.lessdef v1 v3.
Proof.
  intros. inv LD1; inv LD2; vauto.
Qed.

Lemma step_assign_local_correct:
  forall env id v env' k s'
    (VLS : var_local_store env id v env')
    (MS : match_states (Cstacked.SKval v env (Cstacked.EKassign id k)) s'),
      exists t',
        weakstep tlts s' TEtau t' /\
        match_states (Cstacked.SKstmt Csharpminor.Sskip env' k) t'.
Proof.
  intros.
  inv MS; pose proof (ME id) as VM.
    inv MK.
        inv VLS. rewrite EG in VM. inv VM.
        unfold var_set in VS. rewrite <- H1 in VS. inv VS.
        destruct (make_cast_cont_taustar c (EKassign id tk0) 
          (csenv_sp env) v' (te ! id <- v')) as [x (TAU & LD')].
        eexists. split.
          eapply steptau_weakstep. eby econstructor.
          eapply steptau_weakstep. eby econstructor.
          eapply steptau_weakstep. eby econstructor.
          eapply taustar_weakstep. apply make_cast_taustar_cont.
          eapply steptau_weakstep. econstructor. eby rewrite PTree.gss.
          eapply taustar_weakstep. edone.
          eapply step_weakstep. eby econstructor.
        econstructor; try edone.
        intros id'.
        destruct (peq id' id) as [-> | N]; simpl.
          rewrite !@PTree.gss, <- H1. 
          econstructor. eapply lessdef_trans, LD'.
          by apply Val.load_result_lessdef.
        by rewrite !@PTree.gso.
      inv VLS. rewrite EG in VM. inv VM.
      rewrite CID in *; clarify.
      destruct (make_cast_cont_taustar c (EKassign id tk0) 
        (csenv_sp env) v' te) as [x (TAU & LD')];
        eexists; (split; [eapply taustar_weakstep, step_weakstep; 
                         [edone|eby econstructor] | ]).
      econstructor; try edone.
      eapply update_env_match; try edone.
      eapply lessdef_trans, LD'. by apply Val.load_result_lessdef.      
    by inv MACK; inv VLS; rewrite EG in VM; inv VM; rewrite CID in *.
  by inv MACK; inv VLS; rewrite EG in VM; inv VM; rewrite CID in *.
Qed.

Lemma step_store_correct:  
  forall v env c p k s'
    (MS : match_states
         (Cstacked.SKval v env (Cstacked.EKstoreval c (Vptr p) k)) s'),
    exists t', exists v',
        Val.lessdef (cast_value_to_chunk c v) v' /\
        weakstep tlts s' (TEmem (MEwrite p c v')) t' /\
        match_states (Cstacked.SKstmt Csharpminor.Sskip env k) t'.
Proof.
  intros. inv MS.
    inv MK. inv MACK.
    eexists; eexists. 
    split. eby apply cast_value_to_chunk_lessdef.
    split.
      inv LD0.
      by apply step_weakstep; constructor.
    eby econstructor.
  inv MACK.
  eexists; eexists. 
  split. edone.
  split. by inv LD; apply step_weakstep; constructor.
  eby econstructor.
Qed.

Lemma step_call_correct:
  forall optid sig e args env k s'
  (MS : match_states
         (Cstacked.SKstmt (Csharpminor.Scall optid sig e args) env k) s'),
    exists t' : St tlts,
      weakstep tlts s' TEtau t' /\
      match_states (Cstacked.SKexpr e env (Cstacked.EKcall optid sig args k))
        t'.
Proof.
  intros. inv MS.
  destruct optid as [id|]; monadInv TEX.
    eexists; split.
      eapply steptau_weakstep. constructor.
      apply step_weakstep. constructor.
    eby econstructor vauto.
  eexists; split.
    apply step_weakstep. constructor.
  eby econstructor vauto.
Qed.

Lemma lessdef_list_app:
  forall l1 l1' l2 l2'
    (LD1 : Val.lessdef_list l1 l1')
    (LD2 : Val.lessdef_list l2 l2'),
      Val.lessdef_list (l1 ++ l2) (l1' ++ l2').
Proof.
  intros until l1.
  induction l1 as [|h l1 IH]; intros; inv LD1. done.
  rewrite <- ! app_comm_cons. by constructor; auto.
Qed.

Lemma step_call_args_correct:
  forall sig vf fd v e oid vs k s'
  (GFF : Genv.find_funct (Cstacked.ge (ge, gvare)) vf = Some fd)
  (FSIG: Csharpminor.funsig fd = sig)
  (MS : match_states
         (Cstacked.SKval v e (Cstacked.EKargs oid vf sig nil vs k)) s'),
    exists t' : St tlts,
      weakstep tlts s' TEtau t' /\
      match_states
        (Cstacked.SKcall (vs ++ v :: nil) (Cstacked.Kcall oid fd e k)) t'.
Proof.
  intros. inv MS; [|by inv MACK]. inv MK; [|by inv MACK].
  inv TEXL.
  (* Massage the global environment relation *)
  unfold Genv.find_funct in GFF. destruct vf; try done; simpl in GFF.
  inv LD0. pose proof (proj2 TRANSF p) as GF. rewrite GFF in GF.
  destruct (Genv.find_funct_ptr tge p) as [tf|] _eqn : GFF'; [|done].
  (* Show the step and the simulation *)
  assert(Esig: funsig tf = Csharpminor.funsig fd). 
    destruct fd. 
      monadInv GF. unfold transl_function in EQ.
      by destruct build_compilenv; destruct zle; [monadInv EQ|].
    by inv GF.
  inv MEK; eexists; (split; [eby apply step_weakstep; econstructor|]);
    econstructor; try edone; eby eapply lessdef_list_app; vauto. 
Qed.  
  
Lemma step_call_args1_correct:
  forall vf e oid sig i is k s'
    (MS : match_states
         (Cstacked.SKval vf e (Cstacked.EKcall oid sig (i :: is) k)) s'),
      exists t' : St tlts,
        weakstep tlts s' TEtau t' /\
        match_states (Cstacked.SKexpr i e (Cstacked.EKargs oid vf sig is nil k)) t'.
Proof.
  intros. inv MS; [|by inv MACK]. inv MK; [|by inv MACK].
  monadInv TEXL.
  eexists. split.
    apply step_weakstep. constructor.
  eby econstructor vauto.
Qed.

Lemma step_call_args2_correct:
  forall sig v e oid vf i is vs k s'
    (MS : match_states
           (Cstacked.SKval v e (Cstacked.EKargs oid vf sig (i :: is) vs k)) s'),
      exists t' : St tlts,
        weakstep tlts s' TEtau t' /\
        match_states
          (Cstacked.SKexpr i e
             (Cstacked.EKargs oid vf sig is (vs ++ v :: nil) k)) t'.
Proof.
  intros. inv MS; [|by inv MACK]. inv MK; [|by inv MACK].
  monadInv TEXL.
  eexists. split.
    apply step_weakstep. constructor.
  econstructor vauto.  
  econstructor; try edone.
  eby eapply lessdef_list_app; vauto.
Qed.

Lemma step_empty_call_correct:
  forall vf fd e oid sig k s'
  (GFF : Genv.find_funct (Cstacked.ge (ge, gvare)) vf = Some fd)
  (FSIG: Csharpminor.funsig fd = sig)
  (MS : match_states (Cstacked.SKval vf e (Cstacked.EKcall oid sig nil k)) s'),
    exists t' : St tlts,
      weakstep tlts s' TEtau t' /\
      match_states (Cstacked.SKcall nil (Cstacked.Kcall oid fd e k)) t'.
Proof.
  intros.  inv MS; [|by inv MACK]. inv MK; [|by inv MACK].
  inv TEXL.
  (* Massage the global environment relation *)
  unfold Genv.find_funct in GFF. destruct vf; try done; simpl in GFF.
  inv LD. pose proof (proj2 TRANSF p) as GF. rewrite GFF in GF.
  destruct (Genv.find_funct_ptr tge p) as [tf|] _eqn : GFF'; [|done].
  (* Show the step and the simulation *)
  assert(Esig: funsig tf = Csharpminor.funsig fd). 
    destruct fd. 
      monadInv GF. unfold transl_function in EQ.
      by destruct build_compilenv; destruct zle; [monadInv EQ|].
    by inv GF.
  inv MEK; eexists; (split; [eby apply step_weakstep; econstructor|]);
    econstructor; try edone; eby eapply lessdef_list_app; vauto. 
Qed.

Lemma step_exit_seq_correct:
  forall n env s k s'
  (MS : match_states
         (Cstacked.SKstmt (Csharpminor.Sexit n) env (Cstacked.Kseq s k)) s'),
    exists t' : St tlts,
      weakstep tlts s' TEtau t' /\
      match_states (Cstacked.SKstmt (Csharpminor.Sexit n) env k) t'.
Proof.
  intros. inv MS. monadInv TEX.
  remember (Cstacked.Kseq s k) as sq; revert s k Heqsq.
  
  induction MK; intros; inv Heqsq;
    eby try (by eexists; split; [apply step_weakstep|]; vauto);
      destruct (IHMK ME _ _ (refl_equal _)) as [t' (WS & MS)];
        eexists; (split; [eapply steptau_weakstep|]; vauto).
Qed.

Lemma step_exit_block_correct:
  forall env k s'
    (MS : match_states
           (Cstacked.SKstmt (Csharpminor.Sexit 0) env (Cstacked.Kblock k)) s'),
      exists t' : St tlts,
        weakstep tlts s' TEtau t' /\
        match_states (Cstacked.SKstmt Csharpminor.Sskip env k) t'.
Proof.
  intros. inv MS. monadInv TEX.
  remember (Cstacked.Kblock k) as bk; revert k Heqbk.

  induction MK; intros; inv Heqbk.
  by eexists; split; [apply step_weakstep|]; vauto.
  eby destruct (IHMK ME _ (refl_equal _)) as [t' (WS & MS)];
    eexists; (split; [eapply steptau_weakstep|]; vauto).
Qed.

Lemma step_exists_block1_correct:
  forall n env k s'
    (MS : match_states
      (Cstacked.SKstmt (Csharpminor.Sexit (S n)) env (Cstacked.Kblock k)) s'),
      exists t' : St tlts,
        weakstep tlts s' TEtau t' /\
        match_states (Cstacked.SKstmt (Csharpminor.Sexit n) env k) t'.
Proof.
  intros. inv MS. monadInv TEX.
  remember (Cstacked.Kblock k) as bk; revert k Heqbk.

  induction MK; intros; inv Heqbk.
  by eexists; split; [apply step_weakstep|]; vauto.
  eby destruct (IHMK ME _ (refl_equal _)) as [t' (WS & MS)];
    eexists; (split; [eapply steptau_weakstep|]; vauto).
Qed.

Remark length_switch_table:
  forall sl base1 base2,
  length (switch_table sl base1) = length (switch_table sl base2).
Proof.
  induction sl; intros; simpl. auto. decEq; auto.
Qed.

Remark switch_table_shift:
  forall n sl base dfl,
  switch_target n (S dfl) (switch_table sl (S base)) =
  S (switch_target n dfl (switch_table sl base)).
Proof.
  induction sl; intros; simpl. auto. destruct (Int.eq n i); auto. 
Qed.

Lemma switch_descent:
  forall {cenv xenv ls body s} k,
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK s ->
  exists k',
  transl_lblstmt_cont cenv xenv ls k k'
  /\ (forall sp e,
      weakstep tlts (SKstmt s sp e k) TEtau (SKstmt body sp e k')).
Proof.
  induction ls; intros. 
  monadInv H. econstructor; split.
  econstructor; eauto.
  intros. eapply steptau_weakstep. constructor. 
          apply step_weakstep; constructor.
  monadInv H. exploit IHls; eauto. intros [k' [A B]]. 
  econstructor; split.
  econstructor; eauto.
  intros. eapply weakstep_taustar. eauto. 
  eapply taustar_step. constructor. apply steptau_taustar. constructor. 
Qed.

Lemma step_switch_correct:
  forall e cs env k s'
    (MS : match_states (Cstacked.SKstmt (Csharpminor.Sswitch e cs) env k) s'),
    exists t' : St tlts,
      weakstep tlts s' TEtau t' /\
      match_states (Cstacked.SKexpr e env (Cstacked.EKswitch cs k)) t'.
Proof.
  intros.
  inv MS. monadInv TEX.
  destruct (switch_descent tk EQ0) as [k' (TLS & WS)].
  eexists. split. 
    eapply weakstep_taustar. apply WS. 
    apply steptau_taustar. constructor.
  econstructor; try edone.
  eby eapply match_EKswitch.
Qed.

Lemma switch_ascent:
  forall n sp e {cenv xenv k ls k1}
  (TLC : transl_lblstmt_cont cenv xenv ls k k1),
  let tbl := switch_table ls O in
  let ls' := select_switch n ls in
  exists k2,
  taustar tlts (SKstmt (Sexit (switch_target n (length tbl) tbl)) sp e k1)
               (SKstmt (Sexit O) sp e k2)
  /\ transl_lblstmt_cont cenv xenv ls' k k2.
Proof.
  induction ls; intros; unfold tbl, ls'; simpl.
  inv TLC. econstructor; split. apply taustar_refl. econstructor; eauto.
  simpl in TLC. inv TLC. 
  rewrite Int.eq_sym. destruct (Int.eq i n).
  econstructor; split. apply taustar_refl. econstructor; eauto. 
  exploit IHls; eauto. intros [k2 [A B]].
  rewrite (length_switch_table ls 1%nat 0%nat). 
  rewrite switch_table_shift.
  econstructor; split. 
  eapply taustar_step. constructor. eapply taustar_step. constructor. eexact A. 
  exact B.
Qed.

Lemma switch_match_cont:
  forall xenv k tk ls tk',
  match_cont k tk xenv ->
  transl_lblstmt_cont (get_cenv k) xenv ls tk tk' ->
  match_cont (Cstacked.Kseq (seq_of_lbl_stmt ls) k) tk' (false :: switch_env ls xenv).
Proof.
  induction ls; intros; simpl.
  inv H0. apply match_Kblock2. econstructor; eauto.
  inv H0. apply match_Kblock2. eapply match_Kseq2. auto. eauto. 
Qed.

Lemma transl_lblstmt_suffix:
  forall n cenv xenv ls body ts,
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  let ls' := select_switch n ls in
  exists body', exists ts',
  transl_lblstmt cenv (switch_env ls' xenv) ls' body' = OK ts'.
Proof.
  induction ls; simpl; intros. 
  monadInv H.
  exists body; econstructor. rewrite EQ; eauto. simpl. reflexivity.
  monadInv H.
  destruct (Int.eq i n).
  exists body; econstructor. simpl. rewrite EQ; simpl. rewrite EQ0; simpl. reflexivity.
  eauto.
Qed.

Lemma switch_match_states:
  forall (* fn *) k e (* tfn *) (* ts *) tk te xenv ls (* body *) tk'
    (* TRF: transl_funbody cenv sz fn = OK tfn *)
    (ME: match_env (get_cenv k) e te)
    (* TR: transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts *)
    (MK: match_cont k tk xenv)
    (TK: transl_lblstmt_cont (get_cenv k) xenv ls tk tk'),
  exists S,
     weakstep tlts (SKstmt (Sexit O) e.(csenv_sp) te tk') TEtau S
  /\ match_states (Cstacked.SKstmt (seq_of_lbl_stmt ls) e k) S.
Proof.
  intros. destruct ls; simpl.
  inv TK. econstructor; split. 
    eapply steptau_weakstep. constructor.
    apply step_weakstep. constructor.
    eby econstructor. 
  inv TK. econstructor; split.
    eapply steptau_weakstep. constructor.
    apply step_weakstep. constructor.
  eapply match_SKstmt_seq; try edone.
  eapply switch_match_cont; eauto.
Qed.

Lemma step_select_correct:
  forall n env cs k s'
    (MS : match_states 
      (Cstacked.SKval (Vint n) env (Cstacked.EKswitch cs k)) s'),
      exists t' : St tlts,
        weakstep tlts s' TEtau t' /\
        match_states
          (Cstacked.SKstmt (seq_of_lbl_stmt (select_switch n cs)) env k) t'.
Proof.
  intros. inv MS; [|by inv MACK]. inv MK; [by inv MACK|]. inv LD.
  destruct (switch_ascent n (csenv_sp env) te TLS) as [k' (WS & TK)].
  (* TODO : missing transl_lblstmt in the simulation relation *)
  exploit switch_match_states; try edone. intros [ns (WS' & MS')].
  eexists. split.
    eapply steptau_weakstep. constructor.
    eapply taustar_weakstep. apply WS.
    edone.
  edone.
Qed.

(** Commutation between [find_label] and compilation *)

Section FIND_LABEL.

Variable lbl: label.

Remark find_label_var_set:
  forall cenv id e s k,
  var_set cenv id e = OK s ->
  find_label lbl s k = None.
Proof.
  intros. unfold var_set in H.
  destruct (cenv!!id); monadInv H; reflexivity.
Qed.

Lemma transl_lblstmt_find_label_context:
  forall cenv xenv ls body ts tk1 tk2 ts' tk',
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  transl_lblstmt_cont cenv xenv ls tk1 tk2 ->
  find_label lbl body tk2 = Some (ts', tk') ->
  find_label lbl ts tk1 = Some (ts', tk').
Proof.
  induction ls; intros.
  monadInv H. inv H0. simpl. simpl in H2. replace x with ts by congruence. rewrite H1. auto.
  monadInv H. inv H0.
  eapply IHls. eauto. eauto. simpl in H6. replace x with ts0 by congruence. simpl.
  rewrite H1. auto.
Qed.

Lemma transl_find_label:
  forall s k xenv ts tk,
  transl_stmt (get_cenv k) xenv s = OK ts ->
  match_cont k tk xenv ->
  match Cstacked.find_label lbl s k with
  | None => find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', exists xenv',
        find_label lbl ts tk = Some(ts', tk')
     /\ transl_stmt (get_cenv k') xenv' s' = OK ts'
     /\ match_cont k' tk' xenv'
     /\ get_cenv k = get_cenv k'
  end

with transl_lblstmt_find_label:
  forall ls xenv body k ts tk tk1,
  transl_lblstmt (get_cenv k) (switch_env ls xenv) ls body = OK ts ->
  match_cont k tk xenv ->
  transl_lblstmt_cont (get_cenv k) xenv ls tk tk1 ->
  find_label lbl body tk1 = None ->
  match Cstacked.find_label_ls lbl ls k with
  | None => find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', exists xenv',
        find_label lbl ts tk = Some(ts', tk')
     /\ transl_stmt (get_cenv k') xenv' s' = OK ts'
     /\ match_cont k' tk' xenv'
     /\ get_cenv k = get_cenv k'
  end.
Proof.
  intros. destruct s; try (monadInv H); simpl; auto.
  (* assign *)
  eapply find_label_var_set; eauto.
  (* call *)
  destruct o; monadInv H; simpl; auto.
  eapply find_label_var_set; eauto.
  (* seq *)
  exploit (transl_find_label s1 (Cstacked.Kseq s2 k)). eauto. 
    eapply match_Kseq. eexact EQ1. eauto.  
  destruct (Cstacked.find_label lbl s1 (Cstacked.Kseq s2 k)) as [[s' k'] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]]. 
  exists ts'; exists tk'; exists xenv'. intuition. rewrite A; auto.
  intro. rewrite H. apply transl_find_label with xenv; auto.
  (* ifthenelse *)
  exploit (transl_find_label s1). eauto. eauto.  
  destruct (Cstacked.find_label lbl s1 k) as [[s' k'] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]]. 
  exists ts'; exists tk'; exists xenv'. intuition. rewrite A; auto.
  intro. rewrite H. apply transl_find_label with xenv; auto. 
  (* loop *)
  replace (get_cenv k) with (get_cenv (Cstacked.Kseq (Csharpminor.Sloop s) k)); [|done].
  apply transl_find_label with xenv. auto. econstructor; eauto. simpl. rewrite EQ; auto.
  (* block *)
  replace (get_cenv k) with (get_cenv (Cstacked.Kblock k)); [|done].
  apply transl_find_label with (true :: xenv). auto. constructor; auto. 
  (* switch *)
  exploit @switch_descent; eauto. intros [k' [A B]].
  eapply transl_lblstmt_find_label. eauto. eauto. eauto. reflexivity.  
  (* return *)
  destruct o; monadInv H; auto.
  (* label *)
  destruct (ident_eq lbl l).
  exists x; exists tk; exists xenv; auto.
  apply transl_find_label with xenv; auto.
  (* atomic *)
  destruct o; monadInv H; simpl; auto.
  eapply find_label_var_set; eauto.

  intros. destruct ls; monadInv H; simpl.
  (* default *)
  inv H1. simpl in H3. replace x with ts by congruence. rewrite H2.
  eapply transl_find_label; eauto.
  (* case *)
  inv H1. simpl in H7.
  exploit (transl_find_label s (Cstacked.Kseq (seq_of_lbl_stmt ls) k)). eauto. eapply switch_match_cont; eauto. 
  destruct (Cstacked.find_label lbl s (Cstacked.Kseq (seq_of_lbl_stmt ls) k)) as [[s' k''] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]].
  exists ts'; exists tk'; exists xenv'; intuition. 
  eapply transl_lblstmt_find_label_context; eauto. 
  simpl. replace x with ts0 by congruence. rewrite H2. auto.
  intro.
  eapply transl_lblstmt_find_label. eauto. auto. eauto. 
  simpl. replace x with ts0 by congruence. rewrite H2. auto. 
Qed.

Remark find_label_store_parameters:
  forall cenv vars s k,
  store_parameters cenv vars = OK s -> find_label lbl s k = None.
Proof.
  induction vars; intros.
  monadInv H. auto.
  simpl in H. destruct a as [id lv]. monadInv H.
  simpl. rewrite (find_label_var_set cenv id (Evar id)); auto.
Qed.

End FIND_LABEL.

Lemma call_cont_related:
  forall sk tk xenv
    (MK : match_cont sk tk xenv),
      match_cont (Cstacked.call_cont sk) (call_cont tk) nil.
Proof.
  intros; induction MK; vauto.
Qed.

Lemma transl_find_label_body:
  forall {xenv f k tk lbl s' k'}
  (GFD : Cstacked.get_fundef (Cstacked.call_cont k) = (Some (Internal f)))
  (MK  : match_cont k tk xenv)
  (FL  : Cstacked.find_label lbl f.(Csharpminor.fn_body) (Cstacked.call_cont k) = Some (s', k')),
  exists tf, exists ts', exists tk', exists xenv',
     Cminor.get_fundef (Cminor.call_cont tk) = (Some (Internal tf))
  /\ find_label lbl tf.(fn_body) (call_cont tk) = Some(ts', tk')
  /\ transl_stmt (get_cenv k') xenv' s' = OK ts'
  /\ match_cont k' tk' xenv'
  /\ get_cenv k = get_cenv k'.
Proof.
  intros. 
  pose proof (call_cont_related _ _ _ MK) as CCR.
  destruct (Cstacked.call_cont k) as [] _eqn : CC; try done; []. inv GFD.
  assert (TB : exists sz, exists tf, 
      transl_funbody (fst (build_compilenv gce f)) sz f = OK tf /\
      Cminor.get_fundef (Cminor.call_cont tk) = (Some (Internal tf))).
    inv CCR; vauto.
  destruct TB as [sz [tf (TB & GFDt)]]. exists tf.
  monadInv TB. simpl.
  rewrite (find_label_store_parameters lbl (fst (build_compilenv gce f)) (Csharpminor.fn_params f)); auto.
  exploit (transl_find_label lbl). 2 : apply CCR. eexact EQ. rewrite FL.
  unfold get_cenv; rewrite CC; intros [ts' [tk' [xenv' X]]]; eauto.
Qed.

Lemma step_goto_correct:
  forall k k' f lbl s' s'' k'' env
    (CC : Cstacked.call_cont k = k')
    (GFD : Cstacked.get_fundef k' = Some (Internal f))
    (FL : Cstacked.find_label lbl (Csharpminor.fn_body f) k' = Some (s'', k''))
    (MS : match_states (Cstacked.SKstmt (Csharpminor.Sgoto lbl) env k) s'),
      exists t' : St tlts,
        weakstep tlts s' TEtau t' /\
        match_states (Cstacked.SKstmt s'' env k'') t'.
Proof.
  intros. inv MS. monadInv TEX.
  destruct (transl_find_label_body GFD MK FL) 
    as [tf [ts' [tk' [xenv' (GFD' & FL' & TS' & MK' & GEQ)]]]].
  rewrite GEQ in ME.
  eexists; split.
    apply step_weakstep. eby econstructor.
  eby econstructor.
Qed.

Lemma ptree_set_set:
  forall A t id (e e': A),
    (t ! id <- e) ! id <- e' = t ! id <- e'.
Proof.
  intros.
  eapply PTree.ext.
  intro x; destruct (peq x id) as [<- | N].
    by rewrite !PTree.gss.
  by rewrite !PTree.gso.
Qed.

Lemma step_return_finish_local_correct:
  forall k id fd env' k' v env'' s'
    (CC : Cstacked.call_cont k = Cstacked.Kcall (Some id) fd env' k')
    (VLS : var_local_store env' id v env'')
    (MS : match_states (Cstacked.SKreturn (Some v) k) s'),
      exists t' : St tlts,
        weakstep tlts s' TEtau t' /\
        match_states (Cstacked.SKstmt Csharpminor.Sskip env'' k') t'.
Proof.
  intros.
  inv MS; inv VLS. 
  assert (CCR := call_cont_related _ _ _ MK); rewrite CC in CCR; inv CCR.
  pose proof (ME id) as VM. rewrite EG in VM. inv VM.
  unfold var_set in VS.
  replace ((get_cenv k') !! id) with (Var_local c) in VS.
  inv VS.
  destruct (make_cast_cont_taustar c (EKassign id tk0) (csenv_sp env') v0 
                                 (te !id <- v0)) as [v'' (TAU & LD')].
  eexists; split.
    eapply steptau_weakstep. econstructor. eby symmetry. eby simpl.
    eapply steptau_weakstep. econstructor. 
    eapply steptau_weakstep. econstructor. 
    eapply taustar_weakstep. apply make_cast_taustar_cont. 
    eapply steptau_weakstep. econstructor. eby rewrite PTree.gss.
    eapply taustar_weakstep. edone.
    apply step_weakstep. constructor. edone.
  econstructor; try edone. rewrite ptree_set_set.
  eapply update_env_match. edone. done.
    eapply lessdef_trans, LD'. by apply Val.load_result_lessdef.
Qed.

Lemma update_env_match_non_local:
  forall cenv env te v id
  (ME : match_env cenv env te)
  (LOC: match cenv !! id with Var_local _ => False | _ => True end),
    match_env cenv env te ! id <- v.
Proof.
  intros. intro id'. specialize (ME id').
  destruct (peq id' id) as [<- | N].
    remember (cenv !! id') as cid; clear Heqcid.
    by inv ME; vauto.
  eby rewrite !@PTree.gso.
Qed.

Lemma step_return_finish_mem_correct:
  forall k id fd env' k' p c s' v
    (CC : Cstacked.call_cont k = Cstacked.Kcall (Some id) fd env' k')
    (EVR : eval_var_ref (ge, gvare) env' id p c)
    (MS : match_states (Cstacked.SKreturn (Some v) k) s'),
      exists t' : St tlts, exists v' : val,
        Val.lessdef (cast_value_to_chunk c v) v' /\
        weakstep tlts s' (TEmem (MEwrite p c v')) t' /\
        match_states (Cstacked.SKstmt Csharpminor.Sskip env' k') t'.
Proof.
  intros. inv MS.
  assert (CCR := call_cont_related _ _ _ MK); rewrite CC in CCR; inv CCR.
  pose proof (ME id) as VM.
  inv EVR.
    (* Stack *)
    rewrite EG in VM. inv VM. unfold var_set in VS.
    replace ((get_cenv k') !! id) with (Var_stack_scalar c offs) in VS.
    inv VS. unfold make_store, store_arg in *.
    eexists; eexists; split. eby eapply cast_value_to_chunk_lessdef.
    split.
      eapply steptau_weakstep. econstructor. eby symmetry. eby simpl.
      eapply steptau_weakstep. constructor. 
      eapply steptau_weakstep. constructor. 
      eapply steptau_weakstep. constructor. eby rewrite EB. 
      eapply steptau_weakstep. constructor.
      eapply steptau_weakstep. constructor. eby rewrite PTree.gss.
      eapply step_weakstep. constructor.
    econstructor; try edone.
    eapply update_env_match_non_local. edone. 
    by replace ((get_cenv k') !! id) with (Var_stack_scalar c offs).
  (* Global *)
  rewrite EG in VM. inv VM; simpl in EGS; inv EGS.
    2 : by replace (gvare ! id) with (Some (Vscalar c)) in GVE.
  simpl in GFF; rewrite GVP in GFF; inv GFF.
  unfold var_set in VS. rewrite GVE in *. clarify.
  replace ((get_cenv k') !! id) with (Var_global_scalar c) in VS.
  inv VS. unfold make_store, store_arg in *.
  eexists; eexists; split. eby eapply cast_value_to_chunk_lessdef.
  split.
    eapply steptau_weakstep. econstructor. eby symmetry. eby simpl.
    eapply steptau_weakstep. constructor. 
    eapply steptau_weakstep. constructor. 
    eapply steptau_weakstep. 
      constructor. simpl. eby rewrite <- (proj1 TRANSF), GVP, Ptr.add_zero_r.
    eapply steptau_weakstep. constructor.
    eapply steptau_weakstep. constructor. eby rewrite PTree.gss.
    eapply step_weakstep. constructor.
  econstructor; try edone.
  eapply update_env_match_non_local. edone.
  by replace ((get_cenv k') !! id) with (Var_global_scalar c).
Qed.

Lemma step_bind_args_stack_correct:
  forall env id c ofs sp v vs args k s' f
    (EG : (csenv_env env) ! id = Some (Env_stack_scalar c ofs))
    (EB : csenv_sp env = Some sp)
    (MS : match_states (SKbind f (v :: vs) (id :: args) env k) s'),
      exists t' : St tlts, exists v' : val,
        Val.lessdef (cast_value_to_chunk c v) v' /\
        weakstep tlts s' (TEmem (MEwrite (sp + Int.repr ofs) c v')) t' /\
        match_states (SKbind f vs args env k) t'.
Proof.
  intros.
  inv MS.
  simpl in BIE.
  destruct BIE as [BIE TE].
  destruct (te ! id) as [i|] _eqn : Ei; [|done].
  destruct pars as [|[id' v'] pars]; simpl in Eparids. done. 
  inv Eparids.
  monadInv Eps.
  pose proof (ME id') as VM. rewrite EG in VM. inv VM.
  unfold var_set in EQ. 
  replace ((get_cenv k) !! id') with (Var_stack_scalar c ofs) in EQ.
  inv EQ. rewrite EB in *; clarify.
  inversion ND as [|? ? NIN' ND']; subst.
  eexists. eexists. 
  split. eby eapply cast_value_to_chunk_lessdef.
  split. 
    eapply steptau_weakstep. constructor. 
    eapply steptau_weakstep. constructor. 
    eapply steptau_weakstep. constructor. eby simpl.
    eapply steptau_weakstep. constructor. simpl. 
    eapply steptau_weakstep. constructor. edone.
    eapply weakstep_taustar.
    eapply step_weakstep. constructor.
    eapply steptau_taustar. constructor.
  eby econstructor.
Qed.

Lemma bind_in_env_other:
  forall id l vs e v
    (NIN: ~ In id l)
    (BIE: bind_in_env l vs e),
      bind_in_env l vs (e ! id <- v).
Proof.
  intros id l.
  induction l as [|h l IH]; intros. done.
  
  destruct vs; simpl in *. 
    by eapply IH; eauto.
  destruct BIE. rewrite PTree.gso; [|by auto].
  by split; [eapply IH|]; eauto.
Qed.  

Lemma step_bind_args_env_correct:
  forall env id env' v vs args f k s'
    (VLS : var_local_store env id v env')
    (MS : match_states (SKbind f (v :: vs) (id :: args) env k) s'),
   (* order (SKbind f vs args env' k) (SKbind f (v :: vs) (id :: args) env k) /\
   match_states (SKbind f vs args env' k) s' \/ *)
      exists t' : St tlts,
        weakstep tlts s' TEtau t' /\ match_states (SKbind f vs args env' k) t'.
Proof.
  intros.
  inv MS.
  simpl in BIE.
  destruct BIE as [BIE TE].
  destruct (te ! id) as [i|] _eqn : Ei; [|done].
  destruct pars as [|[id' v'] pars]; simpl in Eparids. done. 
  inv Eparids.
  monadInv Eps. inv VLS.
  pose proof (ME id') as VM. rewrite EG in VM. inv VM.
  unfold var_set in EQ. 
  replace ((get_cenv k) !! id') with (Var_local c) in EQ.
  inv EQ.
  destruct (make_cast_cont_taustar c (EKassign id' (Kseq x0 (Kseq ts tk)))
               (csenv_sp env) i te) as [v'' (TAU & LD')].
  inversion ND as [|? ? NIN' ND']; subst.
  eexists; split.
    eapply steptau_weakstep. econstructor. 
    eapply steptau_weakstep. econstructor. 
    eapply taustar_weakstep. apply make_cast_taustar_cont. 
    eapply steptau_weakstep. econstructor. apply Ei. 
    eapply taustar_weakstep. edone.
    eapply weakstep_taustar.
    apply step_weakstep. constructor. edone.
    eapply steptau_taustar. constructor.
  econstructor; try edone.
    eby eapply bind_in_env_other.
  eapply update_env_match. edone. done.
  eapply lessdef_trans, LD'. by apply Val.load_result_lessdef.
Qed.

Lemma bind_in_env_set_params:
  forall l vs vs'
    (ND : NoDup l)
    (LD : Val.lessdef_list vs vs'),
      bind_in_env l vs (set_params vs' l).
Proof.
  induction l as [|h l IH]; intros. vauto.
  
  simpl. inv ND.
  destruct vs; inv LD. by eapply bind_in_env_other; auto.
  split. by eapply bind_in_env_other; auto.
  by rewrite PTree.gss.
Qed.

Remark identset_removelist_charact:
  forall l s x, Identset.In x (identset_removelist l s) <-> Identset.In x s /\ ~In x l.
Proof.
  induction l; simpl; intros. tauto.
  split; intros.
  exploit Identset.remove_3; eauto. rewrite IHl. intros [P Q].  
  split. auto. intuition. elim (Identset.remove_1 H1 H).
  destruct H as [P Q]. apply Identset.remove_2. tauto. rewrite IHl. tauto.
Qed.

Remark InA_In:
  forall (A: Type) (x: A) (l: list A),
  InA (fun (x y: A) => x = y) x l <-> In x l.
Proof.
  intros. rewrite InA_alt. split; intros. destruct H as [y [P Q]]. congruence. exists x; auto. 
Qed.

Remark NoDupA_norepet:
  forall (A: Type) (l: list A),
  NoDupA (fun (x y: A) => x = y) l -> NoDup l.
Proof.
  induction 1. constructor. constructor; auto. red; intros; elim H.
  rewrite InA_In. auto.
Qed.

Lemma make_vars_norepet:
  forall fn body,
  NoDup (fn_params_names fn ++ fn_vars_names fn) ->
  NoDup (make_vars (fn_params_names fn) (fn_vars_names fn) body
         ++ fn_params_names fn).
Proof.
  intros. rewrite nodup_app in H. destruct H as [A [B C]]. 
  rewrite nodup_app. split.
  unfold make_vars. rewrite nodup_app. split. auto. 
  split. apply NoDupA_norepet. apply Identset.elements_3w.
  red; intros. red; intros; subst y. rewrite <- InA_In in H0. 
  exploit Identset.elements_2. eexact H0.
  rewrite identset_removelist_charact. intros [P Q]. elim Q. 
  apply in_or_app. auto. 
  split. auto. 
  red; intros. unfold make_vars in H. destruct (in_app_or _ _ _ H).
  apply sym_not_equal. apply C; auto.
  rewrite <- InA_In in H1. exploit Identset.elements_2. eexact H1. 
  rewrite identset_removelist_charact. intros [P Q]. 
  red; intros; elim Q. apply in_or_app. left; congruence. 
Qed.

Lemma bind_env_disjoint:
  forall l' l vs e
  (DISJ: list_disjoint l l')
  (BIE : bind_in_env l vs e),
    bind_in_env l vs (set_locals l' e).
Proof.
  induction l' as [|h l' IH]; intros. done.
  
  simpl. apply bind_in_env_other. 
    intro IN. by elim (DISJ _ _ IN (in_eq _ _)).
  eapply IH. 
    intros x y INx INy. apply (DISJ _ _ INx (in_cons _ _ _ INy)).
  done.
Qed.

Lemma pars_vars_eq_fn_variables:
  forall fn,
    fn_params_names fn ++ fn_vars_names fn =
    map (@fst _ _) (fn_variables fn).
Proof.
  by intro; unfold fn_variables; rewrite map_app, map_map.
Qed.

Lemma set_params_defined:
  forall params args id,
  In id params -> (set_params args params)!id <> None.
Proof.
  induction params; simpl; intros.
  elim H.
  destruct args.
  rewrite PTree.gsspec. case (peq id a); intro.
  congruence. eapply IHparams. elim H; intro. congruence. auto.
  rewrite PTree.gsspec. case (peq id a); intro.
  congruence. eapply IHparams. elim H; intro. congruence. auto.
Qed.

Lemma set_locals_defined:
  forall e vars id,
  In id vars \/ e!id <> None -> (set_locals vars e)!id <> None.
Proof.
  induction vars; simpl; intros.
  tauto.
  rewrite PTree.gsspec. case (peq id a); intro.
  congruence.
  apply IHvars. assert (a <> id). congruence. tauto.
Qed.

Lemma set_locals_params_defined:
  forall args params vars id,
  In id (params ++ vars) ->
  (set_locals vars (set_params args params))!id <> None.
Proof.
  intros. apply set_locals_defined. 
  elim (in_app_or _ _ _ H); intro. 
  right. apply set_params_defined; auto.
  left; auto.
Qed.

Lemma assign_variables_not_in: 
  forall {vr v ids ce s ce' s'},
  ~ In v (map (@fst _ _)  vr) ->
  assign_variables ids vr (ce, s) = (ce', s') ->
  ce !! v = ce' !! v.
Proof.
  intro vr.

  induction vr as [|vh vt IH].
  intros; simpl in *; clarify.

  intros v ids ce s ce' s' NIN AV.
  destruct vh as [vid []]; simpl in AV;
    (assert (NINv : ~ In v (map (@fst _ _) vt));
      [intro; elim NIN; simpl; by right |]);
    destruct (Identset.mem vid ids);
      specialize (IH _ _ _ _ _ _ NINv AV) ;
        rewrite PMap.gso in IH; try done; 
          intro; subst; apply NIN; left; done.
Qed.

Lemma build_compilenv_not_in:
  forall id f cenv cenv' sz
   (NIN : ~ In id (map (@fst _ _) (fn_variables f)))
   (BCE : build_compilenv cenv f = (cenv', sz)),
     cenv !! id = cenv' !! id.
Proof.
  intros. unfold build_compilenv in *.
  eby eapply assign_variables_not_in.
Qed.

Lemma assign_variable_agree:
  forall vars n g1 g2 cenv1 cenv2 sz1 sz2 s
   (ND  : NoDup (map (@fst _ _) vars))
   (AV1 : assign_variables s vars (g1, n) = (cenv1, sz1))
   (AV2 : assign_variables s vars (g2, n) = (cenv2, sz2)),
     sz1 = sz2 /\
     forall id : ident, In id (map (@fst _ _) vars) -> cenv1 !! id = cenv2 !! id.
Proof.
  induction vars as [|[id vk] vars IH]; intros. simpl in *; clarify.
  simpl in AV1, AV2.
  inversion ND as [|? ? NIN ND']; subst.
  by destruct vk; [destruct Identset.mem|]; 
    destruct (IH _ _ _ _ _ _ _ _ ND' AV1 AV2) as [-> S]; (split; [done|]);
      intros id' IN; simpl in IN; specialize (S id'); destruct IN as [<- | IN];
        try (by apply S);
    rewrite <- (assign_variables_not_in NIN AV1), 
            <- (assign_variables_not_in NIN AV2), !PMap.gss.
Qed.

Lemma build_compileenv_agree:
  forall {f g1 cenv1 sz1 g2 cenv2 sz2}
  (ND  : NoDup (fn_params_names f ++ fn_vars_names f))
  (BCE1 : build_compilenv g1 f = (cenv1, sz1))
  (BCE2 : build_compilenv g2 f = (cenv2, sz2)),
    sz1 = sz2 /\
    forall id (IN : In id (fn_params_names f ++ fn_vars_names f)),
       cenv1 !! id = cenv2 !! id.
Proof.
  intros f. rewrite pars_vars_eq_fn_variables.
  intros.
  eby eapply assign_variable_agree; edone.
Qed.

Lemma build_env_agree:
  forall {f cenv sz1 g nenv sz2}
  (ND  : NoDup (fn_params_names f ++ fn_vars_names f))
  (BEM : build_env f = Some (nenv, sz1))
  (BCE : build_compilenv g f = (cenv, sz2)),
    sz1 = sz2.
Proof.
  intros.
  unfold build_env in BEM.
  destruct (build_compilenv (PMap.init Var_global_array) f) as [] _eqn : BCE'.
  destruct build_envmap. clarify. eby eapply build_compileenv_agree.
  done.
Qed.

Lemma build_envmap_not_in:
  forall {id cenv e vars acc}
   (EM : build_envmap vars cenv acc = Some e)
   (NIN: ~ In id (map (@fst _ _) vars)),
     e ! id = acc ! id.
Proof.
  intros until vars.
  induction vars as [|[id' vk] vars IH]; intros. by inv EM.
  
  simpl in NIN.
  destruct (peq id id') as [<- | N].
    by elim NIN; left.
  assert (NIN' : ~ In id (map (@fst _ _) vars)). 
    by intro X; elim NIN; right.
  simpl in EM; destruct (cenv !! id'); try done;
    by rewrite (IH _ EM NIN'), PTree.gso.
Qed.    

Lemma match_env_item_build_envmap:
  forall cenv cenv' te e sp id vars acc
  (ND : NoDup (map (@fst _ _) vars))
  (EM : build_envmap vars cenv' acc = Some e)
  (AG : forall id, In id (map (@fst _ _) vars) -> cenv !! id = cenv' !! id)
  (TEU: forall id, In id (map (@fst _ _) vars) -> te ! id <> None)
  (IN : In id (map (@fst _ _) vars))
  (SP : match (cenv !! id) with
          | Var_stack_scalar _ _  => sp <> None
          | Var_stack_array _ => sp <> None
          | _ => True 
        end),
    match_env_item id (cenv !! id) (e ! id) (te ! id) sp.
Proof.
  intros until vars.
  induction vars as [|[idv vk] vars IH]. done.
  
  intros. simpl in EM. inversion ND as [|? ? NIN ND']; subst.
  simpl in IN.
  destruct IN as [<- | IN].
    rewrite AG in SP |- *; try (by left); []. 
    specialize (TEU _ (in_eq _ _)); simpl in TEU.
    destruct (te ! idv) as [x|]; [|done].
    destruct (cenv' !! idv); try done;
      rewrite (build_envmap_not_in EM NIN), PTree.gss in *;
        destruct sp; try done; econstructor vauto.
  pose proof (fun idx INx => AG _ (in_cons _ idx _ INx)).
  pose proof (fun idx INx => TEU _ (in_cons _ idx _ INx)).
  destruct (cenv' !! idv); try done; eby exploit IH.
Qed.

Definition global_match gce gvare :=
  forall id,
    match gce !! id, gvare ! id with
      | Var_global_scalar c, Some (Vscalar c') => c = c'
      | Var_global_array, Some (Varray _)  => True
      | Var_global_array, None => True
      | _, _ => False
    end.

Lemma gce_gvare_match: global_match gce gvare.
Proof.
  unfold gce, gvare, build_global_compilenv, global_var_env.
  remember (prog_vars prog) as vars in |- *. clear Heqvars.
  remember (PMap.init Var_global_array) as ia.
  remember (PTree.empty var_kind) as it.
  assert (GI : global_match ia it).
    intro id'. by rewrite Heqia, PMap.gi, Heqit, PTree.gempty.
  clear Heqia Heqit.
  revert ia it GI.
  induction vars as [|[[id'  init'] vk'] vars IH]; intros. done.
  apply IH; simpl.
  intro id.
  destruct (peq id id') as [<- | N].
    by destruct vk'; rewrite PMap.gss; try done; rewrite PTree.gss.
  specialize (GI id).
  by destruct vk'; rewrite PMap.gso, PTree.gso; auto.
Qed.  

Lemma global_scalar_impl_find_symb:
  forall id
    (VG: match gce !! id with Var_global_scalar _ => True | _ => False end),
      Genv.find_symbol ge id <> None.
Proof.
  intros.
  apply FINDS.
  unfold gce, build_global_compilenv in VG.
  assert (INIT:
    match (PMap.init Var_global_array) !! id with
      | Var_global_scalar _ => True
      | _ => False
    end ->
    In id (map (fun x => fst (fst x)) (prog_vars prog))).
    by rewrite PMap.gi.
  remember (PMap.init Var_global_array) as i.
  remember (prog_vars prog) as vs in VG, INIT |- *.
  clear Heqi Heqvs.
  revert i INIT VG.
  induction vs as [|[[id' x] vk] vs IH]; intros. by eauto.
  
  simpl in *.
  destruct (peq id id') as [<- | N]. by left.
  right. 
  by destruct vk; eapply IH; try edone; (rewrite PMap.gso; [|done]);
    intro G; (destruct (INIT G); [elim N|]).
Qed.  

Lemma match_env_gce:
  forall sp te, 
    match_env gce (mkcsenv sp (PTree.empty _)) te.
Proof.
  intros sp te id.
  pose proof (gce_gvare_match id) as M.
  simpl; rewrite PTree.gempty.
  destruct (gce!!id) as [] _eqn : Egid; try done.
    pose proof (global_scalar_impl_find_symb id) as FSNE.
    rewrite Egid in FSNE.
    destruct (Genv.find_symbol ge id) as [p|] _eqn : FS. 2 : tauto.
    econstructor. by destruct (gvare ! id) as [[]|]; subst. edone.
  by constructor.
Qed.

(* Should be merged with Cstackedproofalloc *)
Lemma array_alignment_pos:
  forall sz, array_alignment sz > 0.
Proof. 
  intro. unfold array_alignment. repeat destruct zlt; omega.
Qed.

(* Should be merged with Cstackedproofalloc *)
Lemma align_size_chunk_le:
  forall n c, n <= align n (size_chunk c).
Proof. intros; apply align_le, size_chunk_pos. Qed.


(* Should be merged with Cstackedproofalloc *)
Lemma assign_variables_mono:
  forall {ids vars ie n ce sz},
    assign_variables ids vars (ie, n) = (ce, sz) ->
    n <= sz.
Proof.
  intros ids vars.
  induction vars as [|[vid [c | asz]] vt IH]; 
    intros ie n ce sz AV; simpl in *.
  (* Base case *)
  clarify; omega.
  (* Step case *)
    destruct Identset.mem; apply IH in AV;
      pose proof (align_size_chunk_le n c);
        pose proof (size_chunk_pos c); omega.
  apply IH in AV.
  pose proof (align_le n (array_alignment asz) 
    (array_alignment_pos asz)).
  pose proof (Zle_max_l 1 asz).
  omega.
Qed.

Lemma build_compilenv_empty:
  forall cenv' id vars s cenv
  (IN : In id (map (@fst _ _) vars))
  (AV : assign_variables s vars (cenv, 0) = (cenv', 0)),
    match (cenv' !! id) with
      | Var_stack_scalar _ _  => False
      | Var_stack_array _ => False
      | _ => True 
    end.
Proof.
  intros until vars.
  induction vars as [|[id' v] vars IH]; intros. done.
  simpl in *.
  destruct (In_dec peq id (map (@fst _ _) vars)) as [IN' | NIN'].
    destruct v; [destruct Identset.mem|]; pose proof (assign_variables_mono AV).
    - pose proof (align_le 0 _ (size_chunk_pos m)).
      pose proof (size_chunk_pos m). omegaContradiction.
    - eby eapply IH.
    - pose proof (align_le 0 _ (array_alignment_pos z)).
      pose proof (Zmax1 1 z). omegaContradiction.
  destruct IN as [<- | ?]; [|done].
  destruct v; [destruct Identset.mem|]; pose proof (assign_variables_mono AV);
    rewrite <- (assign_variables_not_in NIN' AV), PMap.gss.
  - pose proof (align_le 0 _ (size_chunk_pos m)).
    pose proof (size_chunk_pos m). omega.
  - done.
  - pose proof (align_le 0 _ (array_alignment_pos z)).
    pose proof (Zmax1 1 z). omega.
Qed.

Lemma match_env_build_env:
  forall f nenv fsize vs args' cenv sz s osp
    (ND : NoDup (fn_params_names f ++ fn_vars_names f))
    (BE : build_env f = Some (nenv, fsize))
    (LD : Val.lessdef_list vs args')
    (SP : match osp with
            | Some sp => True
            | None => fsize = 0
          end)
    (BCE: build_compilenv gce f = (cenv, sz)),
      match_env cenv (mkcsenv osp nenv)
        (set_locals
           (make_vars (fn_params_names f) (fn_vars_names f) s)
           (set_params args' (fn_params_names f))).
Proof.
  intros. intro id.
  unfold build_env in BE.
  destruct (build_compilenv (PMap.init Var_global_array) f) 
    as [cenv' fsz] _eqn : BCE'.
  destruct (build_envmap (fn_variables f) cenv' (PTree.empty env_item))
    as [em|] _eqn : BEM; [|done]. inv BE.
  destruct (In_dec peq id (map (@fst _ _) (fn_variables f))) as [IN | NIN].
    (* Local variable *)
    eapply match_env_item_build_envmap.
    - eby rewrite pars_vars_eq_fn_variables in ND.
    - edone.
    - rewrite <- pars_vars_eq_fn_variables.
      eby eapply build_compileenv_agree.
    - rewrite <- pars_vars_eq_fn_variables.
      intros idx INx. eapply set_locals_params_defined.
      unfold make_vars.
      apply in_app_or in INx; apply in_or_app.
      destruct INx. by left. by right; apply in_or_app; left.
    - done.  
    - destruct osp. simpl. by destruct (cenv !! id).
      subst. pose proof (build_compilenv_empty _ _ _ _ _ IN BCE').
      rewrite (proj2 (build_compileenv_agree ND BCE BCE')).
      by destruct (cenv' !! id).
      by rewrite pars_vars_eq_fn_variables.
  erewrite build_envmap_not_in; try edone; [].
  erewrite <- build_compilenv_not_in; try edone; [].
  apply match_env_gce.
Qed.

Lemma step_function_internal_with_stack_correct:
  forall ck optid f env k nenv fsize vs sp s'
    (CC : ck = Cstacked.Kcall optid (Internal f) env k)
    (BE : build_env f = Some (nenv, fsize))
    (FNZ : fsize <> 0%Z)
    (ND : NoDup (map (@fst _ _) (fn_variables f)))
    (MS : match_states (Cstacked.SKcall vs ck) s'),
    exists t' : St tlts,

      weakstep tlts s' (TEmem (MEalloc sp (Int.repr fsize) MObjStack)) t' /\
      match_states
        (SKbind f vs (map (@fst _ _) (Csharpminor.fn_params f))
           (mkcsenv (Some sp) nenv) ck) t'.
Proof.
  intros. 
  rewrite <- pars_vars_eq_fn_variables in ND.
  inv MS; clarify; monadInv TF;
    pose proof (make_vars_norepet _ x.(fn_body) ND) as ND';
    apply nodup_app in ND'; destruct ND' as (NDv & NDp & DISJ).
    (* No return *)
    unfold transl_function, build_env in EQ.
    destruct (build_compilenv gce f) as [cenv sz] _eqn : Ecenv.
    destruct zle as [LT|]; [|done]. pose proof EQ as TFB.
    monadInv EQ. simpl in *.
    eexists. split.
      eapply weakstep_taustar.
        eapply step_weakstep.
        econstructor. edone. simpl. eby eapply build_env_agree. done. eby simpl.  
      eapply steptau_taustar. constructor.
    econstructor; unfold get_cenv; simpl; try rewrite Ecenv; simpl; try edone.
        (* bind_in_env *)
        by apply bind_env_disjoint, bind_in_env_set_params; 
          try apply list_disjoint_sym, DISJ.
      (* match_env *)
      eby eapply match_env_build_env.
    (* match cont *)
    eapply match_Kcall_none with (sz := sz).
    econstructor; try edone. by rewrite Ecenv. edone. edone.
  unfold transl_function, build_env in EQ.
  destruct (build_compilenv gce f) as [cenv sz] _eqn : Ecenv.
  destruct zle as [LT|]; [|done]. pose proof EQ as TFB.
  monadInv EQ. simpl in *.
  eexists. split.
    eapply weakstep_taustar.
      eapply step_weakstep.
      econstructor. edone. simpl. eby eapply build_env_agree. done. eby simpl.  
    eapply steptau_taustar. constructor.
  econstructor; unfold get_cenv; simpl; try rewrite Ecenv; simpl; try edone.
      (* bind_in_env *)
      by apply bind_env_disjoint, bind_in_env_set_params; 
        try apply list_disjoint_sym, DISJ.
    (* match_env *)
    eby eapply match_env_build_env.
  (* match cont *)
  eapply match_Kcall_some with (sz := sz).
  econstructor; try edone. by rewrite Ecenv. edone. edone. edone.
Qed.

Lemma step_function_internal_no_stack_correct:
  forall ck optid f env k nenv s' vs
    (CC : ck = Cstacked.Kcall optid (Internal f) env k)
    (BE : build_env f = Some (nenv, 0%Z))
    (ND : NoDup (map (@fst _ _) (fn_variables f)))
    (MS : match_states (Cstacked.SKcall vs ck) s'),
   exists t' : St tlts,
      weakstep tlts s' TEtau t' /\
      match_states
        (SKbind f vs (map (@fst _ _) (Csharpminor.fn_params f)) 
           (mkcsenv None nenv) ck) t'.
Proof.
  intros. 
  rewrite <- pars_vars_eq_fn_variables in ND.
  inv MS; clarify; monadInv TF;
    pose proof (make_vars_norepet _ x.(fn_body) ND) as ND';
    apply nodup_app in ND'; destruct ND' as (NDv & NDp & DISJ).
    (* No return *)
    unfold transl_function, build_env in EQ.
    destruct (build_compilenv gce f) as [cenv sz] _eqn : Ecenv.
    destruct zle as [LT|]; [|done]. pose proof EQ as TFB.
    monadInv EQ. simpl in *.
    eexists. split.
      eapply weakstep_taustar.
        eapply step_weakstep.
        econstructor. edone. simpl. 
          eby eapply sym_eq, build_env_agree. 
          done. 
      eapply steptau_taustar. constructor.
    econstructor; unfold get_cenv; simpl; try rewrite Ecenv; simpl; try edone.
        (* bind_in_env *)
        by apply bind_env_disjoint, bind_in_env_set_params; 
          try apply list_disjoint_sym, DISJ.
      (* match_env *)
      eby eapply match_env_build_env.
    (* match cont *)
    eapply match_Kcall_none with (sz := sz).
    econstructor; try edone. by rewrite Ecenv. edone. edone.
  unfold transl_function, build_env in EQ.
  destruct (build_compilenv gce f) as [cenv sz] _eqn : Ecenv.
  destruct zle as [LT|]; [|done]. pose proof EQ as TFB.
  monadInv EQ. simpl in *.
  eexists. split.
    eapply weakstep_taustar.
      eapply step_weakstep.
      econstructor. edone. simpl. eby eapply sym_eq, build_env_agree. done. 
    eapply steptau_taustar. constructor.
  econstructor; unfold get_cenv; simpl; try rewrite Ecenv; simpl; try edone.
      (* bind_in_env *)
      by apply bind_env_disjoint, bind_in_env_set_params; 
        try apply list_disjoint_sym, DISJ.
    (* match_env *)
    eby eapply match_env_build_env.
  (* match cont *)
  eapply match_Kcall_some with (sz := sz).
  econstructor; try edone. by rewrite Ecenv. edone. edone. edone.
Qed.

Lemma step_stop_correct:
  forall env s'
  (MS : match_states (Cstacked.SKstmt Csharpminor.Sskip env Cstacked.Kstop) s'),
    exists t' : St tlts,
      weakstep tlts s' TEexit t' /\
      match_states (Cstacked.SKstmt Csharpminor.Sskip env Cstacked.Kstop) t'.
Proof.
  intros. inv MS. monadInv TEX.
  remember (Cstacked.Kstop) as st; revert Heqst.
  induction MK; intro E; try done.
    eexists; split; [apply step_weakstep; constructor|].
    by eapply match_SKstmt with (xenv := xenv); vauto.
  destruct (IHMK ME E) as [t' (WS & M)].
  by exists t'; split; [eapply steptau_weakstep|]; vauto. 
Qed.

Lemma step_next_correct:
  forall env s k s'
  (MS : match_states
         (Cstacked.SKstmt Csharpminor.Sskip env (Cstacked.Kseq s k)) s'),
    exists t' : St tlts,
      weakstep tlts s' TEtau t' /\ match_states (Cstacked.SKstmt s env k) t'.
Proof. 
  intros. inv MS. monadInv TEX.
  remember (Cstacked.Kseq s k) as st; revert s k Heqst.
  induction MK; intros; try done; 
    try (by eexists; (split; [apply step_weakstep|]); vauto).
  destruct (IHMK ME _ _ Heqst) as [t' (WS & M)].
  by exists t'; split; [eapply steptau_weakstep|]; vauto. 
Qed.
    
Lemma step_external_store_mem_correct:
  forall env tgt p c vres k s'
  (EVR : eval_var_ref (ge, gvare) env tgt p c)
  (MS : match_states (SKexternalReturn (Some tgt) vres env k) s'),
    exists t' : St tlts,
      exists v' : val,
        Val.lessdef (cast_value_to_chunk c vres) v' /\
        weakstep tlts s' (TEmem (MEwrite p c v')) t' /\
        match_states (Cstacked.SKstmt Csharpminor.Sskip env k) t'.
Proof.
  intros. inv MS. inv MK.
  (* assert (CCR := call_cont_related _ _ _ MK); rewrite CC in CCR; inv CCR. *)
  pose proof (ME tgt) as VM.
  inv EVR.
    (* Stack *)
    rewrite EG in VM. inv VM. unfold var_set in VS.
    rewrite EB in *; clarify.
    replace ((get_cenv k) !! tgt) with (Var_stack_scalar c offs) in VS.
    inv VS. unfold make_store, store_arg in *.
    eexists; eexists; split. eby eapply cast_value_to_chunk_lessdef.
    split.
      eapply steptau_weakstep. econstructor. eby symmetry. eby simpl.
      eapply steptau_weakstep. constructor. 
      eapply steptau_weakstep. constructor. 
      eapply steptau_weakstep. constructor. edone.
      eapply steptau_weakstep. constructor.
      eapply steptau_weakstep. constructor. eby rewrite PTree.gss.
      eapply step_weakstep. constructor.
    econstructor; try edone.
    eapply update_env_match_non_local. edone. 
    by replace ((get_cenv k) !! tgt) with (Var_stack_scalar c offs).
  (* Global *)
  rewrite EG in VM. inv VM; simpl in EGS; inv EGS.
    2 : by replace (gvare ! tgt) with (Some (Vscalar c)) in GVE.
  simpl in GFF; rewrite GVP in GFF; inv GFF.
  unfold var_set in VS. rewrite GVE in *. clarify.
  replace ((get_cenv k) !! tgt) with (Var_global_scalar c) in VS.
  inv VS. unfold make_store, store_arg in *.
  eexists; eexists; split. eby eapply cast_value_to_chunk_lessdef.
  split.
    eapply steptau_weakstep. econstructor. eby symmetry. eby simpl.
    eapply steptau_weakstep. constructor. 
    eapply steptau_weakstep. constructor. 
    eapply steptau_weakstep. 
      constructor. simpl. eby rewrite <- (proj1 TRANSF), GVP, Ptr.add_zero_r.
    eapply steptau_weakstep. constructor.
    eapply steptau_weakstep. constructor. eby rewrite PTree.gss.
    eapply step_weakstep. constructor.
  econstructor; try edone.
  eapply update_env_match_non_local. edone.
  by replace ((get_cenv k) !! tgt) with (Var_global_scalar c).
Qed.

Lemma step_external_store_env_correct:
  forall env tgt vres env' k s'
  (VLS : var_local_store env tgt vres env')
  (MS : match_states (SKexternalReturn (Some tgt) vres env k) s'),
    exists t' : St tlts,
      weakstep tlts s' TEtau t' /\
      match_states (Cstacked.SKstmt Csharpminor.Sskip env' k) t'.
Proof.
  intros.
  inv MS; inv VLS. inv MK. 
  pose proof (ME tgt) as VM. rewrite EG in VM. inv VM.
  unfold var_set in VS.
  replace ((get_cenv k) !! tgt) with (Var_local c) in VS.
  inv VS.
  destruct (make_cast_cont_taustar c (EKassign tgt tk0) (csenv_sp env) vres 
                                 (te !tgt <- vres)) as [v'' (TAU & LD')].
  eexists; split.
    eapply steptau_weakstep. econstructor. eby symmetry. eby simpl.
    eapply steptau_weakstep. econstructor. 
    eapply steptau_weakstep. econstructor. 
    eapply taustar_weakstep. apply make_cast_taustar_cont. 
    eapply steptau_weakstep. econstructor. eby rewrite PTree.gss.
    eapply taustar_weakstep. edone.
    apply step_weakstep. constructor. edone.
  econstructor; try edone. rewrite ptree_set_set.
  eapply update_env_match. edone. done.
    eapply lessdef_trans, LD'. by apply Val.load_result_lessdef.
Qed.

Lemma atomic_correct:
  forall optid astmt e es env k s'
   (MS : match_states
         (Cstacked.SKstmt (Csharpminor.Satomic optid astmt (e :: es)) env k)
         s'),
   (exists t' : St tlts,
      weakstep tlts s' TEtau t' /\
      match_states
        (Cstacked.SKexpr e env (Cstacked.EKatargs optid astmt es nil k)) t').
Proof.
  intros.
  inv MS.
  destruct optid; monadInv TEX; monadInv EQ.
    eexists; split.
      eapply steptau_weakstep. eby econstructor vauto.
      eapply step_weakstep. eby econstructor.
    eapply match_SKexpr; try edone.
    eby econstructor; vauto.
  eexists; split.
    eapply step_weakstep. eby econstructor.
  eapply match_SKexpr; try edone.
  eby econstructor; vauto.
Qed.

Lemma sem_atomic_statement_lessdef:
  forall astmt vs vs' p rmwi
  (SAS: sem_atomic_statement astmt vs = Some (p, rmwi))
  (LD : Val.lessdef_list vs vs'),
   sem_atomic_statement astmt vs' = Some (p, rmwi).
Proof.
  intros.
  destruct astmt; simpl in *.
  - destruct vs as [|[] [|? [|? []]]]; simpl in SAS; try done.
    inv LD. inv H1. inv H3. inv H4. inv H5.
    destruct Val.eq_dec; [done|].
    destruct (Val.has_type v0 Tint) as [] _eqn : HT1; [|done].
    destruct Val.eq_dec; [done|].
    destruct (Val.has_type v Tint) as [] _eqn : HT2; [|done].
    inv H1; [|done]. inv H2; [|done].
    inv SAS. rewrite HT1, HT2. 
    destruct Val.eq_dec; [done|].
    by destruct Val.eq_dec. 
  - destruct vs as [|[] [|? [|? []]]]; simpl in SAS; try done. 
    inv LD. inv H3. inv H1. done.
Qed.

Lemma cminorgen_step_correct:
  forward_sim_with_undefs2 slts tlts match_states order.
Proof.
  intros s s' l t ST MS.
  (cst_step_cases (destruct ST) Case);
    (* Generic handler of trivial cases *)
    first [ Case "StepExternalStoreNone" | 
      try (inv MS; try inv MACK; first [monadInv TEX | inv MK; try inv MACK];
        by right; right; eexists; split; [apply step_weakstep|]; vauto)];
    (* Get rid of handling of conditionals *)
    try (pose proof BOV; by inv MS; try (by inv MACK); []; inv MK; try (by inv MACK); [];
      by inv LD; [right; right; eexists; split; [apply step_weakstep|]; vauto| inv BOV]).

  Case "StepVarLocal".
    eby right; right; eapply step_var_local_correct. 

  Case "StepVarStack".
    eby right; eapply step_var_stack_correct.

  Case "StepAddrOf".
    eby right; right; eapply step_addr_correct.
  
  Case "StepConst".
    by inv MS; inv TEX; destruct cst;
      (right; right; eexists; split; [apply step_weakstep|]; vauto).

  Case "StepUnop1".
    inv MS; monadInv TEX.
      by right; right; eexists; split; [apply step_weakstep|]; vauto.
    (* Cast-assign elimination *)
    eby right; left; inv MACK; repeat (split; [done|]); econstructor; try edone;
       (eapply match_cast_assign; [|econstructor]).

  Case "StepUnop".
    eby right; eapply step_unop_correct.

  Case "StepBinop".
    inv MS; [|by inv MACK]; inv MK; [|by inv MACK].
    destruct (eval_binop_lessdef EB LD0 LD) as [x (EB' & LD')].
    right; right; eexists; split; [apply step_weakstep|]; vauto.

  Case "StepLoad".
    inv MS; [|by inv MACK]; inv MK; [|by inv MACK].
    inv LD.
    right. eexists. split. 
      apply step_weakstep. eby econstructor. 
    eby intros v' LD; inv LD; eexists; split; econstructor.
  
  Case "StepSkipBlock".
    by right; right; apply match_StepSkipBlock, MS.

  Case "StepAssign1".
    eby right; right; eapply step_assign_correct.

  Case "StepAssignEnv".
    eby right; eapply step_assign_env_correct.

  Case "StepAssignLocal".
    eby right; right; eapply step_assign_local_correct.

  Case "StepStore2".
    inv MS; [|by inv MACK]; inv MK; [by inv MACK|].
    right; right; eexists; split.
      apply step_weakstep. constructor.
    destruct (transl_is_store_arg_dest chunk TEX) as [-> | [e'[o' (-> & CCE)]]].
      econstructor; try edone. 
      by econstructor vauto.
    simpl in TEX. monadInv TEX.
    eapply  match_SKexpr_assign; [| edone | edone | edone | ].
    by simpl; rewrite EQ; inv CCE.
    eby econstructor.

  Case "StepStore".
    eby right; eapply step_store_correct.

  Case "StepCall".
    eby right; right; eapply step_call_correct.

  Case "StepEmptyCall".
    eby right; right; eapply step_empty_call_correct.

  Case "StepCallArgs1". 
    eby right; right; eapply step_call_args1_correct.

  Case "StepCallArgs2".
    eby right; right; eapply step_call_args2_correct.

  Case "StepCallArgs".
    eby right; right; eapply step_call_args_correct.

  Case "StepAtomic".
    eby right; right; eapply atomic_correct.

  Case "StepAtomicArgs".
    right; right.
    inv MS; [|inv MACK]. inv MK; [|inv MACK].
    monadInv TEXL.
    eexists; split; [eapply step_weakstep|];
      econstructor vauto.
    econstructor vauto. edone.
    eby eapply lessdef_list_app; vauto.

  Case "StepAtomicFinishNone".
    inv MS; [|inv MACK]. inv MK; [|inv MACK]. monadInv TEXL.
    right.
    eexists; split. 
      eapply step_weakstep. 
      econstructor vauto.
      eapply sem_atomic_statement_lessdef. edone.
      eby eapply lessdef_list_app; vauto.
    intros vd' LD'.
    eexists; split. 
      eby econstructor vauto; eapply Val.has_type_lessdef.
    inv MEK.
    eby econstructor vauto.

  Case "StepAtomicFinishSome".
    inv MS; [|inv MACK]. inv MK; [|inv MACK]. monadInv TEXL.
    inv MEK.
    right.
    eexists; split. 
      eapply step_weakstep. 
      econstructor vauto.
      eapply sem_atomic_statement_lessdef. edone.
      eby eapply lessdef_list_app; vauto.
    intros vd' LD'.
    eexists; split. 
      eby econstructor vauto; eapply Val.has_type_lessdef.
    econstructor vauto. 

  Case "StepFence".
    right. inv MS. monadInv TEX.
    by eexists; split; [eapply step_weakstep|]; vauto. 

  Case "StepSeq".
    inv MS. monadInv TEX.
      eby right; right; eexists; split; [eapply step_weakstep|]; 
        econstructor vauto.
    right; left. split. done.
    eby econstructor.
      
  Case "StepLoop".
    inv MS. monadInv TEX.
    right; right; eexists; split.
      eapply step_weakstep. constructor.
    by econstructor; try edone; econstructor; try edone; simpl; rewrite EQ.
  
  Case "StepExitSeq".
    eby right; right; eapply step_exit_seq_correct.

  Case "StepExitBlock".
    eby right; right; eapply step_exit_block_correct.

  Case "StepExitBlock1".
    eby right; right; eapply step_exists_block1_correct.

  Case "StepSwitch".
    eby right; right; eapply step_switch_correct.

  Case "StepSelect".
    eby right; right; eapply step_select_correct.

  Case "StepGoto".
    eby right; right; eapply step_goto_correct.

  Case "StepReturnNone".
    inv MS. (* pose proof (is_noreturn_call_cont_pres _ _ _ MK CC). *)
    right; left; monadInv TEX; split; vauto. 
  
  Case "StepReturnFree".
    inv MS; assert (CCR := call_cont_related _ _ _ MK); rewrite CC in CCR;
      inv CCR; monadInv TB; right; eexists; (split; 
        [ by apply step_weakstep; apply sym_eq in H; vauto|
          eby econstructor]). 
    
  Case "StepReturnNoFree".
    inv MS; assert (CCR := call_cont_related _ _ _ MK); rewrite CC in CCR;
      inv CCR; monadInv TB; right; right; eexists; (split;
        [by apply step_weakstep; apply sym_eq in H; vauto |
         eby econstructor]). 

  Case "StepReturnNoneFinish".
    inv MS.
    assert (CCR := call_cont_related _ _ _ MK); rewrite CC in CCR; inv CCR.
    right; right; eexists; split.
      eby apply step_weakstep; econstructor; [symmetry|simpl].
    eby econstructor.

  Case "StepReturnSome".    
    inv MS. monadInv TEX.
    assert (TB: exists tfn, exists sz, 
      transl_funbody (fst (build_compilenv gce f)) sz f = OK tfn /\
      get_fundef (call_cont tk) = Some (Internal tfn)).
      by assert (CCR := call_cont_related _ _ _ MK); inv CCR;
        match goal with H : _ = Cstacked.call_cont _ |- _ => 
          rewrite <- H in CC end; inv CC; vauto.
    destruct TB as [tfn [sz (TB & CC')]].
    right; right; eexists; split.
      apply step_weakstep; econstructor; [eby rewrite CC'|].
      by monadInv TB.
    econstructor. edone. edone. edone.
    eby eapply match_EKreturn. 

  Case "StepReturnSome1".
    inv MS; [|by inv MACK]. inv MK; [by inv MACK|].
    right; left; split. done.
    destruct (Cstacked.call_cont k) as [] _eqn:CK; inv CC.
    eby eapply match_SKfree_some. 

  Case "StepReturnFinishLocal".
    eby right; right; eapply step_return_finish_local_correct.

  Case "StepReturnFinishStack".
    eby right; eapply step_return_finish_mem_correct.

  Case "StepFunctionInternalNoStack".
    eby right; right; eapply step_function_internal_no_stack_correct.
    
  Case "StepFunctionInternalWithStack".
    eby right; eapply step_function_internal_with_stack_correct.

  Case "StepBindArgsEnv".
    eby right; right; eapply step_bind_args_env_correct.

  Case "StepBindArgsStack".
    eby right; eapply step_bind_args_stack_correct.

  Case "StepTransferFun".
    inv MS. destruct pars; [| done]. inv Eps.
    right; right; eexists; split.
      eapply step_weakstep. constructor.
      (*eapply steptau_weakstep. constructor.*)
    eby econstructor.

  Case "StepExternalCall".
    by inv MS; apply lessdef_map_val_of_eval in LD; monadInv TF;
      right; eexists; (split; [apply step_weakstep|]); vauto.
  
  Case "StepExternalReturn".
    inv MS.
    right; eexists; split.
      apply step_weakstep. eby econstructor.
    eby econstructor. 

  Case "StepExternalStoreStack".
    eby right; eapply step_external_store_mem_correct.

  Case "StepExternalStoreEnv".
    eby right; right; eapply step_external_store_env_correct.

  Case "StepExternalStoreNone".
    inv MS. inv MK.
    right; right. eexists; split.
      apply step_weakstep. eby econstructor. 
    eby econstructor. 

  Case "StepNext".
    eby right; right; eapply step_next_correct.

  Case "StepStop".
    eby right; eapply step_stop_correct.
    
  Case "StepThreadFn".
    inv MS; [|by inv MACK]. inv MK; [by inv MACK|]. inv LD.
    by right; right; eexists; (split; [apply step_weakstep|]); vauto.

  Case "StepThreadEvt".
    inv MS; [|by inv MACK]. inv MK; [by inv MACK|].
    assert (Val.lessdef_list (v :: nil) (v' :: nil)). vauto.
    right. eexists; eexists; split. edone.
    split.
      apply step_weakstep. constructor.
    eby econstructor.
Qed.

Definition bsim_rel := @bsr _ slts tlts match_states.
Definition bsim_order := @bsc _ tlts.

Lemma cst_cm_backward_sim:
  @backward_sim_with_undefs _ slts tlts te_ldo te_ldi 
                           bsim_rel bsim_order.
Proof.
  apply (@forward_to_backward_sim_with_undefs thread_labels slts tlts
          (cst_receptive (ge, gvare)) (cm_determinate tge) 
          (cst_progress_dec (ge, gvare)) 
          te_ldo te_ldi ldo_samekind_eq ldo_not_tau ldi_refl 
          match_states order).
  apply mk_forward_sim_with_undefs. apply well_founded_ltof.
  apply cminorgen_step_correct.
Qed.

Lemma cshmgen_init:
  forall p vs vs'
    (LD : Val.lessdef_list vs vs'),
    match Cstacked.cst_init (ge, gvare) p vs, cm_init tge p vs' with
      | Some s, Some t => match_states s t
      | None, None => True
      | _, _ => False
    end.
Proof.
  intros.
  unfold cst_init, cm_init, Cstacked.ge; simpl.
  pose proof TRANSF as [_ FP]. specialize (FP p).
  destruct (Genv.find_funct_ptr ge p) as [] _eqn : Ef;
    destruct (Genv.find_funct_ptr tge p); try done; [].
  destruct f; destruct f0; try done; pose proof FP as FP'; monadInv FP.
  destruct f; destruct f0; try done.  
  unfold transl_function in EQ. simpl in *. 
  destruct build_compilenv; destruct zle; try done. monadInv EQ.
  rewrite !(Val.lessdef_list_length LD). destruct beq_nat; [|done].
  eapply match_SKcall_none with (xenv := nil); vauto.
  by apply Val.conv_list_lessdef.
  apply match_env_gce.
Qed.

End TRANSLATION.


Definition full_genv_rel (sge : cst_sem.(SEM_GE)) 
                         (tge : cm_sem.(SEM_GE)) : Prop :=
  exists prog, 
    genv_rel prog (fst sge) tge /\
    snd sge = global_var_env prog /\
    forall id, In id (map (fun x => fst (fst x)) (prog_vars prog)) -> 
               Genv.find_symbol (fst sge) id <> None.

Definition cst_cm_match_prg (prog : cst_sem.(SEM_PRG)) 
                            (tprog : cm_sem.(SEM_PRG)) : Prop := 
  transl_program prog = OK tprog.

Definition full_bsim_rel (ge : SEM_GE cst_sem) (tge : SEM_GE cm_sem)
                         (cms : SEM_ST cm_sem) (css : SEM_ST cst_sem)  :=
  exists prog, 
    snd ge = global_var_env prog /\
    genv_rel prog (fst ge) tge /\
    (forall id, In id (map (fun x => fst (fst x)) (prog_vars prog)) -> 
                Genv.find_symbol (fst ge) id <> None) /\
    bsim_rel prog (fst ge) tge cms css.

Theorem cst_cminor_sim :
  Sim.sim tso_mm tso_mm cst_sem cm_sem cst_cm_match_prg.
Proof.
  eapply (TSOsim_with_undefs.sim _ _ full_genv_rel 
                                 full_bsim_rel (fun _ => bsim_order)); intros; 
    simpl.
  - destruct GENVR as [prg ((GR & FR) & _)].
    rewrite GR.
    by rewrite (transform_partial_program2_main _ _ _ MP).
  - simpl in *; unfold cst_cm_match_prg, transl_program in MP.
    pose proof (transform_partial_program2_match _ _ _ MP) as MPRG.
    destruct (Genv.exists_matching_genv_and_mem_rev MPRG INIT)
      as [sge (SGEINIT & GENVM)].
    exists (sge, global_var_env src_prog).
    split. by vauto. 
    exists src_prog. 
    split. done. 
    split. done.
    intros id IN; eby eapply Genv.in_prog_find_symbol. 
  - destruct GENVR as [prog (GER & GVE & INP)].
    pose proof (cshmgen_init _ _ _ GER INP fnp _ _ LD) as SHI.
    simpl in INIT; rewrite INIT in SHI. 
    destruct sge; simpl in *; subst.
    destruct cst_init; [|done].
    eexists. split. edone.
    exists prog. 
    split. done. 
    split. done. 
    split. done.
    by apply fsr_in_bsr.
  - destruct GENVR as [prog (GER & GVE & INP)].
    pose proof (cshmgen_init _ _ _ GER INP fnp _ _ LD) as SHI.
    simpl in INITF; rewrite INITF in SHI. 
    destruct sge; simpl in *; subst.
    by destruct cst_init. 
  - destruct GENR as [prog (GER & _ & INP)].
    pose proof (cst_cm_backward_sim _ _ _ GER INP) as (WF & _ & _).
    clear GER INP.
    split. done.
    split. 
      intros until 0. intros STUCK SIM.
      destruct SIM as [p' (E & GER' & INP' & SIM')].
      destruct (cst_cm_backward_sim _ _ _ GER' INP')
        as (_ & SS' & _); destruct sge; simpl in *; subst.
      eby eapply SS'. 
    intros until 0. intros ST BR.
    destruct BR as [p' (E & GER' & INP' & BS')].
    destruct (cst_cm_backward_sim _ _ _ GER' INP') as (_ & _ & SIM).
    destruct sge; simpl in *. rewrite E.
    destruct (SIM _ _ _ _ ST BS') as [(ISTAU & SR & ORD) | 
     [ERROR | [[s' [l' (LDO & TAU & SR)]] | LDIIMPL]]].
    (* Stutter *)
    left. split. done. split. eby eexists p'. done.
    (* Error *)
    by right; left.
    (* LDO step *)
    right; right; left.
    eexists; eexists; split. edone. split. edone. eby eexists.
    (* LDI step *)
    right; right; right. intros l'' LDI.
    destruct (LDIIMPL _ LDI) as [s' (TAU & SR)].
    exists s'. split. edone. eby eexists.
Qed.
