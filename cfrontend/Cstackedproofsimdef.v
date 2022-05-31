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

Require Import Coqlib.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Pointers.
Require Import Events.
Require Import Globalenvs.
Require Import Libtactics.
Require Import TSOmachine.
Require Cminor.
Require Import Cminorgen.
Require Import Cstacked.
Require Import Csharpminor.
Require Import Simulations.
Require Import Mem.
Require Import Memeq.
Require Import Memcomp.
Require Import Permutation.

Section SIMS.

Variable cst_globenv : genv * gvarenv.
Variable csm_globenv : genv * gvarenv.

Definition machine_ptr (p : pointer) :=
  let (b, ofs) := p in low_mem_restr b = true.

Definition scratch_ptr (p : pointer) :=
  let (b, ofs) := p in low_mem_restr b = false.

Let cshm_lts := (mklts event_labels (Comp.step tso_mm cs_sem csm_globenv)).
Let cst_lts := (mklts event_labels (Comp.step tso_mm cst_sem cst_globenv)).

Definition can_reach_error shms :=
    exists shms', taustar cshm_lts shms shms' /\
                  can_do_error cshm_lts shms'.


Section ENV_REL.


Definition machine_val (v : val) := 
  match v with
    | Vptr p => machine_ptr p
    | _ => True         
  end.

(** * Simulation relation definition *)

(** Thread state relation:
      - for each thread, states are related if 
        - all environments in the states are related, i.e.
          - each local variable in Cstacked is equal to its memory cell
            in C#minor
          - for on-stack variables, the (stack pointer + offset) in Cstacked
            must be the same as the pointer in C#minor environment
        - otherwise, the structure of the states must be the same and
          no value in any state can be a pointer to scratch memory
*)

(* Definition scratch_vals := Z -> option (val * memory_chunk). *)

Definition scratch_vals := mem.

Definition load_result_invariant (c : memory_chunk) (v : val) : Prop := 
  Val.load_result c v = v.

Inductive env_item_related : scratch_vals ->       (* C#minor 'scratch' values *)
                             Z ->                  (* frame size *)
                             option pointer ->     (* frame pointer *)
                             Cstacked.env_item ->  (* Cstacked environment 
                                                      entry *)
                             pointer * var_kind -> (* C#minor env entry *)
                             Prop :=
| env_item_related_local: forall p v c svals fs sp
  (LV  : load_ptr c svals p = Some v)
  (SP  : scratch_ptr p)
  (VT  : Val.has_type v (type_of_chunk c))
  (VAR : valid_alloc_range (range_of_chunk p c))
  (*ALG : pointer_chunk_aligned p c*) (* TODO : to be removed when valid_alloc_range contains alignment *)
  (LRV : load_result_invariant c v), 
  env_item_related svals
                   fs sp 
                   (Cstacked.Env_local v c) 
                   (p, Vscalar c) 
| env_item_related_scalar: forall svals fs sp c offs
  (OLB: offs >= 0)
  (OHB: offs + (size_chunk c) <= fs),
  env_item_related svals
                   fs (Some sp)
                   (Cstacked.Env_stack_scalar c offs)
                   (MPtr.add sp (Int.repr offs), Vscalar c)
| env_item_related_array: forall svals fs sp offs size
  (OLB: offs >= 0)
  (OHB: offs + (Zmax 1 size) <= fs),
  env_item_related svals
                   fs (Some sp)
                   (Cstacked.Env_stack_array offs)
                   (MPtr.add sp (Int.repr offs), Varray size).

Definition partitioning := positive -> list arange.

Definition csm_env_item_range (ei : pointer * var_kind) : arange :=
  (fst ei, Int.repr(sizeof(snd ei))).

Definition env_ranges (csm_env : Csharpminor.env) : list arange :=
  map (fun ei => csm_env_item_range (snd ei)) 
      (PTree.elements csm_env).

Definition partitioning_disjoint (part : partitioning) : Prop :=
  forall x y, x <> y -> range_lists_disjoint (part x) (part y).

Definition env_items_related (fsize : int)
                             (csm_vals : scratch_vals) 
                             (cst_env : Cstacked.env) 
                             (csm_env : Csharpminor.env): Prop :=
    forall id, 
      match PTree.get id cst_env.(Cstacked.csenv_env), PTree.get id csm_env with
        | Some ei1, Some ei2 => 
          env_item_related csm_vals
                           (Int.unsigned fsize)
                           cst_env.(Cstacked.csenv_sp) 
                           ei1 ei2
        | None, None => True
        | _ , _ => False
      end.
                         
Definition env_related (cst_obs : list arange)   (csm_obs : list arange)
                       (csm_vals : scratch_vals) 
                       (cst_env : Cstacked.env) (csm_env : Csharpminor.env): Prop :=
  exists n,
    match cst_env.(Cstacked.csenv_sp) with
      | Some sp => valid_alloc_range (sp, n) /\ cst_obs = (sp, n) :: nil /\
                   csm_obs <> nil
      | None => n = Int.zero /\ cst_obs = nil
    end /\
    range_list_disjoint csm_obs /\
    Permutation csm_obs (env_ranges csm_env) /\
    env_items_related n csm_vals cst_env csm_env.

Inductive cont_related : list arange      ->  (* Cstacked allocs *)
                         list arange      ->  (* C#minor allocs *)
                         scratch_vals     ->  (* C#minor scratch vals *)
                         Cstacked.cont    -> 
                         Csharpminor.cont -> 
                         Prop :=
  | k_rel_call_stop: forall svals cst_e csm_e (fd : fundef)
      (FINP: exists p, Genv.find_funct (Cstacked.ge cst_globenv) p = Some fd),
      cont_related nil
                   nil
                   svals
                   (Cstacked.Kcall None fd cst_e Cstacked.Kstop)
                   (Csharpminor.Kcall None fd csm_e Csharpminor.Kstop)
  | k_rel_seq: forall cst_obs csm_obs svals cst_k csm_k stmt
      (KR: cont_related cst_obs csm_obs svals cst_k csm_k),
      cont_related cst_obs csm_obs svals
                   (Cstacked.Kseq stmt cst_k)
                   (Csharpminor.Kseq stmt csm_k) 
  | k_rel_block: forall cst_obs csm_obs svals cst_k csm_k
      (KR: cont_related cst_obs csm_obs svals cst_k csm_k),
      cont_related cst_obs csm_obs svals
                   (Cstacked.Kblock cst_k)
                   (Csharpminor.Kblock csm_k) 
  | k_rel_call: forall cst_obs csm_obs svals cst_obs' csm_obs'
                       cst_k csm_k id cst_e csm_e (fd : fundef)
      (KR: cont_related cst_obs csm_obs svals 
                        cst_k csm_k)
      (ER: env_related cst_obs' csm_obs' svals cst_e csm_e)
      (CSRLD: range_lists_disjoint cst_obs cst_obs')
      (CMRLD: range_lists_disjoint csm_obs csm_obs')
      (FINP: exists p, Genv.find_funct (Cstacked.ge cst_globenv) p = Some fd),
      cont_related (cst_obs' ++ cst_obs)
                   (csm_obs' ++ csm_obs)
                   svals
                   (Cstacked.Kcall id fd cst_e cst_k)
                   (Csharpminor.Kcall id fd csm_e csm_k).

Definition machine_val_list (l : list val) : Prop :=
  forall v, In v l -> machine_val v.

Inductive expr_cont_related : list arange      ->  (* Cstacked allocs *)
                              list arange      ->  (* C#minor allocs *)
                              scratch_vals     ->  (* C#minor scratch vals *)
                              list pointer     ->  (* Cstacked environment ptrs *)
                              list pointer     ->  (* C#minor environment ptrs *)
                              Cstacked.expr_cont    -> 
                              Csharpminor.expr_cont -> 
                              Prop :=
  | ek_rel_unop: forall cst_obs csm_obs svals cst_ep csm_ep op cst_ek csm_ek
      (EKR: expr_cont_related cst_obs csm_obs svals cst_ep csm_ep cst_ek csm_ek),
      expr_cont_related cst_obs csm_obs svals cst_ep csm_ep
                        (Cstacked.EKunop op cst_ek)
                        (Csharpminor.EKunop op csm_ek)
  | ek_rel_binop1: forall cst_obs csm_obs svals cst_ep csm_ep op e cst_ek 
                          csm_ek
      (EKR: expr_cont_related cst_obs csm_obs svals cst_ep csm_ep cst_ek csm_ek),
      expr_cont_related cst_obs csm_obs svals cst_ep csm_ep
                        (Cstacked.EKbinop1 e op cst_ek)
                        (Csharpminor.EKbinop1 e op csm_ek) 
  | ek_rel_binop2: forall cst_obs csm_obs svals cst_ep csm_ep op v cst_ek 
                          csm_ek
      (EKR: expr_cont_related cst_obs csm_obs svals cst_ep csm_ep cst_ek csm_ek)
      (MV: machine_val v),
      expr_cont_related cst_obs csm_obs svals cst_ep csm_ep
                        (Cstacked.EKbinop2 op v cst_ek)
                        (Csharpminor.EKbinop2 op v csm_ek) 
  | ek_rel_load: forall cst_obs csm_obs svals cst_ep csm_ep c cst_ek csm_ek
      (EKR: expr_cont_related cst_obs csm_obs svals cst_ep csm_ep cst_ek csm_ek),
      expr_cont_related cst_obs csm_obs svals cst_ep csm_ep 
                        (Cstacked.EKload c cst_ek)
                        (Csharpminor.EKload c csm_ek)
  | ek_rel_call: forall cst_obs csm_obs svals cst_ep csm_ep id sig args 
                        cst_k csm_k
      (EK: cont_related cst_obs csm_obs svals cst_k csm_k),
      expr_cont_related cst_obs csm_obs svals cst_ep csm_ep
                        (Cstacked.EKcall id sig args cst_k)
                        (Csharpminor.EKcall id sig args csm_k) 
  | ek_rel_args: forall cst_obs csm_obs svals cst_ep csm_ep id fd args vargs
                        cst_k csm_k sig
      (KR: cont_related cst_obs csm_obs svals cst_k csm_k)
      (*FINP: exists id, In (id, fd) prg.(prog_funct)*)
      (MVL: machine_val_list vargs),
      expr_cont_related cst_obs csm_obs svals cst_ep csm_ep
                        (Cstacked.EKargs id fd sig args vargs cst_k)
                        (Csharpminor.EKargs id fd sig args vargs csm_k) 
  | ek_rel_atargs: forall cst_obs csm_obs svals cst_ep csm_ep astmt args vargs
                        cst_k csm_k sig
      (KR: cont_related cst_obs csm_obs svals cst_k csm_k)
      (*FINP: exists id, In (id, fd) prg.(prog_funct)*)
      (MVL: machine_val_list vargs),
      expr_cont_related cst_obs csm_obs svals cst_ep csm_ep
                        (Cstacked.EKatargs astmt sig args vargs cst_k)
                        (Csharpminor.EKatargs astmt sig args vargs csm_k) 
  | ek_rel_cond: forall cst_obs csm_obs  svals cst_ep csm_ep e1 e2 cst_ek 
                        csm_ek
      (EKR: expr_cont_related cst_obs csm_obs svals cst_ep csm_ep cst_ek csm_ek),
      expr_cont_related cst_obs csm_obs svals cst_ep csm_ep
                        (Cstacked.EKcond e1 e2 cst_ek)
                        (Csharpminor.EKcond e1 e2 csm_ek) 
  | ek_rel_assign: forall cst_obs csm_obs svals cst_ep csm_ep id cst_k csm_k
      (KR: cont_related cst_obs csm_obs svals cst_k csm_k),
      expr_cont_related cst_obs csm_obs  svals cst_ep csm_ep
                        (Cstacked.EKassign id cst_k)
                        (Csharpminor.EKassign id csm_k) 
  | ek_rel_thread1: forall cst_obs csm_obs svals cst_ep csm_ep e cst_k csm_k
      (KR: cont_related cst_obs csm_obs svals cst_k csm_k),
      expr_cont_related cst_obs csm_obs svals cst_ep csm_ep
                        (Cstacked.EKthread1 e cst_k)
                        (Csharpminor.EKthread1 e csm_k) 
  | ek_rel_thread2: forall cst_obs csm_obs svals cst_ep csm_ep p cst_k csm_k
      (KR: cont_related cst_obs csm_obs svals cst_k csm_k),
      expr_cont_related cst_obs csm_obs svals cst_ep csm_ep
                        (Cstacked.EKthread2 p cst_k)
                        (Csharpminor.EKthread2 p csm_k) 
  | ek_rel_condstmt: forall cst_obs csm_obs svals cst_ep csm_ep s1 s2 cst_k 
                            csm_k
      (KR: cont_related cst_obs csm_obs svals cst_k csm_k),
      expr_cont_related cst_obs csm_obs  svals cst_ep csm_ep
                        (Cstacked.EKcondstmt s1 s2 cst_k)
                        (Csharpminor.EKcondstmt s1 s2 csm_k) 
  | ek_rel_switch: forall cst_obs csm_obs svals cst_ep csm_ep ls cst_k csm_k
      (KR: cont_related cst_obs csm_obs  svals cst_k csm_k),
      expr_cont_related cst_obs csm_obs svals cst_ep csm_ep
                        (Cstacked.EKswitch ls cst_k)
                        (Csharpminor.EKswitch ls csm_k) 
  | ek_rel_return: forall cst_obs csm_obs svals cst_ep csm_ep cst_k csm_k
      (KR: cont_related cst_obs csm_obs svals cst_k csm_k),
      expr_cont_related cst_obs csm_obs svals cst_ep csm_ep
                        (Cstacked.EKreturn cst_k)
                        (Csharpminor.EKreturn csm_k) 
  | ek_rel_storeaddr: forall cst_obs csm_obs svals cst_ep csm_ep c e cst_k csm_k
      (KR: cont_related cst_obs csm_obs svals cst_k csm_k),
      expr_cont_related cst_obs csm_obs svals cst_ep csm_ep
                        (Cstacked.EKstoreaddr c e cst_k)
                        (Csharpminor.EKstoreaddr c e csm_k) 
  | ek_rel_storeval: forall cst_obs csm_obs svals cst_ep csm_ep c e cst_k csm_k
      (KR: cont_related cst_obs csm_obs svals cst_k csm_k)
      (MV: machine_val e),
      expr_cont_related cst_obs csm_obs svals cst_ep csm_ep
                        (Cstacked.EKstoreval c e cst_k)
                        (Csharpminor.EKstoreval c e csm_k).

Definition partition_injective  (tp : list arange)
                                (sp : list arange) : Prop :=
  forall p n,
    machine_ptr p ->
    In (p, n) sp ->
    exists r', range_inside (p, n) r' /\
               In r' tp.

Inductive state_related : list arange -> 
                          list arange ->
                          scratch_vals ->
                          Cstacked.state -> 
                          Csharpminor.state -> Prop :=
  | st_rel_expr: forall cst_obs csm_obs svals cst_obs' csm_obs' e
                        cst_e csm_e cst_ek csm_ek
      (EKR: expr_cont_related cst_obs csm_obs 
                              svals 
                              (map (@fst _ _) cst_obs')
                              (map (@fst _ _) csm_obs')
                              cst_ek csm_ek)
      (ER: env_related cst_obs' csm_obs' svals cst_e csm_e)
      (CSRLD: range_lists_disjoint cst_obs cst_obs')
      (CMRLD: range_lists_disjoint csm_obs csm_obs'),
      state_related (cst_obs' ++ cst_obs) (csm_obs' ++ csm_obs)
                    svals
                    (Cstacked.SKexpr e cst_e cst_ek)
                    (Csharpminor.SKexpr e csm_e csm_ek)
  | st_rel_stmt: forall cst_obs csm_obs svals cst_obs' csm_obs' s
                        cst_e csm_e cst_k csm_k
      (EKR: cont_related cst_obs csm_obs 
                              svals 
                              cst_k csm_k)
      (ER: env_related cst_obs' csm_obs' svals cst_e csm_e)
      (CSRLD: range_lists_disjoint cst_obs cst_obs')
      (CMRLD: range_lists_disjoint csm_obs csm_obs'),
      state_related (cst_obs' ++ cst_obs) (csm_obs' ++ csm_obs)
                    svals
                    (Cstacked.SKstmt s cst_e cst_k)
                    (Csharpminor.SKstmt s csm_e csm_k)
  | st_rel_val: forall cst_obs csm_obs svals cst_obs' csm_obs' e 
                       cst_e csm_e cst_ek csm_ek
      (EKR: expr_cont_related cst_obs csm_obs 
                              svals 
                              (map (@fst _ _) cst_obs')
                              (map (@fst _ _) csm_obs')
                              cst_ek csm_ek)
      (ER: env_related cst_obs' csm_obs' svals cst_e csm_e)
      (MV: machine_val e)
      (CSRLD: range_lists_disjoint cst_obs cst_obs')
      (CMRLD: range_lists_disjoint csm_obs csm_obs'),
      state_related (cst_obs' ++ cst_obs) (csm_obs' ++ csm_obs)
                    svals
                    (Cstacked.SKval e cst_e cst_ek)
                    (Csharpminor.SKval e csm_e csm_ek)
  | st_rel_call: forall cst_obs csm_obs svals vs cst_k csm_k
      (KR: cont_related cst_obs csm_obs 
                        svals 
                        cst_k csm_k)
      (MVL: machine_val_list vs),
      state_related cst_obs csm_obs svals
                    (Cstacked.SKcall vs cst_k)
                    (Csharpminor.SKcall vs csm_k)
(*  | st_rel_nextstmt: forall cst_obs csm_obs svals cst_obs' csm_obs'
                            cst_e csm_e cst_k csm_k
      (KR: cont_related cst_obs csm_obs 
                        svals 
                        cst_k csm_k)
      (ER: env_related cst_obs' csm_obs' svals cst_e csm_e)
      (CSRLD: range_lists_disjoint cst_obs cst_obs')
      (CMRLD: range_lists_disjoint csm_obs csm_obs'),
      state_related (cst_obs' ++ cst_obs) (csm_obs' ++ csm_obs)
                    svals
                    (Cstacked.SKnextstmt cst_e cst_k)
                    (Csharpminor.SKnextstmt csm_e csm_k) *)
  | st_rel_skipstmt_stop: forall svals cst_e csm_e,
      state_related nil nil
                    svals
                    (Cstacked.SKstmt Sskip cst_e Cstacked.Kstop)
                    (Csharpminor.SKstmt Sskip csm_e Csharpminor.Kstop)
  | st_rel_free: forall cst_obs csm_obs svals cst_obs' csm_obs'
                        csm_e cst_k csm_k ov op lp
      (KR: cont_related cst_obs csm_obs svals cst_k csm_k)
      (MV: match ov with Some v => machine_val v | None => True end)
      (PI: partition_injective cst_obs' csm_obs')
      (OP: match op with
             | Some p => map (@fst _ _) cst_obs' = p :: nil /\ 
                         csm_obs' <> nil
             | None => cst_obs' = nil
           end)
      (P: Permutation (map (@fst _ _) csm_obs') lp)
      (CSRLD: range_lists_disjoint cst_obs cst_obs')
      (CMRLD: range_lists_disjoint csm_obs csm_obs'),
      state_related (cst_obs' ++ cst_obs) (csm_obs' ++ csm_obs)
                    svals
                    (SKfree op ov cst_k)
                    (Csharpminor.SKstmt Sskip csm_e 
                                            (Csharpminor.Kfree lp ov csm_k))
  | st_rel_return: forall cst_obs csm_obs svals csm_e cst_k csm_k ov
      (KR: cont_related cst_obs csm_obs svals cst_k csm_k)
      (MV: match ov with Some v => machine_val v | None => True end),
      state_related cst_obs csm_obs
                    svals
                    (SKreturn ov cst_k)
                    (Csharpminor.SKstmt Sskip csm_e 
                                            (Csharpminor.Kfree nil ov csm_k))    
  | st_rel_bind: forall cst_obs csm_obs svals cst_obs' csm_obs'
                        f vs ids cst_e csm_e cst_k csm_k
      (KR: cont_related cst_obs csm_obs 
                        svals 
                        cst_k csm_k)
      (ER: env_related cst_obs' csm_obs' svals cst_e csm_e)
      (MVL: machine_val_list vs)
      (CSRLD: range_lists_disjoint cst_obs cst_obs')
      (CMRLD: range_lists_disjoint csm_obs csm_obs'),
      state_related (cst_obs' ++ cst_obs) (csm_obs' ++ csm_obs)
                    svals
                    (Cstacked.SKbind f vs ids cst_e cst_k)
                    (Csharpminor.SKbind f vs ids csm_e csm_k)
  | st_rel_external: forall cst_obs csm_obs svals cst_obs' csm_obs'
                            sig id cst_e csm_e cst_k csm_k
      (KR: cont_related cst_obs csm_obs 
                        svals 
                        cst_k csm_k)
      (ER: env_related cst_obs' csm_obs' svals cst_e csm_e)
      (CSRLD: range_lists_disjoint cst_obs cst_obs')
      (CMRLD: range_lists_disjoint csm_obs csm_obs'),
      state_related (cst_obs' ++ cst_obs) (csm_obs' ++ csm_obs)
                    svals
                    (Cstacked.SKexternal sig id cst_e cst_k)
                    (Csharpminor.SKexternal sig id csm_e csm_k)
  | st_rel_external_return: forall cst_obs csm_obs svals cst_obs' csm_obs'
                                   id v cst_e csm_e cst_k csm_k
      (KR: cont_related cst_obs csm_obs 
                        svals 
                        cst_k csm_k)
      (ER: env_related cst_obs' csm_obs' svals cst_e csm_e)
      (MV: machine_val v)
      (CSRLD: range_lists_disjoint cst_obs cst_obs')
      (CMRLD: range_lists_disjoint csm_obs csm_obs'),
      state_related (cst_obs' ++ cst_obs) (csm_obs' ++ csm_obs)
                    svals
                    (Cstacked.SKexternalReturn id v cst_e cst_k)
                    (Csharpminor.SKexternalReturn id v csm_e csm_k)
  | st_rel_external_stop: forall svals sig cst_e csm_e,
                    state_related nil nil
                    svals
                    (Cstacked.SKexternal sig None cst_e Cstacked.Kstop)
                    (Csharpminor.SKexternal sig None csm_e Csharpminor.Kstop)
  | st_rel_external_return_stop: forall svals v cst_e csm_e
      (MV: machine_val v),
      state_related nil nil
                    svals
                    (Cstacked.SKexternalReturn None v cst_e Cstacked.Kstop)
                    (Csharpminor.SKexternalReturn None v csm_e Csharpminor.Kstop).

Definition set_consistent_with_ptenv (s : Identset.t)
                                    (e : PTree.t Cstacked.env_item) : Prop :=
  forall id, 
    match (PTree.get id e) with
      | Some (Cstacked.Env_local _ _) =>
          Identset.mem id s = false
      | _ => True
    end.

Definition set_consistent_with_env (s : Identset.t)
                                   (en : Cstacked.env) : Prop :=
  let (sp, e) := en in set_consistent_with_ptenv s e.

Definition expr_consistent_with_env (ex : expr) 
                                    (en : Cstacked.env) : Prop :=
  set_consistent_with_env (addr_taken_expr ex) en.

Definition expr_list_consistent_with_env (exl : list expr) 
                                         (en : Cstacked.env) : Prop :=
  set_consistent_with_env (addr_taken_exprlist exl) en.

Definition stmt_consistent_with_env (s : stmt) 
                                    (en : Cstacked.env) : Prop :=
  set_consistent_with_env (addr_taken_stmt s) en.

Definition lstmt_consistent_with_env (s : lbl_stmt) 
                                     (en : Cstacked.env) : Prop :=
  set_consistent_with_env (addr_taken_lblstmt s) en.

Definition dummy_env : Cstacked.env := 
  mkcsenv None (PTree.empty Cstacked.env_item).

Fixpoint cont_consistent_with_env (kp : Cstacked.cont)
                                  (en : Cstacked.env) : Prop :=
  match kp with 
  | Cstacked.Kstop => True
  | Cstacked.Kseq s k => stmt_consistent_with_env s en /\
                cont_consistent_with_env k en 
  | Cstacked.Kblock k => cont_consistent_with_env k en 
  | Cstacked.Kcall _ fd en' k => 
      cont_consistent_with_env k en' /\
      match fd with
        | Internal f => stmt_consistent_with_env f.(fn_body) en
        | _ => True
      end
  end.

Fixpoint econt_consistent_with_env (ekp : Cstacked.expr_cont)
                                   (en : Cstacked.env) : Prop :=
  match ekp with
  | Cstacked.EKunop _ ek =>     
         econt_consistent_with_env ek en
  | Cstacked.EKbinop1 _ e ek => 
         expr_consistent_with_env e en /\
         econt_consistent_with_env ek en
  | Cstacked.EKbinop2 _ _ ek =>    
         econt_consistent_with_env ek en
  | Cstacked.EKload _ ek =>        
         econt_consistent_with_env ek en
  | Cstacked.EKcall _ _ el k =>    
         expr_list_consistent_with_env el en /\
         cont_consistent_with_env k en
  | Cstacked.EKargs _ fd _ el _ k => 
         expr_list_consistent_with_env el en /\
         cont_consistent_with_env k en
  | Cstacked.EKatargs _ _ el _ k => 
         expr_list_consistent_with_env el en /\
         cont_consistent_with_env k en
  | Cstacked.EKcond e1 e2 ek => 
         expr_consistent_with_env e1 en /\
         expr_consistent_with_env e2 en /\
         econt_consistent_with_env ek en
  | Cstacked.EKassign _ k =>    
         cont_consistent_with_env k en
  | Cstacked.EKthread1 e k =>   
         expr_consistent_with_env e en /\
         cont_consistent_with_env k en
  | Cstacked.EKthread2 _ k =>   
         cont_consistent_with_env k en
  | Cstacked.EKcondstmt s1 s2 k => 
         stmt_consistent_with_env s1 en /\
         stmt_consistent_with_env s2 en /\
         cont_consistent_with_env k en
  | Cstacked.EKswitch ls k =>   
         cont_consistent_with_env k en /\
         lstmt_consistent_with_env ls en
  | Cstacked.EKreturn k =>    
         cont_consistent_with_env k en
  | Cstacked.EKstoreaddr _ e k => 
         expr_consistent_with_env e en /\
         cont_consistent_with_env k en
  | Cstacked.EKstoreval _ _ k => 
         cont_consistent_with_env k en
  end.

Definition state_consistent_with_env (sp : Cstacked.state) : Prop := 
  match sp with
  | Cstacked.SKexpr e en ek =>
         expr_consistent_with_env e en /\
         econt_consistent_with_env ek en
  | Cstacked.SKval _ en ek =>
         econt_consistent_with_env ek en 
  | Cstacked.SKstmt s en k =>
         stmt_consistent_with_env s en /\
         cont_consistent_with_env k en
  | Cstacked.SKcall _ k =>
         cont_consistent_with_env k dummy_env
  | Cstacked.SKbind f _ _ en k =>
         stmt_consistent_with_env f.(fn_body) en /\
         cont_consistent_with_env k en
  | Cstacked.SKexternal _ _ en k => 
         cont_consistent_with_env k en
  | Cstacked.SKexternalReturn _ _ en k =>
         cont_consistent_with_env k en
  | Cstacked.SKfree _ _ k =>
         cont_consistent_with_env k  dummy_env
  | Cstacked.SKreturn _ k =>
         cont_consistent_with_env k  dummy_env
  end.

End ENV_REL.

Section MEM_REL. 

(* Relation on memories *)

Variable cst_mem : mem. 
Variable csm_mem : mem. 

(* Values in machine block must be the same in Cstacked and C#minor *)
Definition load_values_related := 
  forall p, machine_ptr p ->
    forall c,
      match load_ptr c cst_mem p, load_ptr c csm_mem p with
        | Some v, Some v' => v = v'
        | _, None => True
        | _, _ => False
      end.

Definition mem_content_machine :=
  forall p c, 
    match load_ptr c csm_mem p with
      | Some v => machine_val v
      | _ => True
    end.

(** Memory relation definition *)
Definition mem_content_related :=
  mrestr cst_mem = low_mem_restr /\
  mrestr csm_mem = no_mem_restr /\
  load_values_related /\
  mem_content_machine.

End MEM_REL.

Definition machine_buffer_item (bi : buffer_item) : Prop :=
  match bi with
    | BufferedWrite p c v => machine_val v 
    | _ => True
  end.

Definition machine_buffer (b : list buffer_item) :=
  forall bi, In bi b -> machine_buffer_item bi.

(* All buffers must only refer to machine pointers... *)
Definition machine_thread_buffers (buffs : buffers) : Prop :=
  forall t, machine_buffer (buffs t).

Definition update_partitioning (t : thread_id) (l : list arange)
                               (p : partitioning) : partitioning :=
  fun t' => if peq t' t then l else p t'.

Fixpoint pointer_in_range_list (p : pointer) (l : list arange) : bool :=
  match l with
    | nil => false
    | (p', _) :: t => 
        if MPtr.eq_dec p p' 
          then true
          else pointer_in_range_list p t
  end.

Fixpoint range_remove (p : pointer) (rs : list arange) : list arange :=
  match rs with
    | nil => nil
    | (p', s')::rest => 
        if MPtr.eq_dec p' p 
          then rest 
          else (p', s')::(range_remove p rest)
  end.

Lemma in_range_remove:
  forall p p' n' l,
    In (p', n') (range_remove p l) -> In (p', n') l.
Proof.
  intros p p' n' l.
  induction l as [|[ph nh] l IH].
  done.
  
  simpl.
  destruct (MPtr.eq_dec ph p) as [-> | N].
  intro. by right.
  simpl. 
  intros [E | IN]. left; done. 
  by right; apply IH.
Qed.

Lemma in_range_remove_back:
  forall p p' n' l,
    In (p', n') l -> p = p' \/ In (p', n') (range_remove p l).
Proof.
  induction l as [|[ph nh] l IH].
  done.
  
  simpl. destruct (MPtr.eq_dec ph p) as [-> | N].
    intros [E | IN]. inv E; by left.
    by right.
  intros [E | IN]. inv E. right; by apply in_eq.
  destruct (IH IN). by left.
  right. by apply in_cons.
Qed.

Definition part_with_vals := (list arange * scratch_vals)%type.

Fixpoint chunk_inside_range_list (p : pointer) (c : memory_chunk)
                                 (l : list arange) : bool :=
  match l with
    | nil => false
    | h :: t => 
        if range_inside_dec (range_of_chunk p c) h
          then true
          else chunk_inside_range_list p c t
  end.

Definition part_update  (bi : buffer_item)
                        (part : list arange)
                     :  option (list arange) :=
  match bi with
    | BufferedFree p MObjStack => 
        if pointer_in_range_list p part 
          then Some (range_remove p part)
          else None
    | BufferedWrite p c v => 
        if low_mem_restr (MPtr.block p)
          then Some part
          else if chunk_inside_range_list p c part 
            then Some part
            else None
    | BufferedAlloc p n MObjStack => 
        if valid_alloc_range_dec (p, n)
          then if range_in_dec (p, n) part 
            then None
            else Some ((p, n) :: part)
          else None
    | BufferedAlloc p n _ => 
        if valid_alloc_range_dec (p, n) 
          then if low_mem_restr (MPtr.block p) 
            then Some part
            else None
          else None
    | BufferedFree p _ => 
        if low_mem_restr (MPtr.block p) 
          then Some part
          else None
  end.

Definition part_update_buffer := fold_left_opt part_update.

Definition is_item_scratch_update (bi : buffer_item) : Prop :=
  match bi with
    | BufferedFree p MObjStack => scratch_ptr p
    | BufferedAlloc p _ MObjStack => scratch_ptr p
    | BufferedWrite p _ _ => scratch_ptr p
    | _ => False
  end.

Definition allocs_related (p : pointer) (n : int) 
                          (b : list buffer_item) : Prop :=
  forall bi, 
    In bi b ->
    is_item_scratch_update bi \/
    match bi with 
      | BufferedAlloc p' n' MObjStack => range_inside (p', n') (p, n)
      | _ => False 
    end.

Definition pointer_inside (p : pointer) (r : arange) : Prop :=
  let '(Ptr b1 ofs1, (Ptr b2 ofs2, s2)) := (p, r) in
    b1 = b2 /\ 
    Int.unsigned ofs1 >= Int.unsigned ofs2 /\
    Int.unsigned ofs1 < Int.unsigned ofs2 + Int.unsigned s2.

Definition frees_related (p : pointer) (n : int)
                         (b : list buffer_item) : Prop :=
  forall bi,
    In bi b ->
    is_item_scratch_update bi \/ 
    match bi with
      | BufferedFree p' MObjStack => pointer_inside p' (p, n)
      | _ => False 
    end.

Definition buffer_item_irrelevant (bi : buffer_item) :=
  match bi with
    | BufferedFree _ MObjStack => False
    | BufferedAlloc _ _ MObjStack => False
    | BufferedAlloc p n _ => valid_alloc_range (p, n) /\ machine_ptr p
    | BufferedFree p _ => machine_ptr p
    | BufferedWrite p _ v => machine_ptr p /\ machine_val v
  end.

Inductive buffers_related : 
  list buffer_item ->      (* Cstacked buffer *)
  list arange ->           (* Cstacked partition *)
  list (list buffer_item) -> (* C#minor (partitioned) buffer *)
  list arange ->           (* C#minor partition *)
  Prop :=
| buffers_related_empty:
  forall tp sp,
    buffers_related nil tp nil sp

| buffers_related_alloc:
  forall p n sb sp sp' tb sbr tp
    (AR: allocs_related p n sb)
    (PUB: part_update_buffer sb sp = Some sp')
    (VAR: valid_alloc_range (p, n))
    (RIN: range_not_in (p, n) tp)
    (BSR: buffers_related tb ((p, n) :: tp) sbr sp'),
    buffers_related (BufferedAlloc p n MObjStack :: tb) tp
                    (sb :: sbr) sp

| buffers_related_free:
  forall p n sb sp sp' tb sbr tp
    (FR: frees_related p n sb)
    (RF: forall r, In r sp' -> ranges_disjoint r (p, n))
    (PUB: part_update_buffer sb sp = Some sp')
    (BSR: buffers_related tb tp sbr sp'),
    buffers_related (BufferedFree p MObjStack :: tb) ((p, n) :: tp)
                    (sb :: sbr) sp

| buffers_related_other:
  forall bi sb sp sp' tb tp sbr
    (BIIR: buffer_item_irrelevant bi)
    (OSCR: forall bis, In bis sb -> is_item_scratch_update bis) 
    (PUB: part_update_buffer sb sp = Some sp')
    (BSR: buffers_related tb tp sbr sp'),
    buffers_related (bi :: tb) tp ((bi :: sb) :: sbr) sp.

Definition buffered_states_related
                          (tb : list buffer_item)
                          (tp : list arange)
                          (ts : Cstacked.state)                          
                          (sb : list buffer_item)
                          (sp : list arange)
                          (sm : mem)
                          (ss : Csharpminor.state) : Prop :=
  exists sm', exists sp', exists tp',
    apply_buffer sb sm = Some sm' /\
    part_update_buffer tb tp = Some tp' /\
    part_update_buffer sb sp = Some sp' /\
    state_related tp' sp' sm' ts ss /\
    state_consistent_with_env ts.

Definition buffered_ostates_related 
                          (tb : list buffer_item)
                          (tp : list arange)
                          (ots : option Cstacked.state)                          
                          (sb : list buffer_item)
                          (sp : list arange)
                          (sm : mem)
                          (oss : option Csharpminor.state) : Prop :=
  match ots, oss with
    | Some ts, Some ss => 
        buffered_states_related tb tp ts sb sp sm ss
    | None, None => tp = nil /\ sp = nil /\ tb = nil /\ sb = nil
    | _, _ => False
  end.

Definition mem_related_with_partitioning
                                 (m : mem) 
                                 (part : positive -> list arange) : Prop :=
  partitioning_disjoint part /\
  (forall t, range_list_disjoint (part t)) /\
  (forall r, (exists t, In r (part t)) <-> 
              range_allocated r MObjStack m).

Definition non_stack_mem_related (cst_m : mem) (csm_m : mem) : Prop :=
  forall r k,
    match k with 
      | MObjStack => True
      | _ => range_allocated r k cst_m <-> range_allocated r k csm_m
    end.

(* Scratch allocations must be unique *)
Fixpoint buffer_scratch_ranges (b : list buffer_item) : list arange :=
  match b with
    | nil => nil
    | BufferedAlloc p n MObjStack :: br =>
        if low_mem_restr (MPtr.block p) 
          then buffer_scratch_ranges br 
          else (p, n) :: (buffer_scratch_ranges br)
    | _ :: br => buffer_scratch_ranges br
  end.

Definition scratch_allocs_fresh (sbs : thread_id -> list buffer_item)
                                (sp : partitioning) : Prop :=
  (* Scratch allocations are disjoint in each buffer *)
  (forall t, 
    range_list_disjoint (buffer_scratch_ranges (sbs t))) /\
  (* Scratch allocations in different buffers are disjoint *)
  (forall t' t, t' <> t ->
    range_lists_disjoint (buffer_scratch_ranges (sbs t))
                         (buffer_scratch_ranges (sbs t'))) /\
  (* Scratch allocations are disjoint from all partitions *)
  (forall t' t, 
    range_lists_disjoint (buffer_scratch_ranges (sbs t))
                         (sp t')).

Definition tso_pc_related_witt (ts : Comp.state tso_mm cst_sem)
                               (ss : Comp.state tso_mm cs_sem) 
                               (bp : thread_id -> list (list buffer_item))
                               (tp : partitioning)
                               (sp : partitioning) : Prop :=
  (* Only machine values in buffers *)
  machine_thread_buffers (fst ss).(tso_buffers) /\
  (* Non-stack allocations are the same *)
  non_stack_mem_related (fst ts).(tso_mem) (fst ss).(tso_mem) /\
  (* Memory contents are related *)
  mem_content_related (fst ts).(tso_mem) (fst ss).(tso_mem) /\
  (* all unbufferings are successful *)
  Comp.consistent tso_mm cs_sem ss /\
  (* bp is C#minor buffer partitioning *)
  (forall t, (fst ss).(tso_buffers) t = flatten (bp t)) /\
  (* buffer partitions are not empty *)
  (forall t b, In b (bp t) -> b <> nil) /\
  (* Scratch allocations in buffers are globally fresh *)
  scratch_allocs_fresh (fst ss).(tso_buffers) sp /\
  (* cstm and csmmp are partitionings consistent with the memory *)
  mem_related_with_partitioning (fst ts).(tso_mem) tp /\
  mem_related_with_partitioning (fst ss).(tso_mem) sp /\
  forall t,
  (* Partitions must be injective *)
  partition_injective (tp t) (sp t) /\
  (* States must be related *)
  buffers_related ((fst ts).(tso_buffers) t) (tp t)
                  (bp t) (sp t) /\
  buffered_ostates_related ((fst ts).(tso_buffers) t) (tp t) 
                           ((snd ts) ! t)
                           (flatten (bp t)) (sp t) (fst ss).(tso_mem) ((snd ss) ! t).

Definition tso_pc_unsafe_related (ts : Comp.state tso_mm cst_sem)
                                 (ss : Comp.state tso_mm cs_sem) : Prop :=
  exists bp, exists tp, exists sp,
    tso_pc_related_witt ts ss bp tp sp.

Definition tso_pc_related ts ss :=
  Comp.consistent _ _ ts /\ tso_pc_unsafe_related ts ss.



Lemma tso_pc_related_to_buff_states:
  forall ttso tthr stso sthr bp sp tp t
    (TREL : tso_pc_related_witt (ttso, tthr) (stso, sthr) bp tp sp),
    buffered_ostates_related (tso_buffers ttso t)
                             (tp t) (tthr ! t)
                             (tso_buffers stso t) 
                             (sp t) stso.(tso_mem) (sthr ! t).
Proof.
  intros. 
  destruct TREL as (_ & _ & _ & _ & FB & _ & _ & _ & _ & THR).
  by destruct (THR t) as (_ & _ & BOR); rewrite <- FB in BOR. 
Qed.

Lemma restricted_low_pointer_machine:
  forall p m,
    mrestr m = low_mem_restr ->
    (restricted_pointer p m <->
     machine_ptr p).
Proof.
  intros [b ofs] m MCR. 
  split; simpl; by rewrite MCR.
Qed.

Fixpoint buffer_insert_list (t : thread_id)
                            (b : list buffer_item)
                            (tso : tso_state) : tso_state :=
  match b with
    | nil => tso
    | bi :: br =>
        buffer_insert_list t br (buffer_insert tso t bi)
  end.

Lemma buffer_insert_list_app:
  forall t b1 b2 tso,
    buffer_insert_list t (b1 ++ b2) tso = 
    buffer_insert_list t b2 (buffer_insert_list t b1 tso).
Proof.
  induction b1 as [|h b1 IH]. done.
  intros. rewrite <- app_comm_cons. simpl.
  by rewrite IH.
Qed.

Lemma buffer_insert_list_s:
  forall t b tso,
    tso_buffers (buffer_insert_list t b tso) t = 
    tso_buffers tso t ++ b.
Proof.
  induction b as [|h b IH]. 
    by simpl; intros; subst; rewrite <- app_nil_end.
  intros tso. 
  simpl. rewrite IH. 
  simpl. by rewrite tupdate_s, app_ass.
Qed.

Lemma buffer_insert_list_o:
  forall t b tso t',
    t' <> t ->
      tso_buffers (buffer_insert_list t b tso) t' = 
      tso_buffers tso t'.
Proof.
  induction b as [|h b IH]. 
    by simpl; intros; subst.
  intros tso t' N. 
  simpl. rewrite IH with (t' := t').
  simpl. by rewrite tupdate_o. done.
Qed.

Lemma buffer_insert_list_m:
  forall t b tso,
    tso_mem (buffer_insert_list t b tso) = tso_mem tso.
Proof.
  induction b as [|h b IH]. 
    simpl; intros; subst; done.
  intros tso. simpl. by rewrite IH.
Qed.

Lemma rev_nil:
  forall {A} {l : list A},
    nil = rev l -> l = nil.
Proof.
  intros A [|]. done.
  intros a l E. apply (f_equal (@rev A)) in E.
  by rewrite rev_involutive in E.
Qed.

Lemma rev_cons:
  forall {A} {h : A} {l t : list A},
    h :: t = rev l -> l = rev t ++ h :: nil.
Proof.
  intros A h l t E.
  apply (f_equal (@rev A)) in E.
  by rewrite rev_involutive in E.
Qed.  

Lemma machine_not_scratch:
  forall p, 
    machine_ptr p -> scratch_ptr p -> False.
Proof.
  intros [b ofs]; simpl; by intros ->.
Qed.

Lemma machine_or_scratch:
  forall p,
    machine_ptr p \/ scratch_ptr p.
Proof.
  intros [b ofs].
  simpl. by destruct low_mem_restr; [left | right].
Qed.

Lemma machine_scratch_disjoint:
  forall p1 n1 p2 n2,
    machine_ptr p1 ->
    scratch_ptr p2 ->
      ranges_disjoint (p1, n1) (p2, n2).
Proof.
  intros [b1 o1] n1 [b2 o2] n2.
  destruct (zeq b1 b2) as [-> | N]. 
    by simpl; intros ->.
  by intros; left.
Qed.

Lemma buffer_item_irrelevant_part_update:
  forall bi p,
    buffer_item_irrelevant bi ->
    part_update bi p = Some p.
Proof.
  intros bi part BI.
  destruct bi as [[b ofs] c v | [b ofs] n [] | [b ofs] []]; 
    simpl; unfold buffer_item_irrelevant in BI; try unfold machine_ptr in BI; simpl in *;
      (* Handle non-alloc cases *)
      try (by try destruct BI; destruct (low_mem_restr b) as [] _eqn : LMR);
      try (by destruct (low_mem_restr b) as [] _eqn : LMR);
        (* Handle the alloc case separately *)
        destruct BI; destruct (valid_alloc_range_dec (Ptr b ofs, n)); try done;
          destruct (low_mem_restr b) as [] _eqn : LMR; done.
Qed.  

End SIMS.

Tactic Notation "cont_related_cases" tactic(first) tactic(c) :=
    first; [
      c "k_rel_call_stop" |
      c "k_rel_seq" |
      c "k_rel_block" |
      c "k_rel_call"].


Tactic Notation "expr_cont_related_cases" tactic(first) tactic(c) :=
    first; [
      c "ek_rel_unop" |
      c "ek_rel_binop1" |
      c "ek_rel_binop2" |
      c "ek_rel_load" |
      c "ek_rel_call" |
      c "ek_rel_args" |
      c "ek_rel_atargs" |
      c "ek_rel_cond" |
      c "ek_rel_assign" |
      c "ek_rel_thread1" |
      c "ek_rel_thread2" |
      c "ek_rel_condstmt" |
      c "ek_rel_switch" |
      c "ek_rel_return" |
      c "ek_rel_storeaddr" |
      c "ek_rel_storeval"].

Tactic Notation "buffers_related_cases" tactic(first) tactic(c) :=
    first; [
      c "buffers_related_empty" |
      c "buffers_related_alloc" |
      c "buffers_related_free" |
      c "buffers_related_other"].

Tactic Notation "state_related_cases" tactic(first) tactic(c) :=
    first; [
      c "st_rel_expr" |
      c "st_rel_stmt" |
      c "st_rel_val" |
      c "st_rel_call" |
      c "st_rel_skipstmt_stop" |
      c "st_rel_free" |
      c "st_rel_return" |
      c "st_rel_bind" |
      c "st_rel_external" |
      c "st_rel_external_return" |
      c "st_rel_external_stop" |
      c "st_rel_external_return_stop"].

Lemma buffers_related_suffix:
  forall tb tp sb sp tb' tp' sb' sp',
    buffers_related tb tp sb sp ->
    buffers_related tb' tp' sb' sp' ->
    part_update_buffer (flatten sb') sp' = Some sp ->
    part_update_buffer tb' tp' = Some tp ->
    buffers_related (tb' ++ tb) tp' (sb' ++ sb) sp'.
Proof.
  intros tb tp sb sp tb' tp' sb' sp' BR BR'.

  (buffers_related_cases (induction BR') Case);
  simpl; intros PUBs PUBt; unfold part_update_buffer in *. 
  
  Case "buffers_related_empty".
    by inv PUBs; inv PUBt.
  
  Case "buffers_related_alloc".
    destruct (fold_left_opt_consD PUBt) as [tpi (PUt & PUBt2)].
    destruct (fold_left_opt_appD PUBs) 
      as [spi (PUs & PUBs2)].
    eapply buffers_related_alloc; try edone.
    rewrite PUs in PUB; inv PUB.
    eapply IHBR'. edone.
    simpl in PUt. 
    destruct valid_alloc_range_dec; try done.
    destruct range_in_dec; try done. by inv PUt.

  Case "buffers_related_free".
    destruct (fold_left_opt_consD PUBt) as [tpi (PUt & PUBt2)].
    destruct (fold_left_opt_appD PUBs) 
      as [spi (PUs & PUBs2)].
    eapply buffers_related_free; try edone.
    rewrite PUs in PUB; inv PUB.
    eapply IHBR'. edone.
    simpl in PUt. destruct MPtr.eq_dec; try done. by inv PUt.

  Case "buffers_related_other".
    destruct (fold_left_opt_consD PUBt) as [tpi (PUt & PUBt2)].
    destruct (fold_left_opt_consD PUBs) as [spi (PUs & PUBs2)].
    destruct (fold_left_opt_appD PUBs2) 
      as [spi' (PUBs3 & PUBs4)].
    eapply buffers_related_other; try edone.
    eapply IHBR'.
      rewrite (buffer_item_irrelevant_part_update _ _ BIIR) in PUs. inv PUs.
      rewrite PUB in PUBs3. by inv PUBs3.
    rewrite (buffer_item_irrelevant_part_update _ _ BIIR) in PUt.
    by inv PUt.
Qed.

Lemma identset_nin_union:
  forall {id s1 s2},
    Identset.mem id (Identset.union s1 s2) = false ->
    Identset.mem id s1 = false /\
    Identset.mem id s2 = false.
Proof.
  intros id s1 s2 NIU.
  assert (NIU' : ~ Identset.In id (Identset.union s1 s2)).
    intro I. apply Identset.mem_1 in I.
    by rewrite I in NIU.
  destruct (Identset.mem id s1) as [] _eqn : Em1.
    elim NIU'; apply Identset.union_2, Identset.mem_2, Em1.
  destruct (Identset.mem id s2) as [] _eqn : Em2.
    elim NIU'; apply Identset.union_3, Identset.mem_2, Em2.
  done.
Qed.

Lemma identset_nin_union_rev:
  forall {id s1 s2},
    Identset.mem id s1 = false /\ Identset.mem id s2 = false ->
    Identset.mem id (Identset.union s1 s2) = false.
Proof.
  intros id s1 s2 [NI1 NI2].
  destruct (Identset.mem id (Identset.union s1 s2)) as [] _eqn:E; [|done].
  apply Identset.mem_2 in E.
  apply Identset.union_1 in E. 
  destruct E as [E | E]; apply Identset.mem_1 in E; by rewrite E in *.
Qed.

Definition env_same_kinds (e e' : Cstacked.env) :=
  forall id, 
   match (csenv_env e) ! id, (csenv_env e') ! id with 
     | Some (Env_local _ _), Some (Env_local _ _) => True
     | Some (Env_stack_scalar _ _), Some (Env_stack_scalar _ _) => True
     | Some (Env_stack_array _), Some (Env_stack_array _) => True
     | _, None => True
     | _, _ => False
   end.

Lemma same_kinds_expr_consistent:
  forall e e' expr
    (ESK : env_same_kinds e e')
    (ECE : expr_consistent_with_env expr e),
      expr_consistent_with_env expr e'.
Proof.
  intros [sp e] [sp' e'] expr ESK ECE.
  intro id. specialize (ESK id). specialize (ECE id).
  simpl in *.
  by destruct (e!id) as [[]|]; destruct (e'!id) as [[]|].
Qed.

Lemma same_kinds_stmt_consistent:
  forall e e' s
    (ESK : env_same_kinds e e')
    (SCE : stmt_consistent_with_env s e),
      stmt_consistent_with_env s e'.
Proof.
  intros [sp e] [sp' e'] expr ESK SCE.
  intro id. specialize (ESK id). specialize (SCE id).
  simpl in *.
  by destruct (e!id) as [[]|]; destruct (e'!id) as [[]|].
Qed.

Lemma same_kinds_lstmt_consistent:
  forall e e' s
    (ESK : env_same_kinds e e')
    (SCE : lstmt_consistent_with_env s e),
      lstmt_consistent_with_env s e'.
Proof.
  intros [sp e] [sp' e'] expr ESK SCE.
  intro id. specialize (ESK id). specialize (SCE id).
  simpl in *.
  by destruct (e!id) as [[]|]; destruct (e'!id) as [[]|].
Qed.

Lemma same_kinds_cont_consistent:
  forall e e' k
    (ESK : env_same_kinds e e')
    (KCE : cont_consistent_with_env k e),
      cont_consistent_with_env k e'.
Proof.
  intros e e' k. 
  induction k; intros; try done; simpl in *.
  - destruct KCE.
    split. eby eapply same_kinds_stmt_consistent.
    by apply IHk.
  - by apply IHk.
  - destruct KCE. 
    split. done.
    destruct f; try done.
    eby eapply same_kinds_stmt_consistent.
Qed.

Lemma same_kinds_expr_list_consistent:
  forall e e' k
    (ESK : env_same_kinds e e')
    (ECE : expr_list_consistent_with_env k e),
      expr_list_consistent_with_env k e'.
Proof.
  intros [sp e] [sp' e'] expr ESK SCE.
  intro id. specialize (ESK id). specialize (SCE id).
  simpl in *.
  by destruct (e!id) as [[]|]; destruct (e'!id) as [[]|].
Qed.

Lemma same_kinds_expr_cont_consistent:
  forall e e' k
    (ESK : env_same_kinds e e')
    (KCE : econt_consistent_with_env k e),
      econt_consistent_with_env k e'.
Proof.
  intros e e' k. 
  induction k; intros; try done; simpl in *;
    try (by apply IHk);
  decompose [and] KCE; repeat split;
    try (by apply IHk); 
    try (eby eapply same_kinds_expr_consistent);
    try (eby eapply same_kinds_expr_list_consistent);
    try (eby eapply same_kinds_cont_consistent);
    try (eby eapply same_kinds_stmt_consistent);
    try (eby eapply same_kinds_lstmt_consistent).
Qed.

Lemma cont_consistent_dummy:
  forall k env, 
    cont_consistent_with_env k env ->
    cont_consistent_with_env k dummy_env.
Proof.
  intros k [] CWE.
  eapply same_kinds_cont_consistent, CWE. 
  unfold dummy_env. intro id. simpl. 
  by destruct (csenv_env!id) as [[]|]; rewrite PTree.gempty.
Qed.

Lemma call_cont_consistent:
  forall oid fd env' k' k env
    (CC : Cstacked.call_cont k = Cstacked.Kcall oid fd env' k')
    (CWE: cont_consistent_with_env k env),
      cont_consistent_with_env k' env'.
Proof.
  intros oid fd env' k' k.
  induction k; intros; simpl in CWE, CC. 
  - done.
  - eapply IHk. done. eby destruct CWE.
  - eby eapply IHk. 
  - by destruct CWE; clarify.
Qed.

Lemma call_cont_consistent_body:
  forall oid f env' k' k env
    (CC : Cstacked.call_cont k = Cstacked.Kcall oid (Internal f) env' k')
    (CWE: cont_consistent_with_env k env),
       stmt_consistent_with_env f.(fn_body) env.
Proof.
  intros oid f env' k' k.
  induction k; intros; simpl in CWE, CC. 
  - done.
  - eapply IHk. done. eby destruct CWE.
  - eby eapply IHk. 
  - by destruct CWE; clarify.
Qed.

Lemma var_local_store_same_kinds:
  forall env id v env',
    var_local_store env id v env' ->
    env_same_kinds env env'.
Proof.
  intros env id v env' VLS.
  inv VLS.
  destruct env; simpl.
  intro id'; simpl in*; destruct (peq id' id) as [<- | N].
    by rewrite PTree.gss, EG. 
  rewrite PTree.gso. by destruct (csenv_env ! id') as [[]|].
  done.
Qed.

Lemma cont_consistent_var_local_store:
  forall env id v env' k,
    var_local_store env id v env' ->
    cont_consistent_with_env k env ->
    cont_consistent_with_env k env'.
Proof.
  intros env id v env' k VLS CWE.
  eapply same_kinds_cont_consistent.
    eby eapply var_local_store_same_kinds.
  edone.
Qed.

Lemma stmt_consistent_skip:
  forall e,
   stmt_consistent_with_env Sskip e.
Proof.
  intros [] id. by destruct (csenv_env!id) as [[]|].
Qed.

Definition compilenv_consistent (ce : compilenv)
                                (i : Identset.t) : Prop :=
  forall id,
    match ce !! id with
      | Var_local _ => 
          Identset.mem id i = false
      | _ => True
    end.

Lemma assign_variables_addr_not_taken:
  forall i cenv' fs' v cenv fs
    (AV : assign_variables i v (cenv, fs) = (cenv', fs'))
    (CEC: compilenv_consistent cenv i),
      compilenv_consistent cenv' i.
Proof.
  intros i cenv' fs' vs.
  induction vs as [|[id []] vs IH]; intros; simpl in *. by inv AV.
    destruct (Identset.mem id i) as [] _eqn : Eis.
      eapply IH. edone.
      intro id'. 
      destruct (peq id' id) as [<- | N].
        by rewrite PMap.gss.
      by rewrite PMap.gso; [apply CEC|].
    eapply IH. edone.
    intro id'. 
    destruct (peq id' id) as [<- | N].
      by rewrite PMap.gss.
    by rewrite PMap.gso; [apply CEC|].
  eapply IH. edone.
  intro id'. 
  destruct (peq id' id) as [<- | N].
    by rewrite PMap.gss.
  by rewrite PMap.gso; [apply CEC|].
Qed.

Lemma build_envmap_consistent:
  forall cenv e' s vs e
    (CEC: compilenv_consistent cenv s)
    (Ebem: build_envmap vs cenv e = Some e')
    (SCE: set_consistent_with_ptenv s e),
      set_consistent_with_ptenv s e'.
Proof.
  intros cenv e' s vs e CEC; revert e.
  induction vs as [|[id vk] vs IH]; intros; simpl in *. 
  by inv Ebem.
  
  specialize (CEC id).
  by destruct (cenv !! id); try done; (eapply IH; [apply Ebem|]);
    (intro id'; destruct (peq id' id) as [<- | N];
      [rewrite PTree.gss |
       rewrite PTree.gso; [apply SCE|]]).
Qed.

Lemma in_atlstmt:
  forall id cases
    (NIR : Identset.mem id (addr_taken_lblstmt cases) = false),
   Identset.mem id (addr_taken_stmt (seq_of_lbl_stmt cases)) = false.
Proof.
  intros id cases. induction cases. done.
  simpl in *.
  intro.
  destruct (identset_nin_union NIR).
  apply identset_nin_union_rev. split. done.
  by apply IHcases.
Qed.

Lemma addr_taken_switch_case:
  forall id cases n
     (NIN : Identset.mem id (addr_taken_lblstmt cases) = false),
     Identset.mem id
       (addr_taken_stmt (seq_of_lbl_stmt (Cstacked.select_switch n cases))) =
       false.
Proof.
  intros id cases.
  induction cases; intros. done.
  simpl in *.
  destruct Int.eq; simpl; destruct (identset_nin_union NIN) as [NIS NIR].
    apply identset_nin_union_rev.
    split. done.
    by apply in_atlstmt.
  apply IHcases. by destruct (identset_nin_union NIN).
Qed.

Lemma build_env_consistent_with_body:
  forall f nenv fs sp
    (Ebe : build_env f = Some (nenv, fs)),
    stmt_consistent_with_env (fn_body f) 
                             (mkcsenv sp nenv).
Proof.
  intros.
  unfold build_env, build_compilenv in Ebe.
  simpl.
  unfold compilenv, PMap.t in Ebe.
  destruct (assign_variables (addr_taken_stmt (fn_body f)) 
               (fn_variables f) (PMap.init Var_global_array, 0%Z))
    as [cenv fsz] _eqn : Eav.
  destruct (build_envmap (fn_variables f) cenv (PTree.empty env_item))
    as [nenv'|] _eqn : Ebem; [|done]. inv Ebe.
  apply assign_variables_addr_not_taken in Eav; [|by intro; rewrite PMap.gi].
  eapply build_envmap_consistent; try edone; [].
  intro id. by rewrite PTree.gempty.
Qed.

Scheme stmt_ind :=     Induction for stmt Sort Prop 
  with lbl_stmt_ind := Induction for lbl_stmt Sort Prop. 

Ltac dest := repeat match goal with
   | H : match ?a with
        | Some x => _
        | None => _
        end = _ |- _ => destruct a as [] _eqn: ?; clarify
   (* | H : _, H': _ |- _ => specialize (H _ _ _ H'); clarify *)
   end.

Lemma stmt_consistent_seq:
  forall {s1 s2 e}
    (SC : stmt_consistent_with_env (Sseq s1 s2) e),
    stmt_consistent_with_env s1 e /\ 
    stmt_consistent_with_env s2 e.
Proof.
  intros s1 s2 [csp cse] SC.
  split; intro id; specialize (SC id); destruct (cse!id) as [[]|];
    try done; simpl in SC; by destruct (identset_nin_union SC).
Qed.

Lemma stmt_consistent_ite:
  forall {s1 s2 expr e}
    (SC : stmt_consistent_with_env (Sifthenelse expr s1 s2) e),
    stmt_consistent_with_env s1 e /\ 
    stmt_consistent_with_env s2 e.
Proof.
  intros s1 s2 expr [csp cse] SC.
  by split; intro id; specialize (SC id); destruct (cse!id) as [[]|];
    try done; simpl in SC; destruct (identset_nin_union SC) as [_ SC'];
      destruct (identset_nin_union SC').
Qed.

Lemma stmt_consistent_lcase:
  forall {i s l e}
    (SC : lstmt_consistent_with_env (LScase i s l) e),
    stmt_consistent_with_env s e /\ 
    lstmt_consistent_with_env l e.
Proof.
  intros i s l [csp cse] SC.
  by split; intro id; specialize (SC id); destruct (cse!id) as [[]|];
    try done; simpl in SC; destruct (identset_nin_union SC).
Qed.

Lemma consistent_lcase_to_seq:
  forall env l,
    lstmt_consistent_with_env l env ->
    stmt_consistent_with_env (seq_of_lbl_stmt l) env.
Proof.
  intros [csp cse].
  induction l; intro LS. done.
  
  simpl in *.
  assert (SCatl: set_consistent_with_ptenv (addr_taken_lblstmt l) cse).
    intro id; specialize (LS id); destruct (cse!id) as [[]|]; try done.
    by destruct (identset_nin_union LS) as [Is Il].
  specialize (IHl SCatl).
  intro id; specialize (LS id); specialize (IHl id);
    destruct (cse!id) as [[]|]; try done.
  destruct (identset_nin_union LS) as [Is Il].
  by apply identset_nin_union_rev; split.
Qed.  

Lemma find_label_consistent:
  forall lbl env s' k' s k
  (FL : Cstacked.find_label lbl s k = Some (s', k'))
  (CCE  : cont_consistent_with_env k env)
  (SCE  : stmt_consistent_with_env s env),
   stmt_consistent_with_env s' env /\ 
   cont_consistent_with_env k' env.
Proof.
  intros lbl env s' k'.
  
  set (PLS ls := forall k
    (FL : Cstacked.find_label_ls lbl ls k = Some (s', k'))
    (CCE  : cont_consistent_with_env k env)
    (SCE  : lstmt_consistent_with_env ls env),
      stmt_consistent_with_env s' env /\ 
      cont_consistent_with_env k' env).

  induction s using stmt_ind with (P0 := PLS); unfold PLS in *; intros;
    simpl in FL; try done; try (eby exploit IHs). 

  (* Sseq *)
  destruct (stmt_consistent_seq SCE) as [SCs1 SCs2].
  eby dest; [exploit IHs1 | exploit IHs2].

  (* Sifthenelse *)
  destruct (stmt_consistent_ite SCE) as [SCs1 SCs2].
  eby dest; [exploit IHs1 | exploit IHs2].
  
  (* Sswitch *)
  exploit IHs; try edone.
  destruct env as [csp cse]. intro id. specialize (SCE id).
  destruct (cse!id) as [[]|]; try done; [].
  simpl in *. by destruct (identset_nin_union SCE).

  (* Slabel *)
  destruct ident_eq. inv FL. by split.
  eby eapply IHs.

  (* LScase *)
  destruct (stmt_consistent_lcase SCE) as [SCs SCl].
  dest.
    exploit IHs; try edone; by split; [apply consistent_lcase_to_seq|].
  eby exploit IHs0.
Qed.

Lemma step_consistent_with_env:
  forall {sge s e s'}
    (ST : Cstacked.cst_step sge s e s')
    (SCE: state_consistent_with_env s),
      state_consistent_with_env s'.
Proof.
  intros sge s e s' ST.
  
  (cst_step_cases (case ST) Case); intros; simpl in *;
    try (by decompose [and] SCE);
    try (by destruct SCE as [SCbo SCek];
      destruct env; unfold expr_consistent_with_env in SCbo;
        do 2 (split; 
          [intros id; specialize (SCbo id); destruct (csenv_env ! id) as [[]|]; 
            try done; simpl in *; by destruct (identset_nin_union SCbo)|]));
    try (by split; [apply stmt_consistent_skip|]).


  Case "StepIfThenElse".
    destruct SCE as [SCbo SCek].
    destruct env; unfold expr_consistent_with_env in SCbo.
    split.
      intros id; specialize (SCbo id); destruct (csenv_env ! id) as [[]|]; 
        try done; simpl in *; by destruct (identset_nin_union SCbo).
    do 2 (split;
      [by intros id; specialize (SCbo id); destruct (csenv_env ! id) as [[]|]; 
        try done; simpl in *; destruct (identset_nin_union SCbo) as [_ X];
          destruct (identset_nin_union X)|]).
    done.

  Case "StepAssignLocal".
    split. eby eapply stmt_consistent_skip.
    eby eapply cont_consistent_var_local_store.
  
  Case "StepEmptyCall".
    destruct SCE.
    split. done.
    destruct fd; try done.
    by intro id'; rewrite PTree.gempty.

  Case "StepCallArgs".
    destruct SCE.
    split. done.
    destruct fd; try done.
    by intro id'; rewrite PTree.gempty.

  Case "StepCond".
    destruct SCE as [SCbo SCek].
    destruct env; unfold stmt_consistent_with_env in SCbo.
    split.
      intros id; specialize (SCbo id); destruct (csenv_env ! id) as [[]|]; 
        try done; simpl in *; by destruct (identset_nin_union SCbo).
    do 2 (split;
      [by intros id; specialize (SCbo id); destruct (csenv_env ! id) as [[]|]; 
        try done; simpl in *; destruct (identset_nin_union SCbo) as [_ X];
          destruct (identset_nin_union X)|]).
    done.
  
  Case "StepSwitch".
    destruct SCE as [SCbo SCek].
    destruct env; unfold stmt_consistent_with_env in SCbo.
    split.
      intros id; specialize (SCbo id); destruct (csenv_env ! id) as [[]|]; 
        try done; simpl in *; by destruct (identset_nin_union SCbo).
    split. done.
    intros id; specialize (SCbo id); destruct (csenv_env ! id) as [[]|]; 
      try done; simpl in *; by destruct (identset_nin_union SCbo).
  
  Case "StepSelect".
    destruct SCE as [SCek SCbo].
    destruct env; unfold lstmt_consistent_with_env in SCbo.
    split; [|done].
    intro id. specialize (SCbo id).
    destruct (csenv_env ! id) as [[]|]; try done; [].
    by apply addr_taken_switch_case.

  Case "StepGoto".
    unfold Cstacked.get_fundef in GFD.
    destruct k' as [| | | oid fd args k']; try done. inv GFD.
    destruct SCE as [_ SCE].
    eapply find_label_consistent. edone.
    simpl. split. eby eapply call_cont_consistent.
    eby eapply call_cont_consistent_body.
    eby eapply call_cont_consistent_body.

  Case "StepReturnNone".
    destruct SCE as [SCek SCbo].
    eby eapply cont_consistent_dummy.

  Case "StepReturnNoneFinish".
    split. by apply stmt_consistent_skip. 
    eby eapply call_cont_consistent.
 
  Case "StepReturnSome1".
    eby eapply cont_consistent_dummy.

  Case "StepReturnFinishLocal".
    split.
      by apply stmt_consistent_skip.
    eapply cont_consistent_var_local_store. edone.
    eby eapply call_cont_consistent.

  Case "StepReturnFinishStack".
    split. by apply stmt_consistent_skip.
    eby eapply call_cont_consistent.

  Case "StepFunctionInternalNoStack".
    split. eby eapply build_env_consistent_with_body with (sp := None).
    subst; simpl in *; destruct SCE; split. done.
    eby eapply build_env_consistent_with_body with (sp := None).

  Case "StepFunctionInternalWithStack".    
    split. eby (eapply build_env_consistent_with_body with (sp := None)).
    subst; simpl in *; destruct SCE; split. done.
    eby eapply build_env_consistent_with_body with (sp := None).

  Case "StepBindArgsEnv".
    destruct SCE. split.
      eapply same_kinds_stmt_consistent; [|edone].
      eby eapply var_local_store_same_kinds.
    eby eapply cont_consistent_var_local_store.

  Case "StepExternalStoreEnv".    
    split. by apply stmt_consistent_skip. 
    eby eapply cont_consistent_var_local_store.

Qed.    

