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
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Global environments are a component of the dynamic semantics of 
  all languages involved in the compiler.  A global environment
  maps symbol names (names of functions and of global variables)
  to the corresponding memory addresses.  It also maps memory addresses
  of functions to the corresponding function descriptions.  

  Global environments, along with the initial memory state at the beginning
  of program execution, are built from the program of interest, as follows:
- A distinct memory address is assigned to each function of the program.
  These function addresses use negative numbers to distinguish them from
  addresses of memory blocks.  The associations of function name to function
  address and function address to function description are recorded in
  the global environment.
- For each global variable, a memory block is allocated and associated to
  the name of the variable.

  These operations reflect (at a high level of abstraction) what takes
  place during program linking and program loading in a real operating
  system. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Ast.
Require Import Integers.
Require Import Pointers.
Require Import Values.
Require Import Mem.

Set Implicit Arguments.

Module Type GENV.

(** ** Types and operations *)

  Variable t: Type -> Type.
   (** The type of global environments.  The parameter [F] is the type
       of function descriptions. *)

  Variable globalenv_initmem: forall (F V: Type), 
     program F V -> t F -> mem_restr -> mem -> Prop.

  (** Return the global environment for the given program. *)

  Variable find_funct_ptr: forall (F: Type), t F -> pointer -> option F.
   (** Return the function description associated with the given address,
       if any. *)

  Definition find_funct: forall (F: Type), t F -> val -> option F :=
      fun F g v => match v with
      | Vptr p => find_funct_ptr g p
      | _ => None
      end.

   (** Same as [find_funct_ptr] but the function address is given as
       a value, which must be a pointer with offset 0. *)

  Variable find_symbol: forall (F: Type), t F -> ident -> option pointer.
   (** Return the address of the given global symbol, if any. *)

(** ** Properties of the operations. *)

  Hypothesis find_funct_find_funct_ptr:
    forall (F: Type) (ge: t F) (p: pointer),
    find_funct ge (Vptr p) = find_funct_ptr ge p.

  Hypothesis find_funct_ptr_symbol_inversion:
    forall (F V: Type) (p: program F V) 
           (ge : t F) (bl : mem_restr) (m : mem)
           (id: ident) (b: pointer) (f: F),
    globalenv_initmem p ge bl m ->
    find_symbol ge id = Some b ->
    find_funct_ptr ge b = Some f ->
    In (id, f) p.(prog_funct).

  Hypothesis find_funct_ptr_prop:
    forall (F V: Type) (P: F -> Prop) (p: program F V) 
           (ge : t F) (bl : mem_restr) (m : mem) (b: pointer) (f: F),
    globalenv_initmem p ge bl m ->
    (forall id f, In (id, f) (prog_funct p) -> P f) ->
    find_funct_ptr ge b = Some f ->
    P f.

  Hypothesis find_funct_prop:
    forall (F V: Type) (P: F -> Prop) (p: program F V) 
           (ge : t F) (bl : mem_restr) (m : mem) (v: val) (f: F),
    globalenv_initmem p ge bl m ->
    (forall id f, In (id, f) (prog_funct p) -> P f) ->
    find_funct ge v = Some f ->
    P f.

  Hypothesis in_prog_find_symbol:
    forall (F V : Type) (p : program F V) 
           (ge : t F) (bl : mem_restr) (m : mem) 
           (id: ident),
    globalenv_initmem p ge bl m ->
    In id (map (fun x => fst (fst x)) (prog_vars p)) ->
    find_symbol ge id <> None.

  Hypothesis find_symbol_mem_restr:    
    forall (F V: Type) (prg : program F V)
           (ge : t F) (bl : mem_restr) (m : mem) (id : ident) (p: pointer),
      globalenv_initmem prg ge bl m ->
      find_symbol ge id = Some p ->
        bl (MPtr.block p).

  Hypothesis find_funct_mem_restr:    
    forall (F V: Type) (prg : program F V)
           (ge : t F) (bl : mem_restr) (m : mem) (f : F) (p: pointer),
      globalenv_initmem prg ge bl m ->
      find_funct_ptr ge p = Some f ->
        bl (MPtr.block p).

  Hypothesis initmem_mem_restr:    
    forall (F V : Type) (prg : program F V)
           (ge : t F) (bl : mem_restr) (m : mem),
      globalenv_initmem prg ge bl m ->
        mrestr m = bl.

  Hypothesis initmem_allocated_global:
    forall (F V : Type) (prg : program F V)
           (ge : t F) (bl : mem_restr) (m : mem),
      globalenv_initmem prg ge bl m ->
      forall r k, range_allocated r k m -> k = MObjGlobal.

  Definition genv_match (A B: Type) (match_fun: A -> B -> Prop)
                        (ge' : t B) (ge : t A) : Prop :=
         (forall id, find_symbol ge id = find_symbol ge' id) /\
         (forall fp,
            match find_funct_ptr ge fp, find_funct_ptr ge' fp with
             | Some f, Some f' => match_fun f f'
             | Some _, None    => False
             | None  , Some _  => False
             | None  , None    => True
            end).

  Hypothesis exists_matching_genv_and_mem_rev:
    forall (A B V W: Type) (match_fun: A -> B -> Prop)
           (match_var: V -> W -> Prop) (p: program A V) (p': program B W) 
           (ge' : t B) (bl : mem_restr) (m : mem),
       match_program match_fun match_var p p' ->
       globalenv_initmem p' ge' bl m ->
       exists ge, globalenv_initmem p ge bl m /\
         genv_match match_fun ge' ge.

  Definition mem_init_eq (m m' : mem) :=
    (forall r k, 
      match k with 
        | MObjGlobal => range_allocated r k m <-> range_allocated r k m'
        | _ => ~ range_allocated r k m /\ ~ range_allocated r k m'
      end) /\
    (forall p c, load_ptr c m p = load_ptr c m' p) /\
    (forall p c, match load_ptr c m p with 
                   | Some (Vptr (Ptr b _)) => mrestr m b /\ mrestr m' b
                   | _ => True
                 end).

  Definition less_restr (mr mr' : mem_restr) :=
    forall b, mr' b -> mr b.

  Hypothesis exists_matching_genv_and_mem_rev_lessdef:
    forall (A B V W: Type) (match_fun: A -> B -> Prop)
           (match_var: V -> W -> Prop) (p: program A V) (p': program B W) 
           (ge' : t B) (bl bl' : mem_restr) (m : mem),
       less_restr bl' bl ->
       match_program match_fun match_var p p' ->
       globalenv_initmem p' ge' bl m ->
       exists ge, exists m', 
         globalenv_initmem p ge bl' m' /\
         genv_match match_fun ge' ge /\
         mem_init_eq m m'.


  (** The following functions should be only used for testing (via extraction). *)
  Variable add_funct : forall (F : Type), (ident * F) -> pointer -> t F -> t F.
  Variable add_symbol : forall (F : Type), ident -> pointer -> t F -> t F.
  Variable empty : forall (F : Type), t F.

End GENV.

(** The rest of this library is a straightforward implementation of
  the module signature above. *)

Module Genv : GENV.

Section GENV.

Variable F: Type.                         (* The type of functions *)
Variable V: Type.                         (* The type of information over variables *)

Record genv : Type := mkgenv {
  functions: ZZMap.t (option F);           (* mapping function ptr -> function *)
  symbols: PTree.t pointer                (* mapping symbol -> block *)
}.

Definition t := genv.

(** Look up in the environment *)
Definition find_funct_ptr (g: genv) (p: pointer) : option F :=
  let (b, ofs) := p in
    ZZMap.get (b, Int.unsigned ofs) g.(functions).

Definition find_funct (g: genv) (v: val) : option F :=
  match v with
  | Vptr p => find_funct_ptr g p
  | _ => None
  end.

Definition find_symbol (g: genv) (symb: ident) : option pointer :=
  PTree.get symb g.(symbols).

Lemma find_funct_inv:
  forall (ge: t) (v: val) (f: F),
  find_funct ge v = Some f -> exists p, v = Vptr p.
Proof.
  intros. destruct v; try discriminate.
  exists p; reflexivity.
Qed.

Lemma find_funct_find_funct_ptr:
  forall (ge: t) (p: pointer),
  find_funct ge (Vptr p) = find_funct_ptr ge p. 
Proof. auto. Qed.

(** Environment construction *)

Definition add_funct (name_fun: (ident * F)) (p : pointer) (g: genv) : genv :=
  let (b, ofs) := p in
  mkgenv (ZZMap.set (b, Int.unsigned ofs) (Some (snd name_fun)) g.(functions))
         (PTree.set (fst name_fun) p g.(symbols)).

Definition add_symbol (name: ident) (p : pointer) (g: genv) : genv :=
  mkgenv g.(functions)
         (PTree.set name p g.(symbols)).


(* Construct environment and initial memory store *)

Definition empty : genv :=
  mkgenv (ZZMap.init None) (PTree.empty _).

Definition fun_size := Int.one.

(* TODO - do not allocate functions in memory;
   instead, assign them distinct pointers non-deterministically *)
Inductive add_genv_functs : mem -> genv -> list (ident * F) -> 
                            mem -> genv -> Prop :=
| add_genv_functs_nil: forall m g, 
    add_genv_functs m g nil m g
| add_genv_functs_cons: forall m0 g0 p f t m1 g1 m2,
    add_genv_functs m0 g0 t m1 g1 ->
    alloc_ptr (p, fun_size) MObjGlobal m1 = Some m2 ->
    add_genv_functs m0 g0 (f::t) m2 (add_funct f p g1).

Inductive add_genv_globals : mem -> genv -> 
                             list (ident * list init_data * V) -> 
                             mem -> genv -> Prop :=
| add_genv_globals_nil: forall m g, 
    add_genv_globals m g nil m g
| add_genv_globals_cons: forall m0 g0 p id init t m1 g1 m2 v,
    add_genv_globals m0 g0 t m1 g1 ->
    initialize_data p init MObjGlobal m1 = Some m2 ->
    add_genv_globals m0 g0 ((id, init, v)::t) m2 (add_symbol id p g1).

Definition globalenv_initmem (p : program F V) (g : t) 
                             (bl : mem_restr) (m : mem) : Prop :=
  exists g1, exists m1,
    add_genv_globals (Mem.empty bl) empty
                     p.(prog_vars) 
                     m1 g1 /\
    add_genv_functs  m1 g1
                     p.(prog_funct)
                     m g.

Inductive genv_inv m ge bl :=
| genv_inv_intro: forall
  (SAL: forall id p, PTree.get id (symbols ge) = Some p ->
                     exists s, range_allocated (p, s) MObjGlobal m)
  (ALG: forall r k, range_allocated r k m -> k = MObjGlobal)
  (INJ: forall id1 id2 p, 
    PTree.get id1 (symbols ge) = Some p ->
    PTree.get id2 (symbols ge) = Some p ->
    id1 = id2)
  (MR: mrestr m = bl)
  (MRF: forall p f (FF: find_funct_ptr ge p = Some f), bl (MPtr.block p)),
    genv_inv m ge bl.
  
(*
Let genv_inv m ge bl := 
  (forall id p, PTree.get id (symbols ge) = Some p ->
                exists s, range_allocated (p, s) MObjGlobal m) /\
  (forall id1 id2 p, 
    PTree.get id1 (symbols ge) = Some p ->
    PTree.get id2 (symbols ge) = Some p ->
    id1 = id2) /\
  (mrestr m = bl).
*)

Lemma genv_inv_empty:
  forall bl, genv_inv (Mem.empty bl) empty bl.
Proof. 
  intro; split; intros; try (rewrite PTree.gempty in *); try done.
    eby eelim range_allocated_empty.
  destruct p; simpl in *. by rewrite ZZMap.gi in FF.
Qed.

Lemma genv_inv_preserved_by_symbol_alloc:
  forall bl m fns symbs p s id m',
    genv_inv m (mkgenv fns symbs) bl ->
    mrestr m' = mrestr m ->
    range_allocated (p, s) MObjGlobal m' ->
    (forall r k, ranges_overlap (p, s) r -> ~ range_allocated r k m) ->
    (forall r k, range_allocated r k m -> range_allocated r k m') ->
    (forall r k, range_allocated r k m' -> r = (p, s) /\ k = MObjGlobal \/ range_allocated r k m) ->
    genv_inv m' (mkgenv fns (PTree.set id p symbs)) bl.
Proof.
  intros bl m fns symbs ptr s id m' GE MR' RA RNA RAP RAB.
  destruct ptr as [b ofs]. destruct GE as [PAL ALG INJ MR MRF].
  split.
  (* All symbols allocated. *)
  intros id' p'. intro SY. destruct p' as [b' ofs'].
  simpl in SY.
  destruct (ident_eq id' id) as [Ideq | Idneq].
    rewrite Ideq in *. rewrite PTree.gss in SY. injection SY as Oeq Beq.
    rewrite Oeq, Beq in *. exists s. assumption.
  rewrite PTree.gso in SY; try assumption. 
  destruct (PAL id' (Ptr b' ofs') SY) as [s' PAL'].
  by exists s'; apply RAP. 
  (* All allocated regions are global *)
  intros r k RA'. by destruct (RAB _ _ RA') as [[_ E] | RA'']; eauto.
  (* The map is injective *)
  intros id1 id2 p'. specialize(INJ id1 id2 p').
  intros SY1 SY2. destruct p' as [b' ofs']. simpl in SY1, SY2.
  destruct (ident_eq id1 id) as [Ideq1 | Idneq1]; try rewrite Ideq1 in *;
  destruct (ident_eq id2 id) as [Ideq2 | Idneq2]; try rewrite Ideq2 in *; try done.

  rewrite PTree.gss in SY1. rewrite PTree.gso in SY2; try assumption.
    injection SY1 as Oeq Beq. rewrite Oeq, Beq in *.
    destruct (PAL _ _ SY2) as [s' PAL']. 
    assert (RO: ranges_overlap (Ptr b' ofs', s) (Ptr b' ofs', s')).
      intro; unfold ranges_disjoint in *; clarify; 
      destruct (allocated_range_valid _ _ _ RA); 
      destruct (allocated_range_valid _ _ _ PAL'); omega. 
    by specialize (RNA _ _ RO PAL'). 
  rewrite PTree.gss in SY2. rewrite PTree.gso in SY1; try assumption.
    injection SY2 as Oeq Beq. rewrite Oeq, Beq in *.
    destruct (PAL _ _ SY1) as [s' PAL']. 
    assert (RO: ranges_overlap (Ptr b' ofs', s) (Ptr b' ofs', s')).
      intro; unfold ranges_disjoint in *; clarify; 
      destruct (allocated_range_valid _ _ _ RA); 
      destruct (allocated_range_valid _ _ _ PAL'); omega. 
    by specialize (RNA _ _ RO PAL').
  by rewrite PTree.gso in SY1, SY2; auto.
  (* Memory restriction *)
  by rewrite MR', MR.
  (* Function pointers respect the block restriction *)
  intros. eauto. 
Qed.

Lemma genv_inv_preserved_by_add_funct:
  forall bl m g p f m',
    genv_inv m g bl ->
    alloc_ptr (p, fun_size) MObjGlobal m = Some m' ->
    genv_inv m' (add_funct f p g) bl.
Proof.
  intros bl m g ptr f m' GE AL.
  destruct g as [fs gs]. destruct ptr as [b ofs].
  destruct (alloc_someD AL) as (RA & _ & _ & RNA).
  exploit genv_inv_preserved_by_symbol_alloc.
  - edone.
  - eby rewrite <- (restr_of_alloc AL). 
  - apply RA. 
  - apply RNA.
  - intros r. apply (alloc_preserves_allocated AL).
  - intros r k. apply (alloc_preserves_allocated_back AL).
  instantiate (1 := (fst f)). intro GE'. destruct GE'.
  split; try done.
  intros [b' ofs'] f' FF. 
  specialize (MRF (Ptr b' ofs') f').  simpl in MRF, FF.
  destruct (MPtr.eq_dec (Ptr b ofs) (Ptr b' ofs')).
    inv e. by apply range_allocated_consistent_with_restr in RA.
  rewrite ZZMap.gso in FF. auto.
  intro E. elim n. inv E. f_equal. by apply Int.unsigned_eq.
Qed.
    
Lemma genv_inv_preserved_by_add_functs:
  forall bl m g l m' g'
    (GE: genv_inv m g bl)
    (AF: add_genv_functs m g l m' g'),
    genv_inv m' g' bl.
Proof.
  intros; induction AF; try done.
  by eapply genv_inv_preserved_by_add_funct; eauto.
Qed.

Lemma store_init_data_list_preserves_allocs:
  forall {init ptr m m'},
    store_init_data_list ptr init m = Some m' ->
    forall r k, range_allocated r k m <-> range_allocated r k m'. 
Proof.
  intros init.
  induction init as [|ih it IH]; intros ptr m m' SID; simpl in SID.
  injection SID as Meq. rewrite Meq. tauto.
  destruct (store_init_data_list (ptr + Int.repr (size_init_data ih)) it m)
    as [m1|] _eqn :EQS; try discriminate.
  specialize (IH _ _ _ EQS). simpl in SID.
  assert (RAm1m' : forall r k, range_allocated r k m1 <-> range_allocated r k m').
  destruct ih; simpl in SID; try done;
    try apply (store_preserves_allocated_ranges SID);
      try (injection SID as Eq; rewrite Eq; tauto).
  intros r k; specialize (IH r k); specialize (RAm1m' r k); tauto.
Qed.

Lemma genv_inv_preserved_by_init_data:
  forall bl m g p id init m',
    genv_inv m g bl ->
    initialize_data p init MObjGlobal m = Some m' ->
    genv_inv m' (add_symbol id p g) bl. 
Proof.
  intros bl m g ptr id init m' GE IN.
  destruct g as [fs gs]. destruct ptr as [b ofs].
  pose proof (restr_of_initialize_data IN) as MR.
  unfold initialize_data in IN.
  destruct (Z_le_dec (Int.unsigned ofs + size_init_data_list init) Int.modulus) 
    as [LMOD|]; try done. 
  destruct (alloc_ptr (Ptr b ofs, Int.repr (size_init_data_list init)) MObjGlobal m)
    as [m1|] _eqn : EQA; try done. simpl in IN.
  destruct (alloc_someD EQA) as (RA & _ & _ & RNA).
  refine (genv_inv_preserved_by_symbol_alloc _ _ GE MR _ RNA _ _).
    by apply (proj1 (store_init_data_list_preserves_allocs IN 
              (Ptr b ofs, Int.repr (size_init_data_list init)) 
              MObjGlobal)).
    intros r k RA'.
    apply (proj1 (store_init_data_list_preserves_allocs IN r k)).
    by apply (alloc_preserves_allocated EQA _ _ RA').
  intros r k RA'.
  apply (proj2 (store_init_data_list_preserves_allocs IN r k)) in RA'.
  by apply (alloc_preserves_allocated_back EQA _ _ RA').
Qed.

Lemma genv_inv_preserved_by_add_globals:
  forall bl m g l m' g',
    genv_inv m g bl ->
    add_genv_globals m g l m' g' ->
    genv_inv m' g' bl /\ g.(functions) = g'.(functions).
Proof.
  intros bl m g l m' g' GE AG.
  induction AG as [mi gi | mi0 gi0 ptr id init ti mi1 gi1 mi2 v AF IH AL].
  split; tauto.
  destruct (IH GE) as [GE1 F1].
  split.
  exact (genv_inv_preserved_by_init_data ptr id init GE1 AL).
  rewrite F1. destruct gi1. auto.
Qed.

Lemma ione : Int.unsigned Int.one = 1.
Proof. done. Qed.

Lemma find_funct_ptr_symbol_inversion:
  forall (p : program F V) (ge : t) (bl : mem_restr) (m : mem) 
         (id: ident) (b: pointer) (f: F), 
    globalenv_initmem p ge bl m ->
    find_symbol ge id = Some b ->
    find_funct_ptr ge b = Some f ->
    In (id, f) p.(prog_funct).
Proof.
  intros p ge bl m id b f GI. revert id b f.
  destruct GI as [g1 [m1 [AG AF]]].
  induction AF as [mi gi | mi0 gi0 ptr fi ti mi1 gi1 mi2 AF IH AL].
  (* Base case *)
  intros id b f  FS FF.
  destruct (genv_inv_preserved_by_add_globals (genv_inv_empty bl) AG) 
    as [GI Feq].
  unfold empty in Feq. destruct gi. simpl in Feq. rewrite <- Feq in *.
  destruct b as [b ofs]; simpl in FF; rewrite ZZMap.gi in FF;
    discriminate.

  (* Step case *)
  intros id b f FS FF.
  destruct fi as [fid fb]. destruct gi1 as [fs1 gs1].
  destruct ptr as [b' ofs']. destruct b as [b ofs].
  unfold find_symbol in FS. simpl in FS.
  unfold find_funct_ptr in FF. simpl in FF.
  destruct (ident_eq fid id) as [IDeq |IDneq]. rewrite IDeq in *. clear IDeq. 
    rewrite PTree.gss in FS. injection FS as Oeq Beq. rewrite Beq, Oeq in *.
    rewrite ZZMap.gss in FF. injection FF as Feq. rewrite Feq. 
    by apply in_eq.
  apply in_cons. rewrite PTree.gso in FS.
  eapply IH; try edone. 
    2: by auto.
  rewrite ZZMap.gso in FF. apply FF. 

  intro H. injection H as Oeq Beq. apply Int.unsigned_eq in Oeq. 
  rewrite Oeq, Beq in *. 
  (* Here is where we need the invariant *)
  destruct (genv_inv_preserved_by_add_globals (genv_inv_empty bl) AG) as [GI Feq].
  destruct (genv_inv_preserved_by_add_functs GI AF) as [GI1 INJ].
  destruct (GI1 _ _ FS) as [s RA].
  assert(0 < Int.unsigned s). destruct (allocated_range_valid _ _ _ RA).
    omega.
  revert RA. destruct (alloc_someD AL) as (_ & _ & _ & D); eapply D; try edone.
  apply ranges_overlapI; try done; unfold fun_size; rewrite ?ione; omega.
Qed.


Lemma find_funct_ptr_prop:    
  forall (P: F -> Prop) (p : program F V)
         (ge : t) (bl : mem_restr) (m : mem) (b: pointer) (f: F),
    globalenv_initmem p ge bl m ->
    (forall id f, In (id, f) (prog_funct p) -> P f) ->
    find_funct_ptr ge b = Some f ->
    P f.
Proof.
  intros P p ge bl m pf f GINIT PROP FF.
  destruct GINIT as [g1 [m1 [AG AF]]].
  induction AF as [mi gi | mi0 gi0 ptr fi ti mi1 gi1 mi2 AF IH AL].
  (* Base case easy since there are no functions in the environment. *)
  destruct (genv_inv_preserved_by_add_globals (genv_inv_empty bl) AG) 
    as [GI Feq].
  unfold empty in Feq. destruct gi. simpl in Feq. rewrite <- Feq in *.
  destruct pf as [b ofs]; simpl in FF; rewrite ZZMap.gi in FF;
    discriminate.
  
  (* Step case. *)
  destruct (MPtr.eq_dec pf ptr) as [Eq|Neq].
  rewrite Eq in *. destruct ptr as [b ofs]. destruct fi as [fid fb].
  simpl in FF. rewrite ZZMap.gss in FF. injection FF as Feq. rewrite <- Feq.
  apply (PROP fid fb). apply in_eq.
  
  destruct ptr as [b ofs]. destruct pf as [b' ofs']. destruct fi as [fid fb].
  simpl in FF. rewrite ZZMap.gso in FF. 
  assert (PR: forall (id : ident) (f : F), In (id, f) ti -> P f).
    intros id' f' IN. apply (PROP id' f'). apply in_cons; auto.
  specialize (IH AG PR FF). assumption.

  intro H. injection H as Oeq Beq. apply Int.unsigned_eq in Oeq.
  rewrite Beq, Oeq in Neq. elim Neq; reflexivity.
Qed.

Lemma find_funct_prop:
    forall (P: F -> Prop) (p : program F V)
           (ge : t) (bl : mem_restr) (m : mem) (v: val) (f: F),
    globalenv_initmem p ge bl m ->
    (forall id f, In (id, f) (prog_funct p) -> P f) ->
    find_funct ge v = Some f ->
    P f.
Proof.
  intros P p ge bl m pf f GINIT PROP FF.
  destruct (find_funct_inv _ _ FF) as [fp PFF].
  rewrite PFF in *. rewrite find_funct_find_funct_ptr in FF.
  exact (find_funct_ptr_prop _ _ GINIT PROP FF).
Qed.

Lemma find_symbol_mem_restr:    
  forall (prg : program F V)
         (ge : t) (bl : mem_restr) (m : mem) (id : ident) (p: pointer)
    (GIM: globalenv_initmem prg ge bl m)
    (FSY: find_symbol ge id = Some p),
      bl (MPtr.block p).
Proof.
  intros.
  destruct GIM as [g1 [m1 [AG AF]]].
  destruct (genv_inv_preserved_by_add_globals (genv_inv_empty bl) AG) as [GI Feq].
  destruct (genv_inv_preserved_by_add_functs GI AF) as [GI1 _ INJ MR FR].
  destruct (GI1 _ _ FSY) as [s RA].
  rewrite <- MR. eby eapply range_allocated_consistent_with_restr.
Qed.

Lemma find_funct_mem_restr:    
  forall (prg : program F V)
         (ge : t) (bl : mem_restr) (m : mem) (f : F) (p: pointer)
    (GIM: globalenv_initmem prg ge bl m)
    (FF: find_funct_ptr ge p = Some f),
      bl (MPtr.block p).
Proof.
  intros.
  destruct GIM as [g1 [m1 [AG AF]]].
  destruct (genv_inv_preserved_by_add_globals (genv_inv_empty bl) AG) as [GI Feq].
  destruct (genv_inv_preserved_by_add_functs GI AF) as [GI1 _ INJ MR FR].
  eauto.
Qed.

Lemma initmem_mem_restr:    
  forall (prg : program F V)
         (ge : t) (bl : mem_restr) (m : mem)
    (GIM: globalenv_initmem prg ge bl m),
      mrestr m = bl.
Proof.
  intros.
  destruct GIM as [g1 [m1 [AG AF]]].
  destruct (genv_inv_preserved_by_add_globals (genv_inv_empty bl) AG) as [GI Feq].
  by destruct (genv_inv_preserved_by_add_functs GI AF).
Qed.

Lemma initmem_allocated_global:    
  forall (prg : program F V)
         (ge : t) (bl : mem_restr) (m : mem)
    (GIM: globalenv_initmem prg ge bl m),
      forall r k, range_allocated r k m -> k = MObjGlobal.
Proof.
  intros.
  destruct GIM as [g1 [m1 [AG AF]]].
  destruct (genv_inv_preserved_by_add_globals (genv_inv_empty bl) AG) as [GI Feq].
  destruct (genv_inv_preserved_by_add_functs GI AF); eauto.
Qed.

Let fss (ge : t) (ids : list ident) :=
  forall id, In id ids -> find_symbol ge id <> None.

Lemma in_prog_find_symbol:
  forall (p : program F V) (ge : t) (bl : mem_restr) (m : mem) 
         (id: ident)
    (GIM: globalenv_initmem p ge bl m)
    (IN : In id (map (fun x => fst (fst x)) (prog_vars p))),
    find_symbol ge id <> None.
Proof.
  intros. 
  destruct GIM as [ige [im (AG & AF)]].
  remember (prog_vars p) as vars. clear Heqvars.

  induction AF.
    induction AG. done.
    unfold add_symbol, find_symbol; simpl.
    destruct (peq id id0) as [<- | N].
      by rewrite PTree.gss.
    simpl in IN; destruct IN as [-> | IN]; [done|].
    eby rewrite PTree.gso; [eapply IHAG|].
  destruct p0; unfold find_symbol, add_funct; simpl.
  destruct (peq id (fst f)) as [<- | N].
    by rewrite PTree.gss.
  eby rewrite PTree.gso; [eapply IHAF|]. 
Qed.  

End GENV.

Lemma globalenv_init_add_funct:
  forall (F V : Type) (p : program F V) (ge : t F) (bl : mem_restr) 
         (m : mem), 
    globalenv_initmem p ge bl m ->
    forall ptr m',
      alloc_ptr (ptr, fun_size) MObjGlobal m = Some m' ->
      forall f, globalenv_initmem (mkprogram (f :: p.(prog_funct))
                                             p.(prog_main)
                                             p.(prog_vars))
                                  (add_funct f ptr ge) bl m'.
Proof.
  intros F V p ge bl m GI ptr n' AL f.
  destruct GI as [g' [m' [AG AF]]].
  exists g'. exists m'.
  split; try assumption.
  simpl. apply (add_genv_functs_cons _ f AF AL).
Qed.

Lemma list_forall2_with_nil_r:
  forall (A B : Type) (m : A -> B -> Prop) a, 
    list_forall2 m a nil -> a = nil.
Proof.
  by intros A B m a LA; remember (@nil B) as nl in LA; induction LA.
Qed.

Lemma list_forall2_with_nil_l:
  forall (A B : Type) (m : A -> B -> Prop) a, 
    list_forall2 m nil a -> a = nil.
Proof.
  by intros A B m a LA; remember (@nil A) as nl in LA; induction LA.
Qed.

Lemma exists_matching_env_add_globals:  
    forall (A B V W : Type) (ge' : t B) (bl : mem_restr) (m : mem) 
           (match_varinfo: V -> W -> Prop) gl' gl,
       list_forall2 (match_var_entry match_varinfo) gl gl' ->
       @add_genv_globals B W (Mem.empty bl) (empty B) gl' m ge' ->
       @add_genv_globals A V (Mem.empty bl) (empty A) gl m
           (mkgenv (ZZMap.init None) ge'.(symbols)).
Proof.
  intros A B V W ge2 bl m mvi gl2 gl1 MGL AG. revert gl1 MGL.
  remember (Mem.empty bl) as em in AG. remember (empty B) as eg in AG.
  induction AG as [mi gi | mi0 gi0 ptr id init ti mi1 gi1 mi2 v AF2 IH AL].
  (* Base case *)
  intros gl1 MGL.
  destruct gi as [gifs givs].
  rewrite (list_forall2_with_nil_r MGL) in *.
  injection Heqeg as Heqgivs Heqgifs.
  rewrite Heqem, Heqgivs. apply add_genv_globals_nil.

  (* Step case *)
  intros gl1 MGL.
  inversion MGL as [|i1 il1 i2 il2 MVE VM2 Eqpv [Eqi2 Eqil2]].
  rewrite <- Eqpv in *.
  pose proof (IH Heqem Heqeg _ VM2) as AG1.
  destruct i1 as [[iid1 iin1] iv1].
  simpl in MVE. destruct MVE as [Eqiid1 [Eqiin1 MVI]]. 
  rewrite Eqiid1, Eqiin1 in *.
  apply (@add_genv_globals_cons A V (Mem.empty bl) (empty A) ptr id init il1
         mi1 (mkgenv (ZZMap.init None) (symbols gi1)) mi2 iv1 AG1 AL).
Qed.

Lemma find_add_funct_s:
  forall (F : Type) (f : F) ptr id g,
    find_funct_ptr (add_funct (id, f) ptr g) ptr = Some f.
Proof.
  intros; destruct ptr; simpl; apply ZZMap.gss.
Qed.

Lemma find_add_funct_o:
  forall (F : Type) (f : F) p1 p2 id g,
    p1 <> p2 ->
    find_funct_ptr (add_funct (id, f) p1 g) p2 = find_funct_ptr g p2.
Proof.
  intros; destruct p1; destruct p2; simpl; apply ZZMap.gso.
  injection. intros. elim H. f_equal; try apply Int.unsigned_eq; auto. 
Qed.


Definition genv_match (A B: Type) (match_fun: A -> B -> Prop)
                      (ge' : t B) (ge : t A) : Prop :=
       (forall id, find_symbol ge id = find_symbol ge' id) /\
       (forall fp,
          match find_funct_ptr ge fp, find_funct_ptr ge' fp with
           | Some f, Some f' => match_fun f f'
           | Some _, None    => False
           | None  , Some _  => False
           | None  , None    => True
          end).

Lemma exists_matching_genv_and_mem_rev:
    forall (A B V W: Type) (match_fun: A -> B -> Prop)
           (match_var: V -> W -> Prop) (p: program A V) (p': program B W) 
           (ge' : t B) (bl : mem_restr) (m : mem),
       match_program match_fun match_var p p' ->
       globalenv_initmem p' ge' bl m ->
       exists ge, globalenv_initmem p ge bl m /\
         genv_match match_fun ge' ge.
Proof.
  intros A B V W mf mv p1 p2 ge2 bl m2 MP GI2.
  destruct MP as [FM [MM VM]]. 
  destruct p1 as [pf1 pm1 pv1]. destruct p2 as [pf2 pm2 pv2]. simpl in *.
  destruct GI2 as [gi2' [m2' [AG AF]]].
  simpl in AG, AF.
  revert pf1 FM.
  induction AF as [mi gi | mi0 gi0 ptr fi ti mi1 gi1 mi2 AF IH AL];
    intros pf1 FM.
  (* Even base case needs some plumbing here, mainly because we need 
     to go over the globals, too... *)
  inversion FM as [Eqpf1|]. subst. 
  exists (mkgenv (ZZMap.init None) gi.(symbols)).
  split.
    exists (mkgenv (ZZMap.init None) gi.(symbols)); exists mi; simpl.
    split; 
      [ apply (@exists_matching_env_add_globals A B V W _ _ _ mv _ _ VM AG) 
      | apply add_genv_functs_nil].
  split; try done.
  intro v; destruct v; simpl.
  rewrite ZZMap.gi. 
  destruct (genv_inv_preserved_by_add_globals (genv_inv_empty B bl) AG) 
    as [_ Feq]; simpl in Feq.
  rewrite <- Feq, ZZMap.gi; done.

  (* Step case. *)
  inversion FM as [| [idpfi1 fpfi1] pft1 [idpfi2 fpfi2] pft2 [Eqid MFB] FMrest E1 [E2 E3]].
  subst pf1 ti fi.
  destruct (IH AG pft1 FMrest) as [ge1 [GI [SY FS]]]; clear IH FMrest.
  exists (add_funct (idpfi1, fpfi1) ptr ge1).
  split; [ exact (globalenv_init_add_funct GI ptr AL (idpfi1, fpfi1)) |].
  split. 
    intro id. rewrite Eqid.
    destruct ptr as [b ofs].
    unfold find_symbol, add_funct. simpl.
    destruct (ident_eq id idpfi2) as [Eqid2 | Neqid2].
      rewrite Eqid2, PTree.gss, PTree.gss; done.
    rewrite !PTree.gso; try assumption; apply SY; done.
  intro v; destruct (MPtr.eq_dec ptr v) as [Eq|Neq].
    rewrite Eq,!find_add_funct_s; done.
  rewrite !find_add_funct_o; try assumption; apply FS; done.
Qed.

Definition mem_init_eq (m m' : mem) :=
  (forall r k, 
    match k with 
      | MObjGlobal => range_allocated r k m <-> range_allocated r k m'
      | _ => ~ range_allocated r k m /\ ~ range_allocated r k m'
    end) /\
  (forall p c, load_ptr c m p = load_ptr c m' p) /\
  (forall p c, match load_ptr c m p with 
                 | Some (Vptr (Ptr b _)) => mrestr m b /\ mrestr m' b
                 | _ => True
               end).

Definition less_restr (mr mr' : mem_restr) :=
  forall b, mr' b -> mr b.

Lemma load_eq_preserved_by_store:
  forall {c m mx p c' p' v' m' mx'}
    (Leq: load_ptr c m p = load_ptr c mx p)
    (ST: store_ptr c' m  p' v' = Some m')
    (STx: store_ptr c' mx p' v' = Some mx'),
  load_ptr c m' p = load_ptr c mx' p.
Proof.
  intros.
  pose proof (load_chunk_allocated_spec c m p) as LDAL.
  pose proof (load_chunk_allocated_spec c mx p) as LDALX.
  pose proof (load_chunk_allocated_spec c m' p) as LDAL'.
  pose proof (load_chunk_allocated_spec c mx' p) as LDALX'.
  destruct (load_ptr c m p) as [v|] _eqn : SMLD.
    (* Load SUCCESS *)
    destruct (range_eq_dec (range_of_chunk p' c') (range_of_chunk p c))
      as [RCeq | RCneq].
      (* Reading exactly the memory written by the unbuffered store *)
      injection RCeq. 
      intro SCeqm.
      assert (SCeq: size_chunk c' = size_chunk c).
      destruct c; destruct c'; simpl in *; compute in SCeqm; done.
      intro Peq; subst.
      by rewrite (load_store_similar ST SCeq), (load_store_similar STx SCeq).
    (* Reading from different memory; two cases: *)
    destruct (ranges_disjoint_dec (range_of_chunk p' c') 
                                         (range_of_chunk p c)) 
        as [RDISJ | ROVER].
      (* Ranges completely disjoint *)
      rewrite <- (load_store_other ST RDISJ), SMLD.
      by rewrite <- (load_store_other STx RDISJ).
      (* Ranges overlap *)
      apply (store_preserves_chunk_allocation ST _ _) in LDAL.
      rewrite (load_store_overlap ST ROVER RCneq LDAL).
      destruct (load_ptr c mx p) as [v''|] _eqn : SMLD'.
      apply (store_preserves_chunk_allocation STx p c) in LDALX.
      rewrite (load_store_overlap STx ROVER RCneq LDALX).
      done.
      by destruct (load_ptr c mx' p);
        [apply (store_preserves_chunk_allocation STx _ _) in LDALX'|].
    (* Load FAIL *)
    apply sym_eq in Leq. rewrite Leq in LDALX.
    destruct (load_ptr c m' p) as [cmv|] _eqn : E2;
      destruct (load_ptr c mx' p) as [cmv'|] _eqn : E3;
        try apply (store_preserves_chunk_allocation STx _ _) in LDALX';
          try apply (store_preserves_chunk_allocation ST _ _) in LDAL';
            try done.
Qed.

Lemma load_eq_preserved_by_alloc:
  forall {c m mx p r' k' m' mx'}
    (Leq: load_ptr c m p = load_ptr c mx p)
    (AP: alloc_ptr r' k' m = Some m')
    (APx: alloc_ptr r' k' mx = Some mx'),
  load_ptr c m' p = load_ptr c mx' p.
Proof.
  intros; destruct r' as [p' n'].
  pose proof (load_chunk_allocated_spec c m p) as LDAL.
  pose proof (load_chunk_allocated_spec c mx p) as LDALX.
  pose proof (load_chunk_allocated_spec c m' p) as LDAL'.
  pose proof (load_chunk_allocated_spec c mx' p) as LDALX'.
  destruct (pointer_chunk_aligned_dec p c) as [CA | CNA].
    2: destruct (load_ptr c m' p); destruct (load_ptr c mx' p);
      try done; destruct LDAL'; destruct LDALX'; done.
  destruct (range_inside_dec (range_of_chunk p c) (p', n')) as [RI | RNI].
    (* loads inside the newly allocated region *)
    rewrite (load_alloc_inside AP); try done;
      rewrite (load_alloc_inside APx); done.
  destruct (ranges_disjoint_dec (range_of_chunk p c) 
                                       (p', n')) as [DISJ | OVER].
    (* loads outside *)
    rewrite (load_alloc_other AP); try done;
      rewrite (load_alloc_other APx); done.
  (* loads overlap *)
  destruct (alloc_someD AP) as [APA _].
  destruct (alloc_someD APx) as [APA' _].
  destruct (load_ptr c m' p).
    destruct LDAL' as [[r [k [RI RA]]] _].
    destruct (ranges_are_disjoint RA APA) as [[-> ->] | DISJ]; try done. 
    eby elim OVER; eapply disjoint_inside_disjoint.
  destruct (load_ptr c mx' p); try done.
  destruct LDALX' as [[r [k [RI RA]]] _].
  destruct (ranges_are_disjoint RA APA') as [[-> ->] | DISJ]; try done. 
  eby elim OVER; eapply disjoint_inside_disjoint.
Qed.

Lemma alloc_ptr_lessdef:
  forall mr mr' m m' r nm
    (LR : less_restr mr' mr)
    (MR : mrestr m = mr)
    (MR': mrestr m' = mr')
    (MEQ: mem_init_eq m m')
    (AP : alloc_ptr r MObjGlobal m = Some nm),
    exists nm',
      alloc_ptr r MObjGlobal m' = Some nm' /\
      mem_init_eq nm nm'.
Proof.
  intros. destruct MEQ as (AEQ & LEQ & LDR).
  pose proof (alloc_cond_spec r MObjGlobal m) as AS.
  pose proof (alloc_cond_spec r MObjGlobal m') as AS'.
  rewrite AP in AS. destruct AS as (RA & VAR & RP & OVERNA).
  destruct (alloc_ptr r MObjGlobal m') as [nm'|] _eqn : AP'.
    destruct AS' as (RA' & VAR' & RP' & OVERNA').
    exists nm'.
    split. done.
    split. 
      intros r' k'; specialize (AEQ r' k'); destruct k';
        try (by split; intro RAr';
          [destruct(alloc_preserves_allocated_back AP _ _ RAr') 
             as [[<- ?] | RAr''] ;[|apply(proj1 AEQ RAr'')] |
           destruct(alloc_preserves_allocated_back AP' _ _ RAr') 
             as [[<- ?] | RAr''] ;[|apply(proj2 AEQ RAr'')]]).
      split; intro RAr'.
      by destruct(alloc_preserves_allocated_back AP _ _ RAr') 
        as [[<- _] | RAr'']; [|apply(alloc_preserves_allocated AP'), AEQ].
      by destruct(alloc_preserves_allocated_back AP' _ _ RAr') 
        as [[<- _] | RAr'']; [|apply(alloc_preserves_allocated AP), AEQ].
    split.
      intros p c.
      eapply load_eq_preserved_by_alloc. apply LEQ. edone. edone.
    intros p c. specialize (LDR p c).
    destruct (load_ptr c nm p) as [[| | | [b ofs]]|] _eqn : LV; try done; [].
    destruct (ranges_disjoint_dec (range_of_chunk p c) r) as [DISJ | OVER].
      rewrite <- (load_alloc_other AP DISJ), LV in LDR.
      by rewrite (restr_of_alloc AP), (restr_of_alloc AP'). 
    destruct (range_inside_dec (range_of_chunk p c) r) as [RI | RNI].
      pose proof (load_chunk_allocated_spec c nm p) as LS; rewrite LV in LS.
      destruct LS as (_ & PCA).
      by rewrite (load_alloc_inside AP RI PCA) in LV.
    by rewrite (load_alloc_overlap AP RNI OVER) in LV. 
  destruct AS' as [NVAR | [NR | [r' [k' [OVER' RA']]]]]. done.
    elim NR. destruct r as [[b ofs] n].
    simpl in *. unfold less_restr in LR. rewrite <-MR, <-MR' in LR.
    by apply LR.
  byContradiction. eapply (OVERNA r' k'). edone.
  specialize (AEQ r' k').
  destruct k'; try (by apply AEQ); destruct (proj2 AEQ RA').
Qed.  

Lemma store_ptr_lessdef:
  forall mr mr' m m' p c v nm
    (LR : less_restr mr' mr)
    (MR : mrestr m = mr)
    (MR': mrestr m' = mr')
    (VR : match v with 
            | Vptr (Ptr b _) => mr b /\ mr' b
            | _ => True
          end)
    (MEQ: mem_init_eq m m')
    (SP : store_ptr c m p v = Some nm),
    exists nm',
      store_ptr c m' p v = Some nm' /\
      mem_init_eq nm nm'.
Proof.
  intros. destruct MEQ as (AEQ & LEQ & LVR).
  pose proof (store_chunk_allocated_spec c m p v) as SS.
  pose proof (store_chunk_allocated_spec c m' p v) as SS'.
  rewrite SP in SS. destruct SS as ([r [k (RI & RA)]] & PCA).
  destruct (store_ptr c m' p v) as [nm'|] _eqn : SP'.
    exists nm'.
    split. done.
    split.       
      intros r' k'; specialize (AEQ r' k'); destruct k';
        try by destruct AEQ as [NA1 NA2]; split; intro RA'; 
        [elim NA1; apply <- (store_preserves_allocated_ranges SP) | 
         elim NA2; apply <- (store_preserves_allocated_ranges SP')]. 
      eapply iff_trans. apply iff_sym, (store_preserves_allocated_ranges SP).
      eapply iff_trans. apply AEQ.
      apply (store_preserves_allocated_ranges SP').      
    split.
      intros p' c'; eapply load_eq_preserved_by_store. apply LEQ. edone. edone.
    intros p' c'. specialize (LVR p' c').
    pose proof (load_chunk_allocated_spec c' nm p') as LS.
    destruct (load_ptr c' nm p') as [[| | | [b ofs]]|] _eqn : LV; try done; [].
    rewrite (restr_of_store SP), (restr_of_store SP').
    destruct (range_eq_dec (range_of_chunk p c) (range_of_chunk p' c'))
      as [RCeq | RCneq].
      (* Reading exactly the memory written by the store *)
      injection RCeq. 
      intro SCeqm.
      assert (SCeq: size_chunk c = size_chunk c').
      destruct c; destruct c'; simpl in *; compute in SCeqm; done.
      intro Peq; subst.
      rewrite (load_store_similar SP SCeq) in LV.
      destruct compatible_chunks. destruct c'; destruct v; try done.
        destruct p. by inv LV. 
      done.
    (* Reading from different memory; two cases: *)
    destruct (ranges_disjoint_dec (range_of_chunk p c) (range_of_chunk p' c'))
        as [RDISJ | ROVER].
      (* Ranges completely disjoint *)
      by rewrite (load_store_other SP RDISJ), LV in LVR.
      (* Ranges overlap *)
      by rewrite (load_store_overlap SP ROVER RCneq LS) in LV.
  elim SS'.
  split.
    exists r; exists k. split. done.
    specialize (AEQ r k); destruct k; try (by apply AEQ);
      by destruct (proj1 AEQ RA).
  done.
Qed.

Lemma store_init_data_lessdef:
  forall mr mr' id m m' p nm
    (LR : less_restr mr' mr)
    (MR : mrestr m = mr)
    (MR': mrestr m' = mr')
    (MEQ: mem_init_eq m m')
    (SP : store_init_data p id m = Some nm),
    exists nm',
      store_init_data p id m' = Some nm' /\
      mem_init_eq nm nm'.
Proof.
  intros; destruct id; simpl in SP; try (eby eapply store_ptr_lessdef);
    inv SP; by exists m'. 
Qed.

Lemma store_init_data_list_lessdef:
  forall mr mr' l m m' p nm
    (LR : less_restr mr' mr)
    (MR : mrestr m = mr)
    (MR': mrestr m' = mr')
    (MEQ: mem_init_eq m m')
    (SP : store_init_data_list p l m = Some nm),
    exists nm',
      store_init_data_list p l m' = Some nm' /\
      mem_init_eq nm nm'.
Proof.
  intros mr mr' l m m' p nm LR MR MR' MEQ.
  revert p nm.
  induction l as [|h l IH]; intros.
  
  exists m'. split. done. by inv SP.
  
  simpl in SP.
  optbind_dest SP mi Emi. simpl in SP.
  destruct (IH _ _ Emi) as [mi' [SIDL' MEQ']].
  rewrite <- (restr_of_store_init_data_list Emi) in MR.
  rewrite <- (restr_of_store_init_data_list SIDL') in MR'.
  destruct (store_init_data_lessdef _ _ LR MR MR' MEQ' SP) as [nm' [SID' MEQ'']].
  exists nm'.
  split. simpl. by rewrite SIDL'.
  done.
Qed.
  
Lemma initialize_data_lessdef:
  forall mr mr' l m m' p nm
    (LR : less_restr mr' mr)
    (MR : mrestr m = mr)
    (MR': mrestr m' = mr')
    (MEQ: mem_init_eq m m')
    (SP : initialize_data p l MObjGlobal m = Some nm),
    exists nm',
      initialize_data p l MObjGlobal m' = Some nm' /\
      mem_init_eq nm nm'.
Proof.
  intros. destruct p as [b ofs].
  unfold initialize_data in *.
  destruct Z_le_dec; [|done].
  optbind_dest SP mi AP.
  destruct (alloc_ptr_lessdef _ LR MR MR' MEQ AP) as [mi' [AP' MEQ']].
  rewrite AP'.
  eapply store_init_data_list_lessdef; try apply SP; try edone.
  by rewrite (restr_of_alloc AP).
  by rewrite (restr_of_alloc AP').
Qed.

Lemma range_allocated_empty:
  forall mr r k,
    ~ range_allocated r k (Mem.empty mr).
Proof.
  intros mr [[b ofs] n] k.
  unfold range_allocated.
  simpl. by rewrite ZTree.gempty.
Qed.

Lemma load_empty_mem:
  forall c mr p,
    load_ptr c (Mem.empty mr) p = None.
Proof.
  intros.
  pose proof (load_chunk_allocated_spec c (Mem.empty mr) p) as LS.
  destruct load_ptr; [|done].
  destruct LS as [[r [k [_ RA]]] _].
  destruct (range_allocated_empty _ _ _ RA).
Qed.

Lemma mem_init_eq_empty:
  forall mr mr',
    mem_init_eq (Mem.empty mr) (Mem.empty mr').
Proof.
  intros.
  split.
    by intros r []; split; intro RA; destruct (range_allocated_empty _ _ _ RA).
  by split; intros p c; rewrite !load_empty_mem.
Qed.

Lemma exists_matching_env_add_globals_lessdef:  
  forall (A B V W : Type) (ge' : t B) (bl bl' : mem_restr) (m : mem) 
         (match_varinfo: V -> W -> Prop) gl' gl
    (LR : less_restr bl' bl)
    (MGL: list_forall2 (match_var_entry match_varinfo) gl gl')
    (AG : @add_genv_globals B W (Mem.empty bl) (empty B) gl' m ge'),
    exists m',
       @add_genv_globals A V (Mem.empty bl') (empty A) gl m'
           (mkgenv (ZZMap.init None) ge'.(symbols)) /\
       mem_init_eq m m'.
Proof.
  intros. revert gl MGL.
  remember (Mem.empty bl) as em in AG. remember (empty B) as eg in AG.
  induction AG as [mi gi | mi0 gi0 ptr id init ti mi1 gi1 mi2 v AF2 IH AL].
  (* Base case *)
  intros gl1 MGL.
  destruct gi as [gifs givs].
  rewrite (list_forall2_with_nil_r MGL) in *. inv Heqeg.
  exists (Mem.empty bl').
  split. apply add_genv_globals_nil. apply mem_init_eq_empty. 

  (* Step case *)
  intros gl1 MGL.
  inversion MGL as [|i1 il1 i2 il2 MVE VM2 Eqpv [Eqi2 Eqil2]].
  rewrite <- Eqpv in *.
  pose proof (IH Heqem Heqeg _ VM2) as AG1.
  destruct i1 as [[iid1 iin1] iv1].
  simpl in MVE. destruct MVE as [Eqiid1 [Eqiin1 MVI]]. 
  rewrite Eqiid1, Eqiin1 in *.
  destruct AG1 as [mi1' (AEG & MEQ)].
  rewrite Heqem, Heqeg in AF2.
  pose proof (genv_inv_preserved_by_add_globals (genv_inv_empty _ _) AF2)
    as ([] & _).
  pose proof (genv_inv_preserved_by_add_globals (genv_inv_empty _ _) AEG)
    as ([] & _).
  destruct (initialize_data_lessdef _ _ LR MR MR0 MEQ AL) as 
    [m' [ID' MEQ']].
  exists m'.
  split.
  apply (@add_genv_globals_cons _ _ _ _ _ id _ _ _ _ _ _ AEG ID').
  done.
Qed.

Lemma exists_matching_genv_and_mem_rev_lessdef:
    forall (A B V W: Type) (match_fun: A -> B -> Prop)
           (match_var: V -> W -> Prop) (p: program A V) (p': program B W) 
           (ge' : t B) (bl bl' : mem_restr) (m : mem),
       less_restr bl' bl ->
       match_program match_fun match_var p p' ->
       globalenv_initmem p' ge' bl m ->
       exists ge, exists m', 
         globalenv_initmem p ge bl' m' /\
         genv_match match_fun ge' ge /\
         mem_init_eq m m'.
Proof.
  intros A B V W mf mv p1 p2 ge2 bl bl' m2 LR MP GI2.
  destruct MP as [FM [MM VM]]. 
  destruct p1 as [pf1 pm1 pv1]. destruct p2 as [pf2 pm2 pv2]. simpl in *.
  destruct GI2 as [gi2' [m2' [AG AF]]].
  simpl in AG, AF.
  revert pf1 FM.
  induction AF as [mi gi | mi0 gi0 ptr fi ti mi1 gi1 mi2 AF IH AL];
    intros pf1 FM.
  (* Even base case needs some plumbing here, mainly because we need 
     to go over the globals, too... *)
  inversion FM as [Eqpf1|]. subst. 
  exists (mkgenv (ZZMap.init None) gi.(symbols)).
  destruct (@exists_matching_env_add_globals_lessdef A B V W _ _ _ _ 
    mv _ _ LR VM AG) as [mi' (AGG & MEQi)].
  exists mi'.
  split.
    exists (mkgenv (ZZMap.init None) gi.(symbols)); exists mi'; simpl.
    by split; [| apply add_genv_functs_nil].
  split; [|done]. 
  split. done.
  intro v; destruct v; simpl.
  rewrite ZZMap.gi. 
  destruct (genv_inv_preserved_by_add_globals (genv_inv_empty B bl) AG) 
    as [_ Feq]; simpl in Feq.
  rewrite <- Feq, ZZMap.gi; done.

  (* Step case. *)
  inversion FM as [| [idpfi1 fpfi1] pft1 [idpfi2 fpfi2] pft2 [Eqid MFB] 
                     FMrest E1 [E2 E3]].
  subst pf1 ti fi.
  destruct (IH AG pft1 FMrest) as [ge1 [me1 (GI & (SY & FS) & MEQ1)]]; 
    clear IH FMrest.
  exists (add_funct (idpfi1, fpfi1) ptr ge1).
  destruct (genv_inv_preserved_by_add_globals (genv_inv_empty B bl) AG) 
    as [GIi Feq]; simpl in Feq.
  pose proof(genv_inv_preserved_by_add_functs GIi AF) 
    as [_ _ _ MRi _]; simpl in Feq.
  pose proof (initmem_mem_restr GI) as MRi'.
  destruct (alloc_ptr_lessdef _ LR MRi MRi' MEQ1 AL) 
    as [m' [AL' MEQ']].
  exists m'.
  split; [ exact (globalenv_init_add_funct GI ptr AL' (idpfi1, fpfi1)) |].
  split; [|done].
  split. 
    intro id. rewrite Eqid.
    destruct ptr as [b ofs].
    unfold find_symbol, add_funct. simpl.
    destruct (ident_eq id idpfi2) as [Eqid2 | Neqid2].
      rewrite Eqid2, PTree.gss, PTree.gss; done.
    rewrite !PTree.gso; try assumption; apply SY; done.
  intro v; destruct (MPtr.eq_dec ptr v) as [Eq|Neq].
    rewrite Eq,!find_add_funct_s; done.
  rewrite !find_add_funct_o; try assumption; apply FS; done.
Qed.

End Genv.
