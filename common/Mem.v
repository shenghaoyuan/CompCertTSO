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
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This file develops the memory model that is used in the dynamic
  semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load_ptr]: read a memory chunk at a given address;
- [store_ptr]: store a memory chunk at a given address;
- [alloc_ptr]: allocate a fresh memory block;
- [free_ptr]: invalidate a memory block.
*)

Require Import Coqlib.
Require Import Specif.
Require Import Maps.
Require Import Ast.
Require Import Pointers.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Decidable.
Require Import Libtactics.

(*============================================================================*)
(** * Structure of memory states *)

(** A memory state is organized in several disjoint blocks.  Each block
  has a low and a high bound that defines its size.  Each block map
  byte offsets to the contents of this byte. *)

(** The possible contents of a byte-sized memory cell.  To give intuitions,
  a 4-byte value [v] stored at offset [d] will be represented by
  the content [Datum(3, v)] at offset [d] and [Cont] at offsets [d+1],
  [d+2] and [d+3].  The [Cont] contents enable detecting future writes
  that would partially overlap the 4-byte value. *)

Inductive content : Type :=
  | Datum: nat -> val -> content   (**r first byte of a value *)
  | Cont: nat -> content.          (**r continuation bytes for a multi-byte value *)

Record mobject_desc : Type := 
  mkmobj { mobj_low : Z; mobj_high : Z; mobj_kind : mobject_kind }.

Definition contentmap : Type := ZTree.t content.
Definition alloclist : Type := list mobject_desc.

(** A memory block comprises the dimensions of the block (low and high bounds)
  plus a mapping from byte offsets to contents.  *)

Record block_contents : Type := mkblock {
  contents: contentmap;
  allocs: alloclist
}.

Lemma content_eq_dec (a b : content): {a = b} + {a <> b}.
Proof. decide equality; auto using eq_nat_dec, Val.eq_dec. Qed.

Lemma mobj_kind_eq (x y : mobject_kind): {x = y} + {x <> y}.
Proof. decide equality. Qed.

Lemma mobject_desc_eq_dec (a b : mobject_desc): {a = b} + {a <> b}.
Proof. decide equality; auto using Z_eq_dec, mobj_kind_eq. Qed.

Lemma block_contents_eq_dec (a b: block_contents): {a = b} + {a <> b}.
Proof. repeat first [apply ZTree.eq | apply content_eq_dec | decide equality]. Qed.

(*============================================================================*)
(** * Operations on memory chunks *)

Definition pred_size_chunk (chunk: memory_chunk) : nat :=
  match chunk with
  | Mint8signed => 0%nat
  | Mint8unsigned => 0%nat
  | Mint16signed => 1%nat
  | Mint16unsigned => 1%nat
  | Mint32 => 3%nat
  | Mfloat32 => 3%nat
  | Mfloat64 => 7%nat
  end.

Lemma size_chunk_pred:
  forall chunk, size_chunk chunk = 1 + Z_of_nat (pred_size_chunk chunk).
Proof.
  by destruct chunk; auto.
Qed.

Lemma size_chunk_pos:
  forall chunk, size_chunk chunk > 0.
Proof.
  intros; rewrite size_chunk_pred; omega.
Qed.

(** Memory reads and writes must respect alignment constraints:
  the byte offset of the location being addressed should be an exact
  multiple of the natural alignment for the chunk being addressed.
  This natural alignment is defined by the following 
  [align_chunk] function.  Some target architectures
  (e.g. the PowerPC) have no alignment constraints, which we could
  reflect by taking [align_chunk chunk = 1].  However, other architectures
  have stronger alignment requirements.  The following definition is
  appropriate for PowerPC and ARM. *)

Definition align_chunk (chunk: memory_chunk) : Z := 
  match chunk with
  | Mint8signed => 1
  | Mint8unsigned => 1
  | Mint16signed => 2
  | Mint16unsigned => 2
  | _ => 4
  end.

Definition align_size (sz: Z) : Z :=
  if zlt sz 2 then 1
  else if zlt sz 4 then 2
  else if zlt sz 8 then 4 else 8.

Lemma align_chunk_pos:
  forall chunk, align_chunk chunk > 0.
Proof.
  intro; destruct chunk; simpl; omega.
Qed.

Lemma align_size_chunk_divides:
  forall chunk, (align_chunk chunk | size_chunk chunk).
Proof.
  intros; destruct chunk; simpl; try apply Zdivide_refl. exists 2; auto. 
Qed.

Lemma align_chunk_compat:
  forall chunk1 chunk2,
  size_chunk chunk1 = size_chunk chunk2 -> align_chunk chunk1 = align_chunk chunk2.
Proof.
  intros chunk1 chunk2. 
  destruct chunk1; destruct chunk2; simpl; congruence.
Qed.

Lemma align_size_pos:
  forall s, align_size s > 0.
Proof.
  intro s.
  unfold align_size. by repeat destruct zlt.
Qed.

Lemma aligned_rng_dec (l h : Z) : {l < h /\ (align_size (h - l) | l)} +
                                  { ~ l < h \/ ~ (align_size (h - l) | l)}.
Proof.
  intros. 
  destruct (Z_lt_dec l h).
    destruct (Zdivide_dec (align_size (h - l)) l (align_size_pos _)).
      by left.
    by right; right.
  right; left; omega.
Qed.

(*============================================================================*)
(** * Operations on blocks and block validity *)

Fixpoint alloclist_hbound (lbnd : Z) (al : alloclist) : option Z :=
  match al with
    nil => Some lbnd
  | (mkmobj l h _ :: t) => 
       if aligned_rng_dec l h 
         then 
           if Z_le_dec lbnd l
             then alloclist_hbound h t
             else None
         else None
  end.

Definition range_allocated_al (l h : Z) (k : mobject_kind) (al : alloclist) 
  : Prop := In (mkmobj l h k) al.

Definition range_in_allocated_al (l h : Z) (k : mobject_kind) (al : alloclist) 
  : Prop := exists lc, exists hc, range_allocated_al lc hc k al /\ 
                                  lc <= l /\ h <= hc.

Definition unallocated_are_undef (b : block_contents) : Prop :=
  forall i, (forall k, ~ range_in_allocated_al i (i + 1) k (allocs b)) -> 
              ZTree.get i (contents b) = None.

Fixpoint check_cont (n k: nat) (p: Z) (m: contentmap) {struct n} : bool :=
  match n with
  | O => true
  | S n1 =>
      match ZTree.get p m with
      | Some (Cont k1) =>
          if eq_nat_dec k1 k then check_cont n1 (S k) (p + 1) m
                             else false
      | _ => false
      end
  end.

Definition stored_value (c : memory_chunk) (v: val) := 
  match c, v with
  | Mint8signed, Vint n    => Some (Vint (Int.zero_ext 8 n))
  | Mint8unsigned, Vint n  => Some (Vint (Int.zero_ext 8 n))
  | Mint16signed, Vint n   => Some (Vint (Int.zero_ext 16 n))
  | Mint16unsigned, Vint n => Some (Vint (Int.zero_ext 16 n))
  | Mint32, Vint n         => Some (Vint n)
  | Mint32, Vptr p         => Some (Vptr p)
  | Mfloat32, Vfloat f => Some (Vfloat(Float.singleoffloat f))
  | Mfloat64, Vfloat f => Some (Vfloat f)
  | _, _ => None
  end.

Definition value_chunk_ok (c : memory_chunk) (v: val) := 
  match c, v with
  | Mint8unsigned, Vint n  => Int.unsigned n < 256 
  | Mint16unsigned, Vint n => Int.unsigned n < 65536
  | Mint32, Vint n         => True
  | Mint32, Vptr p         => True
  | Mfloat32, Vfloat f     => Float.singleoffloat f = f
  | Mfloat64, Vfloat f     => True
  | _, _ => False
  end.

Definition compatible_chunks (c1 c2 : memory_chunk) : bool := 
  match c1, c2 with
  | Mint8signed, Mint8signed
  | Mint8signed, Mint8unsigned
  | Mint8unsigned, Mint8signed
  | Mint8unsigned, Mint8unsigned
  | Mint16signed, Mint16signed 
  | Mint16signed, Mint16unsigned 
  | Mint16unsigned, Mint16signed 
  | Mint16unsigned, Mint16unsigned
  | Mint32, Mint32
  | Mfloat32, Mfloat32
  | Mfloat64, Mfloat64 => true 
  | _, _ => false
 end.

Lemma compatible_chunks_size (c1 c2 : memory_chunk):
  compatible_chunks c1 c2 -> size_chunk c1 = size_chunk c2.
Proof. 
  by destruct c1; destruct c2.
Qed.

Lemma load_result_stored_value_some:
  forall chunk chunk' v w, 
    stored_value chunk v = Some w ->
    pred_size_chunk chunk = pred_size_chunk chunk' ->
    Val.load_result chunk' v = Val.load_result chunk' w.
Proof.
  intros c c' v w.
  destruct c; destruct v; simpl; intro X; clarify;
  destruct c'; clarify; simpl;
    rewrite ?Int.sign_ext_zero_ext, ?Int.zero_ext_idem,
            ?Float.singleoffloat_idem; clarify.
Qed.

Lemma load_result_stored_value_none:
  forall c v, 
    stored_value c v = None ->
    Val.load_result c v = Vundef.
Proof.
  intros c v.
  destruct c; destruct v; simpl; intro X; clarify;
    rewrite ?Int.sign_ext_zero_ext, ?Int.zero_ext_idem,
            ?Float.singleoffloat_idem; clarify.
Qed.

Lemma stored_value_ok:
  forall chunk v w, 
    stored_value chunk v = Some w ->
    exists chunk', pred_size_chunk chunk = pred_size_chunk chunk' /\ value_chunk_ok chunk' w.
Proof.
  intros chunk v w.
  destruct chunk; destruct v; simpl; intro X; clarify;
    try solve [by exists Mint32|by exists Mfloat64
    | by exists Mint8unsigned; split; [|refine (proj2 (Int.zero_ext_range _ _ _))]
    | by exists Mint16unsigned; split; [|refine (proj2 (Int.zero_ext_range _ _ _))]].
  exists Mfloat32; split; simpl; try done.
  by apply Float.singleoffloat_idem.
Qed.

Lemma value_chunk_ok1: 
   forall c v, value_chunk_ok c v -> Val.load_result c v = v.
Proof.
  intros; destruct c; destruct v; simpl in *; try rewrite H; try done;
  by destruct (Int.unsigned_range i); f_equal; eapply Int.unsigned_eq;
     rewrite Int.zero_ext_mod, Zmod_small.
Qed.

Lemma value_chunk_ok_undef: 
   forall c v, value_chunk_ok c v -> Val.load_result c v <> Vundef.
Proof.
  by intros; destruct c; destruct v.
Qed.

Lemma load_result_undef: 
   forall c, Val.load_result c Vundef = Vundef.
Proof.
  by intros; destruct c.
Qed.


(* [chunk_allocated_al b chunk i] is true if in the block [b], the range starting
   address [i] with the size [chunk] is contained in some allocated range. Note
   that the chunk cannot span across more than one allocated range. *)
Definition chunk_allocated_al (chunk: memory_chunk) 
                              (b : block_contents) (i : Z) : Prop :=
  exists k, range_in_allocated_al i (i + size_chunk chunk) k (allocs b).


(** [valid_access al chunk ofs] holds if a load or a store
    of the given chunk is possible at address [ofs] w.r.t. [al].
    This means:
- The range of bytes accessed is allocated within [b].
- The offset [ofs] is aligned.
*)

Inductive valid_access (chunk: memory_chunk) (ofs: Z) 
                       (al: alloclist) : Prop :=
  | valid_access_intro:
      forall k,
      range_in_allocated_al ofs (ofs + size_chunk chunk) k al ->
      (align_chunk chunk | ofs) ->
      valid_access chunk ofs al.

Definition cont_bytes_ok (b : block_contents) : Prop :=
    (forall (i : Z) n, ZTree.get i (contents b) = Some (Cont n) ->
      exists l, exists v, ZTree.get (i - Z_of_nat n) (contents b) = Some (Datum (l + n) v))
 /\ (forall (i : Z) n v, ZTree.get i (contents b) = Some (Datum n v) ->
        (exists c, n = pred_size_chunk c /\ value_chunk_ok c v /\ valid_access c i (allocs b))
     /\ check_cont n 1 (i + 1) (contents b)).

Definition block_valid (b : block_contents) : Prop :=
  unallocated_are_undef b /\
  cont_bytes_ok b /\
  exists hbnd, alloclist_hbound 1 (allocs b) = Some hbnd /\
               hbnd <= Int.modulus.

(** Block validity preservation by a block transformation function. *)
Definition preserves_block_validity (f : block_contents -> option block_contents) : Prop :=
    forall b b', f b = Some b' -> block_valid b -> block_valid b'.

(*============================================================================*)
(** * Decidability results for alloclists *)

(** Decidability of membership in an alloc range. *)
Lemma block_mem_dec:
  forall l h c, {c.(mobj_low) <= l /\ h <= c.(mobj_high)} + 
                {~ (c.(mobj_low) <= l /\ h <= c.(mobj_high))}.
Proof.
  intros l h [lc hc kc]. simpl.
  destruct (zle lc l); destruct (zle h hc);
    try (right; omega); try (left; omega).
Qed.

(** Decidability of whether a block is too big. *)
Lemma block_mem_huge_dec:
  forall c, {Int.modulus <= c.(mobj_high)} + 
            {~ (Int.modulus <= c.(mobj_high))}.
Proof.
  intros [lc hc kc]; simpl.
  destruct (zle Int.modulus hc);
    try (right; omega); try (left; omega).
Qed.

(** Decidability of range validity *)
Lemma range_in_allocated_al_dec (l h : Z) (al : alloclist) : 
  {k | range_in_allocated_al l h k al} + {forall k', ~ range_in_allocated_al l h k' al}.
Proof.
  pose proof (strong_in_dec _ _ (block_mem_dec l h) al) as DEC.
  destruct DEC as [[[el eh ek] [einal ein]]|noe].
  left. exists ek. exists el. exists eh. tauto.
  right. intro k'. intro rngal. destruct rngal as [lc [hc [inal inbnd]]]. 
  specialize (noe (mkmobj lc hc k')). tauto. 
Qed.

(** Executable version of chunk_allocated. *)
Lemma chunk_allocated_al_dec:
  forall chunk b i,
    {chunk_allocated_al chunk b i} + {~ chunk_allocated_al chunk b i}.
Proof.
  intros chunk b i.
  unfold chunk_allocated_al.
  destruct (range_in_allocated_al_dec i (i + size_chunk chunk) (allocs b))
    as [[k RA]|NRA].
  eby left; eexists.
  by right; intros [x H]; apply (NRA x). 
Qed.

(** The following function checks whether accessing the given memory chunk
  at the given offset in the given block respects the bounds of the block. *)
Definition in_block (chunk: memory_chunk) (al: alloclist) (ofs: Z) :
           {valid_access chunk ofs al} + {~valid_access chunk ofs al}.
Proof. 
  intros.
  destruct (range_in_allocated_al_dec ofs (ofs + size_chunk chunk) al) as [[k]|N];
  destruct (Zdivide_dec (align_chunk chunk) ofs (align_chunk_pos chunk));
  try (eby left; econstructor);
  try (by try red in N; right; intro nv; destruct nv; eauto).
Qed.
  
(** The following predicates will be used to describe the state
    of allocated memory. *)

(** The initial store. *)

Definition empty_block : block_contents :=
  mkblock (ZTree.empty _) nil.

Lemma empty_block_valid: block_valid empty_block.
Proof. 
  by repeat split; repeat intro; try rewrite ZTree.gempty in *; clarify; exists 1.
Qed.

Lemma invalid_access_nil  (chunk: memory_chunk) (ofs: Z) :
   ~valid_access chunk ofs nil.
Proof. by intros [k [? [? [X ?]]]]; inversion X. Qed.

(*
Lemma invalid_block_access_empty (chunk: memory_chunk) (ofs: Z) :
   ~valid_block_access chunk ofs empty_block.
Proof. by intros c o [[? [? [? [X ?]]]]]; inversion X. Qed.
*)

Lemma valid_access_same_size:
  forall c ofs b c',
    size_chunk c = size_chunk c' ->
    valid_access c ofs b ->
    valid_access c' ofs b.
Proof.
  intros c ofs b c' EQs VBA.
  destruct VBA as [k CA AL].
  econstructor.
    eby rewrite <- EQs.
  by rewrite align_chunk_compat with (chunk2 := c).
Qed.


(** Allocation of a block of a given size at a given address. The allocation
    fails if any address in the block is already allocated *)

(** Here we give an executable version, then we prove an abstract specification.
    Finally, we show preservation of invariants. *)

Fixpoint alloc_in_alloclist (l h : Z) (k : mobject_kind) 
                            (al : alloclist) : option alloclist :=
  match al with
  | nil => Some (mkmobj l h k :: nil)
  | mkmobj lc hc kc :: t =>
      if Z_le_dec h lc then Some (mkmobj l h k :: al)
        else if Z_le_dec hc l then
          option_map (fun nal => mkmobj lc hc kc :: nal)
                     (alloc_in_alloclist l h k t)
          else None
  end.

Definition alloc_block (l h : Z) (k : mobject_kind) (m : block_contents) :
  option block_contents :=
  if Z_le_dec 1 l 
    then if aligned_rng_dec l h 
      then if Z_le_dec h Int.modulus
        then match alloc_in_alloclist l h k (allocs m) with
               | None => None
               | Some newal =>
                     Some(mkblock (contents m) newal)
             end
        else None
      else None
    else None.

Lemma alloc_block_inv:
  forall l h k b b',
    alloc_block l h k b = Some b' ->
    alloc_in_alloclist l h k b.(allocs) = Some b'.(allocs) /\
    contents b' = contents b /\
    1 <= l /\ l < h /\ h <= Int.modulus /\ (align_size (h - l) | l).
Proof.
  intros l h k b b' AB. unfold alloc_block in AB.
  destruct Z_le_dec; [|done].
  destruct aligned_rng_dec; [|done].
  destruct Z_le_dec; [|done].
  destruct (alloc_in_alloclist l h k (allocs b)); [|done].
  by inv AB; tauto.
Qed.
  
(** Memory invariant preservation for allocation *) 
Lemma alloclist_lbnd_lt_hbnd:
  forall {al l h}, alloclist_hbound l al = Some h -> l <= h.
Proof.
  intros al.
  induction al as [|lhc t IH]. 
  intros l h. simpl; intro H; inversion H; omega.
  (* Inductive case *)
  destruct lhc as [lc hc]. intros l h. simpl.
  destruct (aligned_rng_dec lc hc); destruct (Z_le_dec l lc);
    intros; try discriminate.
  assert (hc <= h). apply IH. assumption. omega.
Qed.

Lemma alloclist_hbound_impl_l_lt_h:
  forall {al a b l h k},
    alloclist_hbound a al = Some b ->
    range_allocated_al l h k al ->
    l < h /\ a <= l /\ h <= b /\ (align_size (h - l) | l).
Proof.
  intros al.
  induction al as [|lhc t IH]. 
  intros a b l h k _ RA. destruct RA.
  (* Inductive case *)
  destruct lhc as [lc hc kc]. intros a b l h k. simpl.
  destruct (aligned_rng_dec lc hc) as [[L A] | ]; destruct (Z_le_dec a lc);
    intros X RA; try done.
  destruct (in_inv RA) as [EQ | CONS].
    inv EQ; apply alloclist_lbnd_lt_hbnd in X; tauto.
  destruct (IH _ _ _ _ _ X CONS) as (? & ? & ? & ?). 
  by repeat split; try omega.
Qed.

Lemma alloclist_no_overlap:
  forall {al a b l h k l' h' k'}
    (HBND: alloclist_hbound a al = Some b)
    (RA: range_allocated_al l h k al)
    (RA': range_allocated_al l' h' k' al),
    h <= l' \/ h' <= l \/ l = l' /\ h = h' /\ k = k'.
Proof.
  induction al as [|[lc hc kc] t IH]; intros; [done|]. 
  simpl in HBND; destruct (aligned_rng_dec lc hc) as [[? ?] |]; 
    destruct (Z_le_dec a lc); try done.
  destruct (in_inv RA) as [RAeq | RAtail]; 
    destruct (in_inv RA') as [RAeq' | RAtail']. 
  inv RAeq; inv RAeq'; right; right; done. 
  inv RAeq; destruct (alloclist_hbound_impl_l_lt_h HBND RAtail');
    left; omega.
  inv RAeq'; destruct (alloclist_hbound_impl_l_lt_h HBND RAtail); 
    right; left; omega.
  by specialize (IH _ _ _ _ _ _ _ _ HBND RAtail RAtail').
Qed.

Remark allocated_al_same:
  forall {lbnd hbnd a l h k h' k'}
    (AHBND: alloclist_hbound lbnd a = Some hbnd)
    (RA1: range_allocated_al l h k a)
    (RA2: range_allocated_al l h' k' a),
    h = h' /\ k = k'.
Proof.
  intros.
  pose proof (alloclist_hbound_impl_l_lt_h AHBND RA1).
  pose proof (alloclist_hbound_impl_l_lt_h AHBND RA2).
  destruct (alloclist_no_overlap AHBND RA1 RA2) as [|[]];
    try omegaContradiction.
  tauto.
Qed.  

Lemma alloc_preserves_alloclist_validity:
  forall l h k al al' ol lbnd hbnd,
    lbnd <= l -> l < h -> (align_size (h - l) | l) -> 
    h <= Int.modulus -> ol <= l -> ol <= lbnd ->
    alloc_in_alloclist l h k al = Some al' ->
    alloclist_hbound lbnd al = Some hbnd ->
    alloclist_hbound ol al' = Some(Zmax hbnd h).
Proof.
  intros l h k.
  induction al as [|lhc t IH].
  (* Base case *)
  intros al' ol lbnd hbnd lpos l_lt_h alg h_lt_m oll ollbnd. simpl.
  intros H1 H2. inversion H1 as [lh_al']. inversion H2 as [hbnd1].
  rewrite Zmax_right. simpl.
  destruct (aligned_rng_dec l h) as [[]|[|]]; destruct (Z_le_dec ol l); 
    destruct (Z_le_dec hbnd l); simpl; 
    try discriminate; try congruence; try omegaContradiction.
  omega.

  (* Inductive case *)
  intros al' ol lbnd hbnd lpos l_lt_h alg h_lt_m oll ollbnd. 
  destruct lhc as [lc hc]. simpl.
  destruct (Z_le_dec h lc); destruct (aligned_rng_dec lc hc) as [[? ?]|];
    destruct (Z_le_dec lbnd lc); simpl; 
    try discriminate; try congruence; try omegaContradiction.
  intros H1 H2. clarify. 
  pose proof (alloclist_lbnd_lt_hbnd H2) as hchbnd.
  assert (h < hbnd). omega. rewrite (Zmax_left). simpl.
  by destruct (aligned_rng_dec l h) as [[]|[|]]; destruct (Z_le_dec ol l);
    destruct (aligned_rng_dec lc hc) as [[]|[|]]; destruct (Z_le_dec h lc); 
      try omegaContradiction; try omega.
  omega.
  intros H1 H2. 
  destruct (Z_le_dec hc l);
    destruct (alloc_in_alloclist l h k t); 
    try omegaContradiction; try discriminate; try assumption.
  simpl in H1. injection H1 as apeq. rewrite <- apeq in *. simpl.
  destruct (aligned_rng_dec lc hc) as [[]|[|]]; destruct (Z_le_dec ol lc);
    try omegaContradiction; inv H1; try done.
  by apply (IH a hc hc hbnd); try omega. 
Qed.  

(** * The effect of allocation on alloclists *)

(** Allocation preserves all allocated ranges. *)
Lemma alloc_preserves_allocated_al:
  forall {a a' l l' h h' k k'},
  alloc_in_alloclist l h k a = Some a' ->
  range_allocated_al l' h' k' a ->
  range_allocated_al l' h' k' a'.
Proof.
  intro a. induction a as [|c t IH].
  intros a' l l' h h' k k'.
  simpl. intros APIeq RA. 
  destruct RA.
  
  (* Inductive case *)
  intros a' l l' h h' k k'. destruct c as [lc hc].
  simpl. 
  destruct (Z_le_dec h lc). intro H.
  injection H as APeq. rewrite <- APeq.
  intro RA. (* destruct RA as [ein ebnd]. exists e. *)
  apply in_cons. apply RA.
  destruct (Z_le_dec hc l); 
    intro H ; try discriminate.
  destruct (alloc_in_alloclist l h k t) as [a|] _eqn: eqa. 
  injection H as apeq. rewrite <- apeq.
  intro RA.
  destruct (in_inv RA) as [ein|ein].
  rewrite ein. apply in_eq.
  assert (RAt: range_allocated_al l' h' k' t). auto.
  specialize (IH _ _ _ _ _ _ _ eqa RAt). apply in_cons. tauto.
  discriminate.
Qed.

(** Allocation preserves all allocated sub-ranges. *)
Lemma alloc_preserves_in_allocated_al:
  forall {a a' l l' h h' k k'},
  alloc_in_alloclist l h k a = Some a' ->
  range_in_allocated_al l' h' k' a ->
  range_in_allocated_al l' h' k' a'.
Proof.
  intros a a' l l' h h' k k' AIA RIA.
  destruct RIA as [lc [hc [RA [IE1 IE2]]]].
  exists lc. exists hc.
  repeat split; try assumption.
  exact (alloc_preserves_allocated_al AIA RA).
Qed.

(** Any range in the allocated memory must have been in the original memory
    or it is the newly allocated range. *)
Lemma alloc_preserves_allocated_bw:
  forall {a a' l l' h h' k k'},
  alloc_in_alloclist l h k a = Some a' ->
  range_allocated_al l' h' k' a' ->
  range_allocated_al l' h' k' a \/ l' = l /\ h' = h /\ k' = k.
Proof.
  intro a. induction a as [|c t IH].
  intros a' l l' h h' k k'.
  simpl. intros APIeq RA. 
  injection APIeq as APeq. rewrite <- APeq in RA.
  unfold range_allocated_al in RA. destruct (in_inv RA) as [H|H].
  injection H; intros; right; repeat split; symmetry; assumption.
  destruct H.
  
  (* Inductive case *)
  intros a' l l' h h' k k'. destruct c as [lc hc kc].
  simpl. 
  destruct (Z_le_dec h lc). intro H.
  injection H as APeq. rewrite <- APeq.
  intro RA. unfold range_allocated_al in RA. destruct (in_inv RA) as [EQ|CONS].
  injection EQ; intros; right; repeat split; symmetry; assumption. 
  left; assumption.
  destruct (Z_le_dec hc l); intro H ; try discriminate.
  destruct (alloc_in_alloclist l h k t) as [a|] _eqn: eqa; try discriminate.
  simpl in H. injection H as APeq. rewrite <- APeq.
  intro RA; destruct (in_inv RA) as [EQ|CONS].
  inv EQ . left. apply in_eq.
  destruct (IH _ _ _ _ _ _ _ eqa CONS).
    left; apply in_cons; assumption.
    right; assumption.
Qed.

(** Successful allocation really puts the range into the alloclist. *)
Lemma alloc_allocates:
  forall {a a' l h k},
    alloc_in_alloclist l h k a = Some a' ->
    range_allocated_al l h k a'.
Proof.
  intro a. induction a as [|[lc hc kc] t IH].
  intros a' l h k AA; inv AA; apply in_eq.

  (* Inductive case *)
  intros a' l h k AA; simpl in AA.
  destruct (Z_le_dec h lc). 
  injection AA as Aeq; rewrite <- Aeq; apply in_eq.
  destruct (Z_le_dec hc l); destruct (alloc_in_alloclist l h k t) as [] _eqn : EQA; 
    simpl in AA; try discriminate.
  inv AA; apply IH in EQA; apply in_cons; assumption.
Qed.

(** Successful allocation really puts the range into the alloclist. *)
Lemma alloc_fail_overlap:
  forall {a l h k}
    (AA: alloc_in_alloclist l h k a = None),
    exists l', exists h', exists k',
      range_allocated_al l' h' k' a /\ l < h' /\ l' < h.
Proof.
  induction a as [|[lc hc kc] t IH]; simpl; intros; try done.
  destruct (Z_le_dec h lc); try done.
  destruct (Z_le_dec hc l).
    destruct (alloc_in_alloclist l h k t) as [] _eqn : EQA; 
      simpl in AA; try done.
    destruct (IH _ _ _ EQA) as [l' [h' [k' [AL OVER]]]].
    eexists; eexists; eexists; split; [eapply in_cons; edone | done].
  eexists; eexists; eexists; split; [apply in_eq | omega].
Qed.

(** If allocation succeeds, then the block must have been free before. *)
Lemma alloc_allocated_was_free:
  forall {a a' lbnd hbnd l h k},
    alloclist_hbound lbnd a = Some hbnd ->
    alloc_in_alloclist l h k a = Some a' ->
    forall l' h' k', l < h' -> l' < h -> 
      ~ range_allocated_al l' h' k' a.
Proof.
  intro a. induction a as [|c t IH].
  intros a' lbnd hbnd l h k HB AA l' h' k' Llth' Lplth RA. destruct RA.
  
  (* Inductive case *)
  intros a' lbnd hbnd l h k HB AA l' h' k' Llth' Lplth RA.
  destruct c as [lc hc kc]. simpl in AA.
  simpl in HB; destruct (aligned_rng_dec lc hc) as [[]|]; 
    destruct (Z_le_dec lbnd lc); try discriminate.
  destruct (Z_le_dec h lc). 
  destruct (in_inv RA) as [EQ|CONS]. inv EQ. omega. 
  pose proof (alloclist_hbound_impl_l_lt_h HB CONS). omega.
  destruct (Z_le_dec hc l); destruct (alloc_in_alloclist l h k t) as [] _eqn : eqa ; 
    try discriminate.  
  destruct (in_inv RA) as [EQ|CONS]. inv EQ. omega. 
  specialize (IH _ _ _ _ _ _ HB eqa l' h' k' Llth' Lplth). contradiction.
Qed.

(** Allocation succeeds if there is no overlapping block in the alloclist *)
Lemma alloc_success:
  forall a l h k,
    l < h -> (align_size (h - l) | l)->
    (forall l' h' k', range_allocated_al l' h' k' a -> h <= l' \/ h' <= l) ->
    exists a', alloc_in_alloclist l h k a = Some a'.
Proof.
  intro a. induction a as [|[lc hc kc] t IH].
  intros l h k LH ALG _.
  exists (mkmobj l h k :: nil); simpl; reflexivity.
  
  intros l h k LH ALG DISJ.
  unfold alloc_in_alloclist at 1.
  destruct (Z_le_dec h lc).
  (* We are insreting here - easy *)
  exists (mkmobj l h k :: mkmobj lc hc kc :: t). reflexivity.
  (* The recursive case - go to the IH: *)
  fold alloc_in_alloclist.
  assert (DISJIH: forall l' h' k', range_allocated_al l' h' k' t-> h <= l' \/ h' <= l).
  intros l' h' k' RA. apply (in_cons (mkmobj lc hc kc)) in RA.
  exact (DISJ l' h' k' RA).
  destruct (IH l h k LH ALG DISJIH) as [a' IH'].
  exists (mkmobj lc hc kc :: a').
  destruct (Z_le_dec hc l). destruct (alloc_in_alloclist l h k t).
  simpl; inv IH'; reflexivity.
  discriminate. 
  destruct (DISJ lc hc kc (in_eq _ _)); contradiction.
Qed.


  
(** Allocation preserves block validity... *)
Lemma alloc_preserves_block_validity:
  forall l h k, preserves_block_validity (alloc_block l h k).
Proof.
  intros l h k b b' ab bv.
  unfold alloc_block in ab.
  destruct (Z_le_dec 1 l) as [o_le_l | ]; 
    destruct (aligned_rng_dec l h) as [[l_lt_h alg] | ];
      destruct (Z_le_dec h Int.modulus) as [h_le_m | ]; 
        destruct (alloc_in_alloclist l h k (allocs b)) as [] _eqn: eqa;
          try discriminate.
  destruct bv as [UU [CO [x [xahb xm]]]].
  inv ab.
  split. 
  (* Unallocated are undef *)
  intros i. 
  simpl. intro NA. specialize (UU i). 
  destruct (range_in_allocated_al_dec i (i + 1) (allocs b)) as [RAP|RAN].
  destruct RAP as [k' RAP]; specialize (NA k'); elim NA; revert eqa RAP;
    apply alloc_preserves_in_allocated_al.
  specialize (UU RAN). assumption.

  split. (* cont_bytes_ok *)
    destruct CO as [C D].
    split; [done|].
    intros i n v G; specialize (D i n v G).
    destruct D as [[c [EQ [V [k' CA ALGN]]]] CC].
    split; [exists c; repeat split|]; try done.
    exists k'; try done.
    eby eapply alloc_preserves_in_allocated_al.
  
  (* Monotonicity of blocks *)
  exists (Zmax x h). 
  split.
  apply (alloc_preserves_alloclist_validity _ _ _ _ _ _ _ _
              o_le_l l_lt_h alg h_le_m o_le_l (Zle_refl _) eqa xahb).
  apply Zmax_case_strong; intros; omega.
Qed.

(** * Deallocation *)
Fixpoint free_in_alloclist (l : Z) (k : mobject_kind) 
                           (al : alloclist) : option (alloclist * Z) :=
  match al with
  | nil => None
  | mo :: t =>
      if zeq mo.(mobj_low) l 
        then if mobj_kind_eq mo.(mobj_kind) k 
          then Some(t, mo.(mobj_high)) (* found *)
          else None                    (* found, but kinds do not agree *)
        else match free_in_alloclist l k t with
               | None => None
               | Some (rt, rh) => Some (mo :: rt, rh)
             end
  end.

Fixpoint set_undef (l : Z) (n : nat) (cm : contentmap) : contentmap :=
  match n with
    | 0%nat => cm
    | S m => ZTree.remove l (set_undef (l + 1) m cm)
  end.


Definition clear_value (p: Z) (m: contentmap) : contentmap :=
  match ZTree.get p m with
    | Some (Datum n v) => set_undef p (S n) m
    | Some (Cont k) => 
        match ZTree.get (p - Z_of_nat k) m with
          | Some (Datum n v) => (set_undef (p - Z_of_nat k) (S n) m)
          | _ => m (* should never occur for valid contentmaps *)
        end
    | None => m
  end.

Fixpoint clear_values (p: Z) (n: nat) (m: contentmap) {struct n} : contentmap :=
  match n with 
    | O => m 
    | S n1 => clear_value p (clear_values (p+1) n1 m)
  end.

Definition free_block (l : Z) (k : mobject_kind) (m : block_contents) :
  option block_contents := 
  match free_in_alloclist l k (allocs m) with
    | None => None
    | Some (newal, h) => 
      Some(mkblock (clear_values l (Zabs_nat (h - l)) (contents m)) newal)
  end.

Lemma set_undef_spec_in:
  forall n l c i,
    i >= l -> i < l + Z_of_nat n -> ZTree.get i (set_undef l n c) = None.
Proof.
  intro n. induction n as [|n IH].
  (* Base case *)
  intros; simpl in *; omegaContradiction.
  (* Induction step *)
  intros. rewrite inj_S in *. simpl. 
  destruct (Z_eq_dec i l) as [IeqL|IneqL].
  rewrite IeqL. specialize (IH (l + 1) c i). apply ZTree.grs. 
  rewrite ZTree.gro; try done; try apply IH; omega.
Qed.

Lemma set_undef_spec_out:
  forall n l c i,
    i < l \/ i >= l + Z_of_nat n -> ZTree.get i (set_undef l n c) = ZTree.get i c.
Proof.
  intro n. induction n as [|n IH].
  (* Base case *)
  auto.

  (* Induction step *)
  intros; rewrite inj_S in *. 
  specialize (IH (l + 1) c i).
  simpl. destruct H; rewrite ZTree.gro; try apply IH; try (intro; clarify); omega.
Qed.

Lemma set_undef_preserves_undef:
  forall l n c i,
    ZTree.get i c = None -> ZTree.get i (set_undef l n c) = None.
Proof.
  intros l n c i CIU.
  destruct (dec_Zlt i l); destruct (dec_Zlt i (l + Z_of_nat n)); 
    try (rewrite <- CIU; apply set_undef_spec_out; omega);
      try apply set_undef_spec_in; omega.
Qed.

Lemma set_undef_some:
   forall p q n m v, ZTree.get p (set_undef q n m) = Some v -> ZTree.get p m = Some v.
Proof.
  intros until 0; revert p q; induction n; intros p q; simpl; try done. 
  by destruct (zeq p q); clarify; [rewrite ZTree.grs| rewrite ZTree.gro; [apply IHn|]].
Qed.

(*
Lemma set_undef_none:
   forall p q n m, ZTree.get p (set_undef q n m) = None -> 
           ZTree.get p m = None 
        \/ (exists v, ZTree.get p m = Some v /\ q <= p < q + Z_of_nat n).
Proof.
  intros until 0; revert p q; induction n; intros p q; auto.
  rewrite inj_S; simpl set_undef; destruct (zeq p q); clarify.
    destruct (ZTree.get q m); [right; eexists; split; [edone|omega]|by left].
  rewrite ZTree.gro; try done; intro H; destruct (IHn _ _ H) as [|[? [? ?]]]; [by left |].
  right; eexists; split; [edone|omega].
Qed.
*)

Lemma check_cont_inside:
  forall n k p m q,
  check_cont n k p m ->
  p <= q < p + Z_of_nat n ->
  ZTree.get q m = Some (Cont (k + Zabs_nat (q - p))).
Proof.
  induction n; intros.
    by unfold Z_of_nat in *; omegaContradiction.
  simpl in H. 
  assert (X: p = q \/ p + 1 <= q < (p + 1) + Z_of_nat n).
    rewrite inj_S in *. omega. 
  destruct X; clarify.
    rewrite Zminus_diag; simpl; rewrite plus_0_r.
    by destruct ZTree.get as [[]|]; try destruct eq_nat_dec; clarify. 
  destruct ZTree.get as [[]|]; try destruct eq_nat_dec; clarify. 
  exploit IHn; try edone; intro X; rewrite X. 
  rewrite Zminus_plus_distr; try (try (intro; clarify); omega).
  replace (Zabs_nat (q - p)) with (plus (Zabs_nat (q - p - 1)) (Zabs_nat 1)).
    by f_equal; f_equal; simpl; unfold nat_of_P; simpl; omega.
  rewrite <- (Zabs_nat_Zplus); try omega; f_equal; omega.
Qed.

Lemma check_cont_false_inside:
  forall n k p m,
  check_cont n k p m = false ->
  exists q, p <= q < p + Z_of_nat n /\
  ZTree.get q m <> Some (Cont (k + Zabs_nat (q - p))).
Proof.
  induction n; intros; [done|].
  simpl in H.
  rewrite inj_S. 
  destruct (ZTree.get p m) as [[]|] _eqn: EQ; 
    try (by exists p; rewrite EQ; split; [omega | red; intros; clarify]).
  destruct eq_nat_dec.
    2: exists p; rewrite EQ; split; [omega | red; intros; clarify].
    2: by rewrite Zminus_diag in *; simpl in *; rewrite plus_0_r in *.
  destruct (IHn _ _ _ H) as [q [A B]].
  exists q; split; [omega|].
  intro C; elim B; rewrite C; f_equal; f_equal.
  replace (Zabs_nat (q - p)) with (plus (Zabs_nat (q - (p + 1))) (Zabs_nat 1)).
    by simpl; unfold nat_of_P; simpl; omega.
  rewrite <- (Zabs_nat_Zplus); try omega; f_equal; omega.
Qed.


Lemma Z_of_nat_S: forall n, Z_of_nat (S n) = Z_of_nat n + 1.
Proof.
  by intros; replace 1 with (Z_of_nat 1); [rewrite <- inj_plus; f_equal; omega|]. 
Qed.


Lemma check_cont_spec:
  forall n k p m,
  if check_cont n k p m
  then (forall q, p <= q < p + Z_of_nat n -> ZTree.get q m = Some (Cont (k + Zabs_nat (q - p))))
  else (exists q, p <= q < p + Z_of_nat n /\ ZTree.get q m <> Some (Cont (k + Zabs_nat (q - p)))).
Proof.
  intros; case ifP; intros; [eby eapply check_cont_inside | eby eapply check_cont_false_inside].
Qed.

Lemma check_cont_true:
  forall n k p m,
  (forall q, p <= q < p + Z_of_nat n -> ZTree.get q m = Some (Cont (k + Zabs_nat (q - p)))) ->
  check_cont n k p m.
Proof.
  intros. generalize (check_cont_spec n k p m). 
  destruct (check_cont n k p m). auto.
  intros [q [A B]]. elim B; auto.
Qed.

Lemma check_cont_false:
  forall n k m p q,
  p <= q < p + Z_of_nat n -> ZTree.get q m <> Some (Cont (k + Zabs_nat (q - p))) ->
  check_cont n k p m = false.
Proof.
  intros. generalize (check_cont_spec n k p m). 
  destruct (check_cont n k p m).
  intros. elim H0; auto. 
  auto.
Qed.


Lemma between_dec : forall x y z, { x <= y <= z } + { y < x \/ z < y }.
Proof.
  intros; destruct (zle x y); [destruct (zle y z); [left|right]|right]; omega.
Qed.


Lemma clear_value_datum:
  forall (p q : Z) n v m al,
    cont_bytes_ok (mkblock m al) ->
    ZTree.get p m = Some (Datum n v) ->
    match ZTree.get p (clear_value q m) with 
      | None   => p <= q <= p + Z_of_nat n
      | Some (Datum n' v') => n' = n /\ v' = v /\ (q < p \/ q > p + Z_of_nat n)
      | Some _ => False
    end.
Proof.
  intros p q n v m al OK P.
    unfold clear_value. 
    destruct (zeq p q) as [|NE].
      by subst q; rewrite P, set_undef_spec_in; rewrite ?inj_S; omega.
  destruct (between_dec p q (p + Z_of_nat n)) as [BETW|nBETW].
    exploit (check_cont_inside _ _ _ _ q (proj2 (proj2 OK _ _ _ P))); try omega.
    simpl contents.
    intro Q; rewrite Q.
    rewrite inj_plus, inj_S, inj_Zabs_nat, Zabs_eq; try omega.
    simpl Zsucc.
    replace (q - (1 + (q - (p + 1)))) with p; try omega.
    rewrite P, set_undef_spec_in; rewrite ?inj_S; omega.

  destruct (ZTree.get q m) as [[]|] _eqn: Q; try rewrite P; repeat split; try done; try omega.

    destruct (between_dec q p (q + Z_of_nat n0)). 
      exploit (check_cont_inside _ _ _ _ p (proj2 (proj2 OK _ _ _ Q))); try omega. 
      by simpl contents; rewrite P; intro; clarify.

    rewrite set_undef_spec_out, P; rewrite ?inj_S; repeat split; try done; omega. 

  pose proof (proj1 OK _ _ Q) as [? [? Qm]]; simpl contents in *; rewrite Qm.

    destruct (zeq p (q - Z_of_nat n0)) as [|NE'].
      subst p; rewrite P in Qm; clarify; rewrite set_undef_spec_in; 
      rewrite ?inj_S, ?inj_plus; omega.

    destruct (between_dec (q - Z_of_nat n0) p (q + Z_of_nat x)). 
      exploit (check_cont_inside _ _ _ _ p (proj2 (proj2 OK _ _ _ Qm))).
        rewrite inj_plus; omega. 
      by simpl contents; rewrite P; intro; clarify.
    rewrite set_undef_spec_out, P; rewrite ?inj_S, ?inj_plus; repeat split; try done; omega. 
Qed.

Lemma set_undef_cont_bytes_ok:
  forall m al l n v,
   cont_bytes_ok (mkblock m al) ->
   ZTree.get l m = Some (Datum n v) -> 
   cont_bytes_ok (mkblock (set_undef l (S n) m) al).
Proof. 
  intros m al l n v [C D] G. 
  pose proof (D _ _ _ G) as DG.
  split; unfold contents, allocs in *.
    intros i n0 H.
    destruct (zlt i l). 
      by rewrite (set_undef_spec_out) in *; try omega; auto.
    destruct (zlt i (l + Z_of_nat (S n))). 
      by rewrite (set_undef_spec_in) in H; try omega; auto.
    rewrite (set_undef_spec_out) in H; try omega. 
    destruct (zeq i l); [by clarify; rewrite H in G; clarify|].
    destruct (zle i l); try omegaContradiction.
    destruct (zlt (i - Z_of_nat n0) l). 
      by rewrite (set_undef_spec_out) in *; try omega; auto. 
    destruct (zle (l + Z_of_nat (S n)) (i - Z_of_nat n0)).
      by rewrite (set_undef_spec_out) in *; try omega; auto.
    destruct (C _ _ H) as [? [? X]].
    rewrite !(Z_of_nat_S) in *.
    destruct (zeq (i - Z_of_nat n0) l). clarify.
      rewrite X in G; clarify; rewrite inj_plus in *.
      omegaContradiction.
    rewrite (check_cont_inside _ _ _ _ _ (proj2 DG)) in X; clarify; omega.
  intros i n0 v0 H.
  split.
    by apply (proj1 (D _ _ _ (set_undef_some _ _ _ _ _ H))).  
  apply check_cont_true; intros.
  destruct (zlt q l). 
    rewrite (set_undef_spec_out) in *; try omega.
    by apply (check_cont_inside _ _ _ _ _ (proj2 (D _ _ _ H))).
  destruct (zeq q l) as [|NE]; clarify.
    rewrite (set_undef_spec_out) in H; try omega.
    by rewrite (check_cont_inside _ _ _ _ l (proj2 (D _ _ _ H))) in G.  
  destruct (zlt l q); try omegaContradiction; clear NE.
  destruct (zlt i l); [| destruct (zlt i (l + Z_of_nat (S n)))];
    try (by rewrite set_undef_spec_in in H);
    rewrite (set_undef_spec_out) in H; try omega.
    destruct (zlt l (i + 1 + Z_of_nat n0)).
      by rewrite (check_cont_inside _ _ _ _ l (proj2 (D _ _ _ H))) in G; try omega.
    rewrite set_undef_spec_out; try omega.
    by apply (check_cont_inside _ _ _ _ q (proj2 (D _ _ _ H))).
  rewrite set_undef_spec_out; try omega.
  by apply (check_cont_inside _ _ _ _ q (proj2 (D _ _ _ H))).
Qed.


Lemma clear_value_cont_bytes_ok:
  forall p m al,
   cont_bytes_ok (mkblock m al) ->
   cont_bytes_ok (mkblock (clear_value p m) al).
Proof.
  unfold clear_value; intros p m al OK.
  destruct (ZTree.get p m) as [[]|] _eqn: EQ; try done.
    apply (set_undef_cont_bytes_ok _ _ _ _ _ OK EQ).
  destruct (proj1 OK _ _ EQ) as (? & ? & X); unfold contents in X; rewrite X.
  apply (set_undef_cont_bytes_ok _ _ _ _ _ OK X).
Qed.

Lemma clear_values_cont_bytes_ok:
  forall n p m al,
   cont_bytes_ok (mkblock m al) ->
   cont_bytes_ok (mkblock (clear_values p n m) al).
Proof. 
  induction n; intros; [done|].
  by apply clear_value_cont_bytes_ok; apply IHn.
Qed.


Lemma clear_value_some:
  forall p q m v,
   ZTree.get p (clear_value q m) = Some v -> ZTree.get p m = Some v.
Proof.
  unfold clear_value; intros p q m v H; simpl in *. 
  destruct (ZTree.get q m) as [[]|]; try done.
    by apply (set_undef_some _ _ (S _) _ _ H). 
  destruct (ZTree.get (q - Z_of_nat n) m) as [[]|]; try done.
  by apply (set_undef_some _ _ (S _) _ _ H). 
Qed.

Lemma clear_values_some:
  forall n p q m v,
   ZTree.get p (clear_values q n m) = Some v -> ZTree.get p m = Some v.
Proof.
  induction n; intros; try done.
  eby eapply IHn; eapply clear_value_some.
Qed.


Lemma clear_value_none:
  forall p q m,
    ZTree.get p m = None ->
    ZTree.get p (clear_value q m) = None.
Proof.
  unfold clear_value; intros.
  destruct (ZTree.get q m) as [[]|]; try done.
    by apply set_undef_preserves_undef.
  destruct (ZTree.get (q - Z_of_nat n) m) as [[]|]; try done.
    by apply set_undef_preserves_undef.
Qed.

Lemma clear_values_none:
  forall p n q m,
    ZTree.get p m = None ->
    ZTree.get p (clear_values q n m) = None.
Proof.
  induction n; intros; simpl; try done. 
  by apply clear_value_none; apply IHn.
Qed.

Lemma clear_values_datum:
  forall (p q : Z) n1 n v m al,
    cont_bytes_ok (mkblock m al) ->
    ZTree.get p m = Some (Datum n v) ->
    match ZTree.get p (clear_values q n1 m) with 
     | None   => p <= q + Z_of_nat n1 - 1 /\ q <= p + Z_of_nat n 
     | Some (Datum n' v') => n' = n /\ v' = v 
               /\ (n1 = O \/ q + Z_of_nat n1 - 1 < p \/ q > p + Z_of_nat n) 
     | Some _ => False
    end.
Proof.
  intros p q n1 n v m al OK P; revert q; induction n1; simpl; intros q.
    simpl; rewrite P; repeat split; try done; omega.
  rewrite Zpos_P_of_succ_nat.
  specialize (IHn1 (q + 1)).
  destruct (ZTree.get p (clear_values (q + 1) n1 m)) as [[]|] _eqn: Pc; clarify.
    destruct IHn1 as [-> [-> X]].
  
    pose proof (clear_value_datum _ q _ _ _ _ (clear_values_cont_bytes_ok _ _ _ _ OK) Pc) as CL.
    destruct (ZTree.get p (clear_value q (clear_values (q + 1) n1 m))) as [[]|] _eqn: M; try done.
      destruct CL as [? [? ?]]; repeat split; try done; omega.
    omega.

  rewrite (clear_value_none _ _ _ Pc); omega.
Qed.


Lemma clear_value_in:
  forall (p : Z) m al,
    cont_bytes_ok (mkblock m al) ->
    ZTree.get p (clear_value p m) = None.
Proof.
  unfold clear_value; intros p m al OK.
  destruct (ZTree.get p m) as [[]|] _eqn: EQ; try done.
    apply set_undef_spec_in; rewrite ?inj_S; omega.
  pose proof (proj1 OK _ _ EQ) as [? [? X]]; unfold contents in X; rewrite X.
  apply set_undef_spec_in; rewrite ?inj_S, ?inj_plus; omega.   
Qed.

Lemma clear_values_in:
  forall (p q : Z) n m al,
    cont_bytes_ok (mkblock m al) ->
    q <= p ->
    p < q + Z_of_nat n ->
    ZTree.get p (clear_values q n m) = None.
Proof.
  intros p q n; revert q; induction n; simpl; intros.
    omegaContradiction. 
  rewrite Zpos_P_of_succ_nat in *.
  destruct (zeq p q); clarify.
    eby eapply clear_value_in; apply clear_values_cont_bytes_ok.
  apply clear_value_none; eapply IHn; try edone; omega.
Qed.


Lemma free_mem_in_alloclist:
  forall l h k al al',
    free_in_alloclist l k al = Some(al', h) -> In (mkmobj l h k) al.
Proof.
  intros l h k al.
  induction al as [| a al IH]. 
  intro al'; simpl; discriminate.

  intro al'; destruct a as [lc hc kc].
  simpl. intro H. 
  destruct (mobj_kind_eq kc k); destruct (zeq lc l);
      try (injection H; intros; left; congruence);
        try destruct (free_in_alloclist l k al) as [[rt rh]|]; try discriminate;
          inv H; right; apply (IH rt); reflexivity.
Qed.

Lemma free_hight_gt_low:
  forall l h k a b al al',
    alloclist_hbound a al = Some b ->
    free_in_alloclist l k al = Some(al', h) -> l < h.
Proof.
  intros l h k a b al al' HBND FA.
  apply free_mem_in_alloclist in FA.
  apply (alloclist_hbound_impl_l_lt_h HBND FA).
Qed.
 
(** Invariant preservation for deallocation *) 
Lemma alloclist_lower_lbnd_hbnd:
  forall al l h ol,
    ol <= l ->
    alloclist_hbound l al = Some h ->
    alloclist_hbound ol al = Some h \/
    alloclist_hbound ol al = Some ol.
Proof.
  intros al.
  induction al as [|lhc t IH]. 
  simpl; tauto.
  
  intros l h ol Lt_ol_l.
  destruct lhc as [lc hc].
  destruct (zeq lc l) as [Eq_lc_l | Neq_lc_l].
  simpl; rewrite Eq_lc_l in *.
  destruct (aligned_rng_dec l hc) as [[]|]; 
    destruct (Z_le_dec l l); destruct (Z_le_dec ol l);
      try (intros; discriminate); try tauto.
  
  simpl.
  destruct (aligned_rng_dec lc hc) as [[]|]; destruct (Z_le_dec l lc);
    try (intros; discriminate).
  assert (Le_ol_hc : hc <= hc). omega.
  intro HBND. specialize (IH _ _ _ Le_ol_hc HBND). 
  destruct (Z_le_dec ol lc); try omegaContradiction; tauto.
Qed.

Lemma free_preserves_hbound_validity:
  forall al l k al' h hbnd lbnd,
    free_in_alloclist l k al = Some(al', h) ->
    alloclist_hbound lbnd al = Some hbnd ->
    exists hbnd', lbnd <= hbnd' /\ hbnd' <= hbnd /\
      alloclist_hbound lbnd al' = Some hbnd'.
Proof.
  intro al; induction al as [|a al IH]. 
  
  (* Base case. *)
  intros; simpl; discriminate.

  (* Step case *)
  intros l k al' h hbnd lbnd.
  intro FA. simpl in FA. destruct a as [lc hc kc]. simpl in FA.
  destruct (zeq lc l). destruct(mobj_kind_eq kc k); try done.
  inv FA. simpl. intro HBND.
  destruct (aligned_rng_dec l h) as [[]|]; destruct (Z_le_dec lbnd l); 
    try discriminate.
  assert (Le_lbnd_h: lbnd <= h). omega.
  pose proof (alloclist_lbnd_lt_hbnd HBND).
  destruct (alloclist_lower_lbnd_hbnd _ _ _ _ Le_lbnd_h HBND) as [IHBND|IOL].
  exists hbnd; repeat split; try omega; auto.
  exists lbnd; repeat split; try omega; auto.
  
  simpl; intro HBND.
  destruct (aligned_rng_dec lc hc) as [[]|]; destruct (Z_le_dec lbnd lc); 
    destruct (free_in_alloclist l k al) as [[rall rh]|] _eqn : FAE; try discriminate.
  assert (Le_lbnd_hc: lbnd <= hc). omega.
  destruct (IH _ _ _ _ _ _ FAE HBND) as [hbnd' [H1 [H2 H3]]].
  injection FA as ALP RH. rewrite ALP, <- RH in *.
  exists hbnd'. simpl. 
  destruct (aligned_rng_dec lc hc) as [[]|]; destruct (Z_le_dec lbnd lc); 
    destruct (free_in_alloclist l k al); try discriminate; 
      repeat split; try omega; tauto.
Qed.

Lemma free_in_alloclist_fw:
  forall a na l h k,
    free_in_alloclist l k a = Some (na, h) ->
    forall l' h' k', 
      range_allocated_al l' h' k' a ->
      range_allocated_al l' h' k' na \/ (l' = l /\ h' = h /\ k' = k).
Proof.
  intro a. induction a as [|[lc hc kc] atl IH].
  intros na l h k FIA l' h' k' RA. destruct RA.

  (* Step case *)  
  intros na l h k FIA l' h' k' RA.
  simpl in FIA. 
  destruct (zeq lc l). destruct (mobj_kind_eq kc k); try done.
  inv FIA.
  unfold range_allocated_al in RA. 
  destruct (in_inv RA) as [HD | TL]. inv HD. 
    right; repeat split; reflexivity.
    left; assumption.

  destruct (free_in_alloclist l k atl) as [[rl rh]|] _eqn : FIAE; try discriminate.
  injection FIA as RH NA. rewrite RH, <- NA in *.
  destruct (in_inv RA) as [HD | TL]. inv HD.  
  left. apply in_eq.
  destruct (IH _ _ _ _ FIAE _ _ _ TL) as [IH1 | [IHl IHh]]. 
  left. apply in_cons. assumption.
  right. auto.
Qed.

Lemma free_in_alloclist_bw:
  forall a na l h k,
    free_in_alloclist l k a = Some (na, h) ->
    forall l' h' k', 
      range_allocated_al l' h' k' na ->
      range_allocated_al l' h' k' a.
Proof.
  intro a. induction a as [|[lc hc kc] atl IH].
  intros na l h k FIA. simpl in FIA. discriminate.

  (* Step case *)  
  intros na l h k FIA l' h' k' RA.
  simpl in FIA. 
  destruct (zeq lc l). destruct (mobj_kind_eq kc k); try done.
  (* lc = l *)
    inv FIA; apply in_cons; done.

  (* lc <> l *)
  destruct (free_in_alloclist l k atl) as [[rl rh]|] _eqn : FIAE; try done.
  inv FIA. destruct (in_inv RA) as [HD | TL].
    inv HD. apply in_eq.
    specialize (IH _ _ _ _ FIAE _ _ _ TL); apply in_cons; assumption.
Qed.

Lemma free_must_have_been_allocated:
  forall a na l h k,
    free_in_alloclist l k a = Some (na, h) ->
      range_allocated_al l h k a.
Proof.
  intro a. induction a as [|[lc hc kc] atl IH].
  intros na l h k FIA. simpl in FIA. discriminate.

  (* Step case *)  
  intros na l h k FIA.
  simpl in FIA. 
  destruct (zeq lc l). destruct (mobj_kind_eq kc k); try done.
  (* lc = l *)
    inv FIA. apply in_eq.

  (* lc <> l *)
  destruct (free_in_alloclist l k atl) as [[rl rh]|] _eqn : FIAE; try done.
  inv FIA. apply in_cons. apply (IH _ _ _ _ FIAE).
Qed.

Lemma free_fail:
  forall a lbnd hbnd l k,
    alloclist_hbound lbnd a = Some hbnd ->
    free_in_alloclist l k a = None ->
      forall h, ~ range_allocated_al l h k a.
Proof.
  intro a. induction a as [|[lc hc kc] atl IH].
  by intros.

  (* Step case *)  
  intros lbnd hbnd l k AHBND FIA h AL.
  simpl in FIA, AHBND. 
  destruct (aligned_rng_dec lc hc) as [[]|]; try done.
  destruct (Z_le_dec lbnd lc); try done.
    destruct (zeq lc l) as [-> | N]. destruct (mobj_kind_eq kc k); try done.
    unfold range_allocated_al in AL. simpl in AL. 
    destruct AL as [AL|AL]; clarify; try done.
    by pose proof (alloclist_hbound_impl_l_lt_h AHBND AL); omega.
  destruct (free_in_alloclist l k atl) as [[rt rh]|] _eqn : FIAE; 
    simpl in FIA; try done.
  unfold range_allocated_al in AL. simpl in AL. 
  destruct AL as [AL|AL]; clarify; try done.
  eby eapply IH.
Qed.

Lemma free_frees:
  forall a na lbnd hbnd l h k,
    alloclist_hbound lbnd a = Some hbnd ->
    free_in_alloclist l k a = Some (na, h) ->
    forall l' h' k',
      range_allocated_al l' h' k' na ->
      h' <= l \/ h <= l'.
Proof.
  intro a. induction a as [|[lc hc kc] atl IH].
  intros na _ _ l h k _ FIA. simpl in FIA. discriminate.

  (* Step case *)  
  intros na lbnd hbnd l h k HB FIA l' h' k' RA.
  simpl in FIA. simpl in HB. 
  destruct (aligned_rng_dec lc hc) as [[Ltlhc Alg] | ?]; 
    destruct (Z_le_dec lbnd lc) as [Lellc | ?]; try discriminate.
  destruct (zeq lc l). destruct (mobj_kind_eq kc k); try done.
  (* lc = l *)
    inv FIA.
    pose proof (alloclist_hbound_impl_l_lt_h HB RA). omega.

  (* lc <> l *)
  destruct (free_in_alloclist l k atl) as [[rl rh]|] _eqn : FIAE; try discriminate.
  inv FIA.
  destruct (in_inv RA) as [HD | TL].  
    inv HD. apply free_must_have_been_allocated  in FIAE.
    pose proof(alloclist_hbound_impl_l_lt_h HB FIAE). omega.
    
    exact (IH _ _ _ _ _ _ HB FIAE _ _ _ TL).
Qed.

Lemma free_preserves_block_validity:
  forall l k, preserves_block_validity (free_block l k).
Proof.
  intros l k b [a' c'] FB BV.
  unfold free_block in FB.
  destruct (free_in_alloclist l k b.(allocs)) as [[na h] |] _eqn : EQFA; clarify. 
  destruct BV as [UU [CO [bnd [HBND BNDM]]]].
  split.
  (* Unallocated are Undef *)
    intro i. simpl.
    specialize (UU i). intro NA.
    destruct (range_in_allocated_al_dec i (i + 1) (allocs b)) as 
      [[kc [lc [hc [RAP [Lci Hci]]]]]|RAN].
      destruct (free_in_alloclist_fw _ _ _ _ _ EQFA _ _ _ RAP).
        elim (NA kc); exists lc; exists hc; tauto.
      destruct b.
      eapply clear_values_in; try edone; rewrite ?inj_Zabs_nat, ?Zabs_eq; omega. 
    by apply clear_values_none; apply UU. 
  split. 
      destruct b as [m al]; simpl.
      pose proof (clear_values_cont_bytes_ok (Zabs_nat (h - l)) l _ _ CO) as [C D].
      split; [by apply C|clear C]. unfold contents, allocs in *.
      intros i n v G; specialize (D i n v G); simpl in *.
      destruct D as ((c & ? & ? & k' & l' & h' & RA & ? & ?) & ?); split; try done.
      exists c; repeat split; try done.
      exists k'; try done; exists l'; exists h'; simpl in *; split; try done.
      pose proof (free_in_alloclist_fw _ _ _ _ _ EQFA _ _ _ RA) as [|(? & ? & ?)]; [done|].
      clarify.  
      erewrite clear_values_in in G; try edone; rewrite ?inj_Zabs_nat, ?Zabs_eq; 
        destruct c; simpl in *; omega.
  (* hbound exists and is less than the modulus *)
  destruct (free_preserves_hbound_validity _ _ _ _ _ _ _ EQFA HBND) 
    as [hbnd' [HBND1 [HBNDmax HBND']]].
  exists hbnd'; split; auto; omega. 
Qed.
  
(** Memory stores and loads *)

Definition getN (n: nat) (p: Z) (m: contentmap) : val :=
  match ZTree.get p m with
  | Some (Datum n' v) =>
      if eq_nat_dec n n' then v else Vundef
  | _ =>
      Vundef
  end.

Fixpoint set_cont (n k: nat) (p: Z) (m: contentmap) {struct n} : contentmap :=
  match n with
  | O => m
  | S n1 => ZTree.set p (Cont k) (set_cont n1 (S k) (p + 1) m)
  end.

Definition setN (n: nat) (p: Z) (v: val) (m: contentmap) : contentmap :=
  ZTree.set p (Datum n v) (set_cont n 1 (p + 1) (clear_values p (S n) m)).

Lemma set_cont_inside:
  forall n k p m q,
  p <= q < p + Z_of_nat n ->
  ZTree.get q (set_cont n k p m) = Some (Cont (k + Zabs_nat (q - p))).
Proof.
  induction n; intros.
  unfold Z_of_nat in H. omegaContradiction.
  simpl. 
  assert (p = q \/ p + 1 <= q < (p + 1) + Z_of_nat n).
    rewrite inj_S in H. omega. 
  elim H0; intro.
  subst q. rewrite ZTree.gss, Zminus_diag. simpl; f_equal; f_equal; omega. 
  rewrite ZTree.gso, IHn, Zminus_plus_distr; try (try (intro; clarify); omega).
  replace (Zabs_nat (q - p)) with (plus (Zabs_nat (q - p - 1)) (Zabs_nat 1)).
    by f_equal; f_equal; simpl; unfold nat_of_P; simpl; omega.
  rewrite <- (Zabs_nat_Zplus); try omega; f_equal; omega.
Qed.

Lemma set_cont_outside:
  forall n k p m q,
  q < p \/ p + Z_of_nat n <= q ->
  ZTree.get q (set_cont n k p m) = ZTree.get q m.
Proof.
  induction n; intros.
  simpl. auto.
  simpl. rewrite inj_S in H. 
  rewrite ZTree.gso. apply IHn. omega. intro; clarify; omega.
Qed.

Lemma check_cont_set_inside:
  forall n k p q n' v m, p <= q < p + Z_of_nat n ->
   check_cont n k p (ZTree.set q (Datum n' v) m) = false.
Proof.
  induction n; intros; simpl.
    simpl in *; omegaContradiction.
  destruct (zeq p q); clarify.
    by rewrite ZTree.gss.
  rewrite ZTree.gso, IHn; try done;
  replace (Z_of_nat (S n)) with (Z_of_nat 1 + Z_of_nat n) in *;
   try (by rewrite <- inj_plus); 
  simpl Z_of_nat in *.
    by destruct ZTree.get as [[]|]; try destruct eq_nat_dec.
  omega.
Qed.

Lemma check_cont_set_outside:
  forall n k p q v m, q < p \/ p + Z_of_nat n <= q ->
   check_cont n k p (ZTree.set q v m) =
   check_cont n k p m.
Proof.
  induction n; intros; try done; simpl.
  rewrite ZTree.gso, IHn; try done;
  replace (Z_of_nat (S n)) with (Z_of_nat 1 + Z_of_nat n) in *;
   try (by rewrite <- inj_plus); 
  simpl Z_of_nat in *. 
   omega.
  intro X; clarify; omega.
Qed.

Lemma check_cont_set_cont_same:
  forall (n n' : nat) (z : Z) m, check_cont n n' z (set_cont n n' z m) = true.
Proof.
  induction n; simpl; intros; try done.
  rewrite ZTree.gss, dec_eq_true, check_cont_set_outside, IHn; try done; omega.
Qed.


Lemma check_cont_set_cont_outside:
  forall n k p n' k' q m, 
     p + Z_of_nat n < q \/ q + Z_of_nat n' < p ->
     check_cont n k p (set_cont n' k' q m) = check_cont n k p m.
Proof.
  induction n'; intros; simpl; try rewrite check_cont_set_outside, IHn'; try done;
  replace (Z_of_nat (S n')) with (Z_of_nat 1 + Z_of_nat n') in *;
   try (by rewrite <- inj_plus); 
  simpl Z_of_nat in *;
  omega.
Qed.

Lemma getN_clear_value_same:
  forall (p : Z) n m,
    getN n p (clear_value p m) = Vundef.
Proof.
  intros; unfold clear_value, getN.
  destruct (ZTree.get p m) as [[]|] _eqn: X; try rewrite X; try done.
    rewrite set_undef_spec_in; try done; rewrite ?inj_S; omega.
  destruct (ZTree.get (p - Z_of_nat n0) m) as [[]|] _eqn: Y; try rewrite X; try done.
  destruct (ZTree.get p (set_undef (p - Z_of_nat n0) (S n1) m)) as [[]|] _eqn: Z; try done.
  by apply set_undef_some in Z; rewrite X in Z.
Qed.

Lemma getN_setN_same:
  forall n p v m,
  getN n p (setN n p v m) = v.
Proof.
  intros. unfold getN, setN. rewrite ZTree.gss.
  destruct eq_nat_dec; simpl; clarify.
Qed.

Lemma getN_clear_values_other:
  forall n1 n2 p1 p2 m al,
  cont_bytes_ok (mkblock m al) ->
  p1 + Z_of_nat n1 < p2 \/ p2 + Z_of_nat n2 < p1 ->
  getN n2 p2 (clear_values p1 (S n1) m) = getN n2 p2 m.
Proof.
  intros n1 n2 p1 p2 m al OK H. unfold getN.
  destruct (ZTree.get p2 m) as [[]|] _eqn: X; clarify.
      apply clear_values_datum with (q := p1) (n1 := (S n1)) (al:=al) in X; try done.
      rewrite inj_S in *.
      destruct ZTree.get as [[]|]; try done.
        by destruct X as [-> [-> ?]].
      destruct eq_nat_dec; clarify.
      omegaContradiction.
    destruct (ZTree.get p2 (clear_values p1 (S n1) m)) as [[]|] _eqn: Y; try done.
    by rewrite (clear_values_some _ _ _ _ _ Y) in X.
  by rewrite (clear_values_none _ _ _ _ X).
Qed.

Lemma getN_setN_other:
  forall n1 n2 p1 p2 v m al,
  cont_bytes_ok (mkblock m al) ->
  p1 + Z_of_nat n1 < p2 \/ p2 + Z_of_nat n2 < p1 ->
  getN n2 p2 (setN n1 p1 v m) = getN n2 p2 m.
Proof.
  intros n1 n2 p1 p2 v m al [C D] H. unfold getN, setN.
  rewrite ZTree.gso; [|intro X; clarify; omega].
  rewrite set_cont_outside; [|omega].
  eby eapply getN_clear_values_other.
Qed.

Lemma getN_clear_values_overlap:
  forall n1 n2 p1 p2 m al,
  cont_bytes_ok (mkblock m al) ->
  p1 + Z_of_nat n1 >= p2 -> p2 + Z_of_nat n2 >= p1 ->
  getN n2 p2 (clear_values p1 (S n1) m) = Vundef.
Proof.
  intros n1 n2 p1 p2 m al OK H1 H2. unfold getN, setN.
  destruct (ZTree.get p2 (clear_values p1 (S n1) m)) as [[]|] _eqn: G2c; try done.   
  destruct eq_nat_dec; clarify.
  pose proof (clear_values_some _ _ _ _ _ G2c) as G2.
  apply clear_values_datum with (q:=p1) (n1:=S n1) (al:=al) in G2; try done.
  rewrite G2c, inj_S in G2; omegaContradiction.
Qed.

Lemma getN_setN_overlap:
  forall n1 n2 p1 p2 v m al,
  cont_bytes_ok (mkblock m al) ->
  p1 <> p2 ->
  p1 + Z_of_nat n1 >= p2 -> p2 + Z_of_nat n2 >= p1 ->
  getN n2 p2 (setN n1 p1 v m) = Vundef.
Proof.
  intros n1 n2 p1 p2 v m al OK H H1 H2. unfold getN, setN.
  rewrite ZTree.gso; auto. 
  destruct (zlt p2 p1); [|rewrite set_cont_inside; auto; omega].
  rewrite set_cont_outside; [|omega].
  eby eapply getN_clear_values_overlap.
Qed.

Lemma getN_setN_mismatch:
  forall n1 n2 p v m,
  n1 <> n2 ->
  getN n2 p (setN n1 p v m) = Vundef.
Proof.
  intros. unfold getN, setN. rewrite ZTree.gss. 
  unfold proj_sumbool; rewrite dec_eq_false; simpl. auto. auto.
Qed.

Lemma getN_setN_characterization:
  forall m al v n1 p1 n2 p2,
  cont_bytes_ok (mkblock m al) ->
  getN n2 p2 (setN n1 p1 v m) = v
  \/ getN n2 p2 (setN n1 p1 v m) = getN n2 p2 m
  \/ getN n2 p2 (setN n1 p1 v m) = Vundef.
Proof.
  intros. destruct (zeq p1 p2). subst p2.
  destruct (eq_nat_dec n1 n2). subst n2.
  left; apply getN_setN_same.
  right; right; apply getN_setN_mismatch; auto.
  destruct (zlt (p1 + Z_of_nat n1) p2).
  right; left; eapply getN_setN_other; eauto.
  destruct (zlt (p2 + Z_of_nat n2) p1).
  right; left; eapply getN_setN_other; eauto.
  right; right; eapply getN_setN_overlap; eauto; omega.
Qed.

Lemma getN_empty:
  forall n p,
  getN n p (ZTree.empty _) = Vundef.
Proof.
  by intros; unfold getN; rewrite ZTree.gempty.
Qed.

Lemma getN_setundef_other:
  forall n p n' p' cm,
    (p + Z_of_nat n < p' \/ p' + Z_of_nat n' <= p) ->
    getN n p (set_undef p' n' cm) = getN n p cm.
Proof.
  intros n p n' p' cm Ineq.
  unfold getN. rewrite !set_undef_spec_out; try omega.
  destruct (ZTree.get p cm) as [[m|]|]; try done. 
Qed.

(* The block after a store of value [v] at offset [ofs] in block [b]. *)
Definition unchecked_store_map
     (chunk: memory_chunk) (ofs: Z) (v: val) (b : block_contents) : block_contents :=
     mkblock (match stored_value chunk v with
              | Some w => setN (pred_size_chunk chunk) ofs w b.(contents)
              | None => clear_values ofs (S (pred_size_chunk chunk)) b.(contents)
              end)
              b.(allocs).

(** [store_in_block chunk ofs v b] perform a write in block [b].
  Value [v] is stored at address [ofs].
  Returns the updated block, or [None] if the address is invalid
  or the memory access is out of bounds. *)
Definition store_in_block (chunk: memory_chunk) (ofs: Z) (v: val) 
                          (b : block_contents) : option block_contents :=
  if in_block chunk (allocs b) ofs
  then Some(unchecked_store_map chunk ofs v b)
  else None.

Lemma store_in_block_inv:
  forall chunk b ofs v b',
  store_in_block chunk ofs v b = Some b' ->
  valid_access chunk ofs (allocs b) /\
  b' = unchecked_store_map chunk ofs v b.
Proof.
  intros until b'; unfold store_in_block.
  destruct (in_block chunk (allocs b) ofs); intros.
    split; auto; congruence.
  congruence.
Qed.

Lemma cont_bytes_ok_setN:
  forall p c v m al,
  cont_bytes_ok (mkblock m al) ->
  valid_access c p al ->
  value_chunk_ok c v ->
  cont_bytes_ok (mkblock (setN (pred_size_chunk c) p v m) al).
Proof.
  intros p c v m al OK VACC LRES.
  unfold setN.
  split; unfold contents.
   generalize (pred_size_chunk c); intros n i n0 H0.
   intros.
   unfold ZTree.elt in *.
   destruct (zeq i p); clarify.
     by rewrite ZTree.gss in H0.
   rewrite ZTree.gso in H0; try done.
  destruct (between_dec (p + 1) i (p + Z_of_nat n)). 
    rewrite set_cont_inside in H0; [clarify | omega].
    rewrite inj_S, inj_Zabs_nat, Zabs_eq; try omega.
    replace (i - Zsucc (i - (p + 1))) with p; [|omega].
    rewrite ZTree.gss.
    eexists ((n - S (Zabs_nat (i - (p + 1))))%nat); eexists v.
    f_equal; f_equal; apply inj_eq_rev.
    rewrite inj_plus, inj_minus, inj_S, inj_Zabs_nat, Zabs_eq, Zmax_right; omega.
  rewrite set_cont_outside in H0; [|omega].
(*  apply clear_values_cont_bytes_ok with (n:=S n) (p:=p) in H. *)
  pose proof (proj1 (clear_values_cont_bytes_ok _ _ _ _ OK) _ _ H0) as (? & ? & G); unfold contents in G.
  assert (G' := clear_values_some _ _ _ _ _ G).
  apply clear_values_datum with (q:=p) (n1:= S n) (al:=al) in G'; try done.
  rewrite G in G'; destruct G' as [_ [_ [|G']]]; [done|].
  rewrite inj_S, inj_plus in *.
  rewrite ZTree.gso; [|intro; subst; omega].
  rewrite set_cont_outside; [|omega].
  eby do 2 eexists.
  
  intros i n0 v0 G.
  split. 
    destruct (zeq i p) as [->|].
      rewrite ZTree.gss in G; clarify.
      eby eexists c.
    rewrite ZTree.gso in G; try done.
    destruct (between_dec (p (*+ 1*)) i (p + Z_of_nat (pred_size_chunk c))). 
      by rewrite set_cont_inside in G; [|omega].
    rewrite set_cont_outside in G; [|omega].
    by apply (proj1 (proj2 OK _ _ _ (clear_values_some _ _ _ _ _ G))).

  revert G; generalize (pred_size_chunk c); intros n G.
  apply check_cont_true.
  intros q BTW.
  destruct (zeq i p) as [->|].
    rewrite ZTree.gss in G; clarify.
    rewrite ZTree.gso; [|intro; clarify; omegaContradiction].
    rewrite set_cont_inside; try done; omega.
  rewrite ZTree.gso in G; try done.
  destruct (between_dec (p (*+ 1*)) i (p + Z_of_nat n)). 
    by rewrite set_cont_inside in G; [|omega].
  rewrite set_cont_outside in G; [|omega].
  assert (G' := clear_values_some _ _ _ _ _ G).
  apply clear_values_datum with (q:=p) (n1:= S n) (al:=al) in G'; try done.
  rewrite G, inj_S in G'.
  destruct G' as [_ [_ [|]]]; try done.
  destruct (zeq q p); clarify.
    omegaContradiction.
  rewrite ZTree.gso; try done.
  rewrite set_cont_outside; [|omega].
  apply (check_cont_inside _ _ _ _ q (proj2 (proj2 (clear_values_cont_bytes_ok _ _ _ _ OK) _ _ _ G)) BTW).
Qed.
  

Lemma store_preserves_block_validity:
  forall chunk ofs v, 
    preserves_block_validity (store_in_block chunk ofs v).
Proof.
  intros chunk ofs v b b' SM [UAU [CONT BV]]. 
  apply store_in_block_inv in SM. destruct SM as [[kc CA ALGN] US].
  split.
    (* Unallocated are undef *)
    intros i NRA.
    specialize (UAU i).
    rewrite US in NRA; simpl in NRA.
    specialize (UAU NRA).
    rewrite US. unfold unchecked_store_map. simpl.
    unfold setN. destruct CA as [lc [hc cbetw]].
    destruct (stored_value chunk v) as [|] _eqn: SVeq.
    2: by apply clear_value_none; apply clear_values_none.
    rewrite ZTree.gso, set_cont_outside. by apply clear_values_none. 
    rewrite <- Zplus_assoc, <- size_chunk_pred.
    assert(nbetw: ~ (ofs < i < ofs + size_chunk chunk)).
      by intro betw; elim (NRA kc); exists lc; exists hc; split; [tauto|omega].
    omega. intro ofsni. elim (NRA kc). exists lc; exists hc; split. tauto.
    pose proof (size_chunk_pos chunk); subst; omega.
  split; subst; try done.
  unfold unchecked_store_map.   
  destruct (stored_value chunk v) as [|] _eqn: SVeq.
    pose proof (stored_value_ok _ _ _ SVeq) as [c' [SZeq VOK]]; rewrite SZeq.
    apply cont_bytes_ok_setN; try done.
    by constructor 1 with (k:=kc); destruct chunk; destruct v; clarify; destruct c'.
  apply clear_value_cont_bytes_ok.
  by apply clear_values_cont_bytes_ok.
Qed.

(*=========================================================================*)
(** * Lifting of block operations to memory. *)

(* The memory contents map a block id to its the block's contents.
   The option None stands for a disabled block, i.e., block, which
   is impossible to access. *)

Definition mem_contents : Type := ZTree.t block_contents.
    
Definition mem_bounded (m : mem_contents) : Prop :=
  exists b, forall i, i > b -> (ZTree.get i m = None).


(** Memory is valid if the number of blocks is bounded and
    all blocks are valid. *)
Definition mem_valid (m : mem_contents) (blegal : mem_restr): Prop :=
  mem_bounded m /\ 
  (forall b x, ZTree.get b m = Some x -> blegal b /\ block_valid x /\ x <> empty_block).

(** We package the proof of validity with the memory *)
Record mem : Type := 
  mkmem {
    mcont: mem_contents;
    mrestr: mem_restr;
    mvalid: mem_valid mcont mrestr
  }.

(** Empty memory *)

Lemma empty_mem_valid: forall bl, mem_valid (ZTree.empty _) bl.
Proof.
  split; [by exists 0; intros; apply ZTree.gempty|].
  by intros until 0; rewrite ZTree.gempty.
Qed.

Definition empty bl : mem := mkmem (ZTree.empty _) bl (empty_mem_valid bl).

(** * Generic lifting of block operations to memory content operations. *)

Definition block_contents_o2e (bo: option block_contents) := 
  match bo with
  | None => empty_block
  | Some b => b
  end.

Definition block_contents_e2o (b: block_contents) := 
  if block_contents_eq_dec b empty_block then None else Some b.

Definition blockop_to_memop (f : block_contents -> option block_contents) 
                            (b : Z)
                            (bl : mem_restr)
                            (m : mem_contents) 
                            : option mem_contents :=
 if bl b then
   match f (block_contents_o2e (ZTree.get b m)) with
   | Some bc => 
       Some (if block_contents_eq_dec bc empty_block then ZTree.remove b m 
             else ZTree.set b bc m)
   | None => None
   end
 else None.

(** Non interference of block transformer with other blocks. *)
Lemma blockop_to_memop_inv:
  forall m b bl f m' b',
    blockop_to_memop f b bl m = Some m' ->
    b <> b' ->
    ZTree.get b' m = ZTree.get b' m'.
Proof.
  intros; unfold blockop_to_memop in *. 
  destruct (bl b); clarify.
  by destruct f; clarify; destruct block_contents_eq_dec; clarify; 
     rewrite ?ZTree.gro, ?ZTree.gso; try intro; clarify.
Qed.

(** Lifting of block validity preservation to memory validity preservation. *)
Lemma blockop_to_memop_preserves_validity:
  forall b f, 
    preserves_block_validity f ->
    forall m m' bl,
      blockop_to_memop f b bl m = Some m' ->
      mem_valid m bl ->
      mem_valid m' bl.
Proof.
  intros b f PBV m m' bl BTM [[bnd eb] bv].
  split. 
  (* Mem bounded *)
  unfold mem_bounded in *.
  by destruct (Z_lt_dec b bnd); [exists bnd|exists b];
     intros; rewrite <- (blockop_to_memop_inv _ _ _ _ _ _ BTM); try omega; apply eb; try omega. 

  (* block valid *)
  intros b0 x0 EQ0.
  destruct (Z_eq_dec b b0) as [e|n]; clarify.
    unfold blockop_to_memop in BTM.
    destruct (bl b0); clarify; split; [done|].
    destruct (ZTree.get b0 m) as [bc|] _eqn: EQ. 
      specialize (bv _ _ EQ).
      destruct (f (block_contents_o2e (Some bc))) as [] _eqn: fEQ; clarify. 
      specialize (PBV _ _ fEQ); simpl in PBV.
      destruct block_contents_eq_dec; rewrite ?ZTree.grs, ?ZTree.gss in *; clarify. tauto.

    destruct (f (block_contents_o2e None)) as [] _eqn: fEQ; clarify. 
    specialize (PBV _ _ fEQ); simpl in PBV.
    destruct block_contents_eq_dec; rewrite ?ZTree.grs, ?ZTree.gss in *; clarify. 
    pose proof empty_block_valid. tauto.
   
  apply blockop_to_memop_inv with (b' := b0) in BTM; try done. 
  by rewrite <- BTM in EQ0; apply bv.
Qed.

(** Lifting of operations on memory contents to memories with the validity constraint. 
    Most of the work is re-packaging of the proof... *)
Section Contentop_to_memop.

Variable contentop : mem_restr -> mem_contents -> option mem_contents.

Hypothesis op_preserves_validity : 
  forall m m' bl,
    contentop bl m = Some m' -> mem_valid m bl -> mem_valid m' bl.

Definition valid_op (m : mem) := {m' | mem_valid m' (mrestr m) /\ 
                                       contentop (mrestr m) (mcont m) = Some m'} + 
                                 {contentop (mrestr m) (mcont m) = None}.

Definition transsig (m : mem) : valid_op m :=
  (match contentop (mrestr m) (mcont m) as m'
     return contentop (mrestr m) (mcont m) = m' -> valid_op m with
     | None => fun pf => inright _ pf
     | Some nm => fun pf => inleft _ (exist _ nm
          (conj (op_preserves_validity _ _ _ pf (mvalid m)) pf))
   end) (refl_equal _).

Definition trans (m : mem) : option mem :=
  match transsig m with
  | inright _ => None
  | inleft (exist m' pf) =>
      Some (mkmem m' (mrestr m) (proj1 pf))
  end.

Lemma trans_succ:
  forall m m',
    trans m = Some m' -> contentop (mrestr m) (mcont m) = Some (mcont m').
Proof.
  intros m m'. unfold trans. 
  destruct (transsig m) as [[M' [MV' MSP']] | S]; clarify.
  by intro; clarify.   
Qed.

Lemma trans_fail:
  forall m,
    trans m = None -> contentop (mrestr m) (mcont m) = None.
Proof.
  by unfold trans; intros m; destruct (transsig m) as [[M' [MV' MSP']] | S].
Qed.
  
End Contentop_to_memop.

(** The following function transforms a operation on blocks that preserves
    block validity to a function on memories that preserves memory invariants. *)
Definition memop_with_inv (blockop : block_contents -> option block_contents)
                          (bop_preserves_inv : preserves_block_validity blockop)
                          (b : Z) (m : mem) : option mem :=
  trans (blockop_to_memop blockop b)
        (blockop_to_memop_preserves_validity _ _ bop_preserves_inv) 
        m. 

(** Definitions of memory operations. First without pointers. *)

Definition alloc_mem (l h : Z) (k : mobject_kind) 
                     (b : Z)  (m : mem) : option mem :=
  memop_with_inv (alloc_block l h k) (alloc_preserves_block_validity l h k) b m.

Definition free_mem (l : Z) (k : mobject_kind) 
                    (b : Z) (m: mem) : option mem :=
  memop_with_inv (free_block l k) (free_preserves_block_validity l k) b m.

Definition store_mem (chunk: memory_chunk) (ofs: Z) (v: val) 
                     (b : Z) (m: mem) : option mem :=
  memop_with_inv (store_in_block chunk ofs v) 
                 (store_preserves_block_validity chunk ofs v) b m.

Definition clear_block (l h : Z) (b : Z) (m : mem) : mem_contents :=
  let bc := block_contents_o2e (ZTree.get b (mcont m)) in
  let bc' := (mkblock (clear_values l (Zabs_nat (h - l)) (contents bc)) (allocs bc)) in
  if block_contents_eq_dec bc' empty_block then 
    ZTree.remove b (mcont m)
  else 
    ZTree.set b bc' (mcont m).

Program Definition clear_mem (l h : Z) (b : Z) (m : mem) : mem :=
  mkmem (clear_block l h b m) (mrestr m) _.
Next Obligation.
  destruct m as [mc mr [(bnd & BOUNDED) VALID]]; simpl in *.
  unfold clear_block; simpl.
  destruct block_contents_eq_dec; simpl; split.
  - (* mem_bounded *)
    destruct (Z_lt_dec b bnd); [exists bnd|exists (b + 1)]; intros;
      (rewrite ZTree.gro; [eapply BOUNDED|intro; clarify]; omega). 
  - (* block valid *)
    intros b1 x1 EQ1.
    destruct (Z_eq_dec b1 b); clarify.
      2: by eapply VALID; rewrite ZTree.gro in *.
    rewrite ZTree.grs in *; clarify.
  - (* mem_bounded *)
    destruct (Z_lt_dec b bnd); [exists bnd|exists (b + 1)]; intros;
    (rewrite ZTree.gso; [eapply BOUNDED|intro; clarify]; omega). 
  (* block valid *)
  intros b1 x0 EQ0.
  destruct (Z_eq_dec b1 b); clarify.
    2: by eapply VALID; rewrite ZTree.gso in *.
  rewrite ZTree.gss in *; clarify.
  destruct (ZTree.get b mc) as [] _eqn: X; simpl in *.
  2: by elim n; unfold empty_block; f_equal; eapply ZTree.ext; intros; 
        rewrite clear_values_none; rewrite ZTree.gempty.
  exploit VALID; [by eauto|intros (? & (UU & CONT & HBND) & ?)].
  split; [|split]; try done.
  split; simpl.
  (* Unallocated are Undef *)
    by intros i NA; apply clear_values_none, UU. 
  split; [|done]. 
  (* cont_bytes_ok *)
  destruct b0 as [mm al]; simpl.
  edestruct (clear_values_cont_bytes_ok (Zabs_nat (h - l)) l) as [C D]; [eassumption|].  
  split; [by apply C|clear C]. unfold contents, allocs in *.
  intros ? ? ? G; specialize (D _ _ _ G); simpl in *.
  destruct D as ((c & ? & ? & k' & l' & h' & RA & ? & ?) & ?); split; try done.
  exists c; repeat split; try done.
  exists k'; try done; exists l'; exists h'; simpl in *; split; try done.
Qed.

(** [load chunk m b ofs] perform a read in memory state [m], at address
  [b] and offset [ofs].  [None] is returned if the address is invalid
  or the memory access is out of bounds. *)
Definition load (chunk: memory_chunk) (m: mem) (b: Z) (ofs: Z)
                : option val :=
  let b' := block_contents_o2e (ZTree.get b (mcont m)) in
  if in_block chunk (allocs b') ofs then 
     Some (Val.load_result chunk (getN (pred_size_chunk chunk) ofs (contents b')))
  else None.

(** A range is a pointer and a size. *)
Definition arange := (pointer * int)%type.

Lemma range_eq_dec (x y : arange): {x = y} + {x <> y}.
Proof. decide equality; auto using Int.eq_dec, Ptr.eq_dec. Qed.

(** Definition of memory operations using pointers. *)  
Definition alloc_ptr (r : arange) (k : mobject_kind) (m : mem) : option mem :=
  match tt with tt =>
    let '(Ptr b ofs, s) := r in alloc_mem (Int.unsigned ofs)
                                  (Int.unsigned ofs + Int.unsigned s) k b m
  end.

(*Definition alloc_ptr r k m := match tt with tt => alloc_ptr_internal r k m end.*)

Definition free_ptr (p : pointer) (k : mobject_kind) (m : mem) : option mem :=
  let (b, ofs) := p in free_mem (Int.unsigned ofs) k b m.

Definition load_ptr (chunk: memory_chunk) (m: mem) (p: pointer) : option val :=
  let (b, ofs) := p in load chunk m b (Int.unsigned ofs).

Definition store_ptr (chunk: memory_chunk) (m: mem) (p: pointer) (v : val)
  : option mem :=
  let (b, ofs) := p in store_mem chunk (Int.unsigned ofs) v b m.

(** Definition of memory operations using pointers. *)  
Definition clear_range (r : arange) (m : mem) : mem :=
  match tt with tt =>
    let '(Ptr b ofs, s) := r in clear_mem (Int.unsigned ofs)
                                  (Int.unsigned ofs + Int.unsigned s) b m
  end.

(** Properties of pointer versions of memory operations *)

Lemma in_block_true:
  forall chunk al ofs (A: Type) (a1 a2: A),
  valid_access chunk ofs al ->
  (if in_block chunk al ofs then a1 else a2) = a1.
Proof.
  intros; destruct (in_block chunk al ofs); auto; contradiction.
Qed.

Lemma in_block_empty:
  forall chunk ofs (A: Type) (a1 a2: A),
  (if in_block chunk nil ofs then a1 else a2) = a2.
Proof.
  intros. destruct (in_block chunk nil ofs) as [VAL|]; try done. 
  by apply invalid_access_nil in VAL.
Qed.

Lemma load_inv:
  forall {chunk m b ofs v}
   (H: load chunk m b ofs = Some v),
    exists b', ZTree.get b (mcont m) = Some b' /\
      valid_access chunk ofs (allocs b') /\
      v = Val.load_result chunk
           (getN (pred_size_chunk chunk) ofs (contents b')).
Proof.
  intros until v; unfold load.
  destruct (ZTree.get) as [b'|]; try done; simpl.
    by destruct (in_block chunk (allocs b') ofs ); try done; intros; exists b'; inv H.
  by rewrite in_block_empty.
Qed. 

Lemma load_wt:
  forall {chunk m b ofs v}
    (H: load chunk m b ofs = Some v),
  Val.has_type v (type_of_chunk chunk).
Proof.
  intros; destruct (load_inv H) as (bc & _ & _ & LR); clarify.
  by apply Val.load_result_wt.
Qed. 

Lemma memop_with_inv_spec:
  forall {blockop pf b m m'}
    (MWI: memop_with_inv blockop pf b m = Some m'),
       blockop (block_contents_o2e (ZTree.get b (mcont m))) = 
         Some (block_contents_o2e (ZTree.get b (mcont m'))) 
    /\ (forall b', b <> b' -> ZTree.get b' (mcont m) = ZTree.get b' (mcont m'))
    /\ (mrestr m b).
Proof.
  intros; apply trans_succ in MWI; unfold blockop_to_memop in *.
  split.
    destruct (mrestr m b); try done.
    destruct (blockop (block_contents_o2e (ZTree.get b (mcont m)))); try done.
    destruct m'; clarify; simpl.
    by destruct block_contents_eq_dec; clarify; rewrite ?ZTree.grs, ?ZTree.gss; simpl.
  split.
    by intros b' Bneq; apply (blockop_to_memop_inv _ _ _ _ _ _ MWI Bneq).
  by destruct (mrestr m b).
Qed.

Lemma memop_with_inv_spec_fail:
  forall {blockop pf b m}
    (MWI: memop_with_inv blockop pf b m = None),
    blockop (block_contents_o2e (ZTree.get b (mcont m))) = None \/
    mrestr m b = false.
Proof.
  intros; apply trans_fail in MWI; revert MWI.
  unfold blockop_to_memop.
  destruct (mrestr m b); [left|by right].
  by destruct (blockop (block_contents_o2e (ZTree.get b (mcont m)))).
Qed.

Lemma mem_valid_to_hbound:
  forall (m : mem) b, 
    exists hbnd, 
      alloclist_hbound 1 (allocs (block_contents_o2e (ZTree.get b (mcont m)))) = Some hbnd /\ 
      hbnd <= Int.modulus.
Proof.
  intros [m mr [MB BSV]] b; simpl.
  specialize (BSV b). 
  destruct (ZTree.get b m) as [b'|]; [|by exists 1].
  destruct (BSV _ (refl_equal _)) as [? [[? [? [hbnd HBNDMOD]]] ?]].
  by exists hbnd. 
Qed.

(* ========================================================================= *)
(** * Operations on allocation ranges *)

Definition range_non_empty (r : arange) : Prop :=
  0 < Int.unsigned (snd r).

(** [range_inside] *)

Definition range_inside (a b : arange) : Prop :=
  let '((Ptr b1 ofs1, s1), (Ptr b2 ofs2, s2)) := (a, b) in
    b1 = b2 /\ 
    (Int.unsigned ofs1 = 0 /\ Int.unsigned s1 = 0
     /\ Int.unsigned ofs2 + Int.unsigned s2 >= Int.modulus
\/
    Int.unsigned ofs1 >= Int.unsigned ofs2 /\
    Int.unsigned ofs1 + Int.unsigned s1 <= Int.unsigned ofs2 + Int.unsigned s2).

Lemma range_inside_dec:
  forall r' r, {range_inside r' r} + {~ range_inside r' r}.
Proof.
  intros [[b ofs] s] [[b' ofs'] s'].
  unfold range_inside.
  destruct (zeq b b'); try (right; omega).
  destruct (zeq (Int.unsigned ofs) 0);
    [destruct (zeq (Int.unsigned s) 0); 
      [destruct (zeq (Int.unsigned s) 0); 
        [destruct (Z_le_dec Int.modulus (Int.unsigned ofs' + Int.unsigned s')) |]|]|];
    try (right; omega); try (left; omega);
    destruct (Z_le_dec (Int.unsigned ofs') (Int.unsigned ofs));
    destruct (Z_le_dec (Int.unsigned ofs + Int.unsigned s)
      (Int.unsigned ofs' + Int.unsigned s')); 
    try (left; omega); try (right; omega).
Qed.

Lemma range_inside_refl:
  forall r, range_inside r r.
Proof.
  intros [[b ofs] s].
  unfold range_inside. omega.
Qed.

Lemma range_inside_trans:
  forall x y z, range_inside x y -> range_inside y z -> range_inside x z.
Proof.
  intros [[b1 o1] s1] [[b2 o2] s2] [[b3 o3] s3];
  unfold range_inside; pose proof (Int.unsigned_range s1). omega.
Qed.

Lemma range_inside_antisym: 
  forall a b, range_inside a b -> range_inside b a -> a = b.
Proof.
  unfold range_inside.
  intros [[? [a A]] [s S]] [[? [b B]] [t T]] ? ?; simpl in *.
  f_equal; try f_equal; try apply Int.mkint_eq; omega.
Qed.

(** [ranges_disjoint] *)

Definition ranges_disjoint (a b : arange) : Prop := 
  let '((Ptr b1 ofs1, s1), (Ptr b2 ofs2, s2)) := (a, b) in
    b1 <> b2 \/ 
    Int.unsigned ofs1 + Int.unsigned s1 <= Int.unsigned ofs2 \/
    Int.unsigned ofs2 + Int.unsigned s2 <= Int.unsigned ofs1.

Lemma ranges_disjoint_dec:
  forall r r', {ranges_disjoint r r'} + {~ ranges_disjoint r r'}.
Proof.
  intros [[b ofs] s] [[b' ofs'] s'].
  unfold ranges_disjoint.
  destruct (zeq b b') as [-> | N];
    destruct (Z_le_dec (Int.unsigned ofs + Int.unsigned s) 
      (Int.unsigned ofs'));
    destruct (Z_le_dec (Int.unsigned ofs' + Int.unsigned s') 
                       (Int.unsigned ofs));
  try (left; omega); right; omega.
Qed.

Lemma ranges_disjoint_comm:
  forall r r',
    ranges_disjoint r r' -> ranges_disjoint r' r.
Proof.
  intros [[b ofs] n] [[b' ofs'] n']; unfold ranges_disjoint; omega.
Qed.

Lemma disjoint_inside_disjoint_l:
  forall ri r r',
    ranges_disjoint r r' ->
    range_inside ri r ->
    ranges_disjoint ri r'.
Proof.
  intros [[bi ofsi] ni] [[b ofs] n] [[b' ofs'] n'].
  unfold ranges_disjoint, range_inside. 
  pose proof (Int.unsigned_range ofs'); omega.
Qed.

Definition disjoint_inside_disjoint := disjoint_inside_disjoint_l.

Lemma disjoint_inside_disjoint_r:
  forall ri r r',
    ranges_disjoint r r' ->
    range_inside ri r' ->
    ranges_disjoint r ri.
Proof.
  intros [[bi ofsi] ni] [[b ofs] n] [[b' ofs'] n'].
  unfold ranges_disjoint, range_inside. 
  pose proof (Int.unsigned_range ofs); omega.
Qed.

Lemma disjoint_inside_disjoint2:
  forall ri rj r r',
    ranges_disjoint r r' ->
    range_inside ri r ->
    range_inside rj r' ->
    ranges_disjoint ri rj.
Proof.
  eby intros; 
     eapply disjoint_inside_disjoint_l;
     [eapply disjoint_inside_disjoint_r|].
Qed.

(** [ranges_overlap] *)

Definition ranges_overlap (a b : arange) : Prop := 
  ~ ranges_disjoint a b.

Lemma ranges_overlapI: 
  forall b1 ofs1 s1 b2 ofs2 s2,
    b1 = b2 ->
    Int.unsigned ofs1 + Int.unsigned s1 > Int.unsigned ofs2 ->
    Int.unsigned ofs2 + Int.unsigned s2 > Int.unsigned ofs1 ->
    ranges_overlap (Ptr b1 ofs1, s1) (Ptr b2 ofs2, s2).
Proof.
  intros; intro; unfold ranges_disjoint in *; omega.
Qed.

Lemma ranges_overlapD:
  forall {b1 ofs1 s1 b2 ofs2 s2}, 
  ranges_overlap (Ptr b1 ofs1, s1) (Ptr b2 ofs2, s2) ->
    b1 = b2 /\
    Int.unsigned ofs1 + Int.unsigned s1 > Int.unsigned ofs2 /\
    Int.unsigned ofs2 + Int.unsigned s2 > Int.unsigned ofs1.
Proof.
  intros; unfold ranges_overlap, ranges_disjoint in *; omega.
Qed.

Lemma ranges_overlap_refl:
  forall r, range_non_empty r -> ranges_overlap r r.
Proof.
  intros [[b ofs] n] RNE. 
  unfold range_non_empty in RNE; simpl in *. 
  apply ranges_overlapI; omega.
Qed.

Lemma ranges_overlap_comm:
  forall r r',
    ranges_overlap r r' -> ranges_overlap r' r.
Proof.
  eby intros r r' O D; elim O; eapply ranges_disjoint_comm. 
Qed.

Lemma overlap_inside_overlap:
  forall ri r r',
    ranges_overlap ri r ->
    range_inside ri r' ->
    ranges_overlap r' r.
Proof.
  intros r1 r r' OV IN DISJ; elim OV.
  eby eapply disjoint_inside_disjoint.
Qed.

Lemma ranges_not_overlap_disjoint:
  forall r r', ~ ranges_overlap r r' -> ranges_disjoint r r'.
Proof.
  by intros; destruct (ranges_disjoint_dec r r').
Qed.

Lemma non_empty_same_ptr_overlap:
  forall p n n',
    range_non_empty (p, n) ->
    range_non_empty (p, n') ->
    ranges_overlap (p, n) (p, n').
Proof.
  intros [b ofs] n n' H H'; unfold range_non_empty in *; simpl in *.
  apply ranges_overlapI; omega.
Qed.

(** Valid range is within the memory bounds and non-empty. *)
Definition valid_alloc_range (r : arange) :=
  let '((Ptr b ofs), s) := r in
    1 <= Int.unsigned ofs /\
    0 < Int.unsigned s /\
    Int.unsigned ofs + Int.unsigned s <= Int.modulus /\
    (align_size (Int.unsigned s) | Int.unsigned ofs).

Lemma valid_alloc_range_dec (r : arange) :
  {valid_alloc_range r} + {~ valid_alloc_range r}.
Proof.
  destruct r as [[b ofs] s].
  unfold valid_alloc_range.
  destruct (Z_le_dec 1 (Int.unsigned ofs));
    destruct (Z_lt_dec 0 (Int.unsigned s));
      destruct (Z_le_dec (Int.unsigned ofs + Int.unsigned s) Int.modulus);
        destruct (Zdivide_dec (align_size (Int.unsigned s)) (Int.unsigned ofs)
                              (align_size_pos _));
          try (by left; repeat split; try omega);
            by right; intros (?&?&?&?); try omega.
Qed.

Lemma valid_alloc_range_non_empty:
  forall {r},
    valid_alloc_range r -> range_non_empty r.
Proof.
  intros [[b ofs] s] [_ [S _]]. 
  by unfold range_non_empty. 
Qed.

(** Is a range in the allocation lists? *)

Definition range_allocated (r : arange) (k : mobject_kind) (m : mem) : Prop :=
  let '((Ptr b ofs), s) := r in
  let b' := block_contents_o2e (ZTree.get b (mcont m)) in 
  range_allocated_al (Int.unsigned ofs)
                     (Int.unsigned ofs + Int.unsigned s)
                     k
                     b'.(allocs).

Lemma range_allocated_dec:
  forall m k r, {range_allocated r k m} + {~ range_allocated r k m}.
Proof. by intros m k [[b ofs] s]; apply (In_dec mobject_desc_eq_dec). Qed.

(** Is the range allocated? *)

Definition range_in_allocated (r : arange) (m : mem) : Prop :=
  exists r', exists k, 
    range_inside r r' /\ range_allocated r' k m.

Lemma range_in_allocated_dec:
  forall (r : arange) (m : mem),
    {range_in_allocated r m} + {~ range_in_allocated r m}.
Proof.
  unfold range_in_allocated.
  intros [[b ofs] sz] [m mr mv]; simpl.
  destruct (strong_in_dec _ _ (block_mem_dec (Int.unsigned ofs) (Int.unsigned ofs + Int.unsigned sz)) 
    (allocs (block_contents_o2e (ZTree.get b m)))) as [[[l h k] [IN ?]]|OUT]; simpl in *.
    left; eexists (Ptr b (Int.repr l), Int.repr (h - l)); exists k.
    unfold range_allocated, range_allocated_al; simpl mcont.
    pose proof (proj2 mv b) as X; destruct ZTree.get; try done.
    destruct (X _ (refl_equal _)) as [_ [[UU [? [hbnd [BND HBND]]]]]].
    destruct (alloclist_hbound_impl_l_lt_h BND IN) as [LH [LB HB]].
    repeat split; rewrite ?Int.unsigned_repr, ?Zplus_minus; simpl; try done; unfold Int.max_unsigned; omega.
  (* is r = (0, 0)? *)
  destruct (range_inside_dec (Ptr b ofs, sz) (Ptr b Int.zero, Int.zero)) as [M|M]; 
    unfold range_inside in M; simpl in M; change (0 mod Int.modulus) with 0 in M.
  Case "r = (0, 0)".
    assert (Int.unsigned ofs = 0 /\ Int.unsigned sz = 0) as [EQ1 EQ2]
      by (generalize (Int.unsigned_range ofs), (Int.unsigned_range sz); omega).
    destruct (strong_in_dec _ _ block_mem_huge_dec
      (allocs (block_contents_o2e (ZTree.get b m)))) as [[[l h k] [IN ?]]|OUT']; simpl in *.
      left; eexists (Ptr b (Int.repr l), Int.repr (h - l)); exists k.
      unfold range_allocated, range_allocated_al; simpl mcont.
      pose proof (proj2 mv b) as X; destruct ZTree.get; try done.
      destruct (X _ (refl_equal _)) as [_ [[UU [? [hbnd [BND HBND]]]]]].
      destruct (alloclist_hbound_impl_l_lt_h BND IN) as [LH [LB HB]].
      repeat split; rewrite ?Int.unsigned_repr, ?Zplus_minus; simpl; try done; unfold Int.max_unsigned; omega. 
    right; intros [[[b' ofs'] sz'] [k [[<- [RI|RI]] RA]]]; simpl in *.
      eapply OUT'; try eassumption; simpl; omega.
    eapply OUT; try eassumption; simpl; omega.
  Case "r <> (0, 0)".
  right; intros [[[b' ofs'] sz'] [k [[<- RI] RA]]]; simpl in *.
  eapply OUT; try eassumption; simpl; omega.
Qed.

(** Alignments of chunks *)

Definition pointer_chunk_aligned (p : pointer) 
                                 (c : memory_chunk) : Prop :=
  let (b, ofs) := p in (align_chunk c | (Int.unsigned ofs)).

Definition range_of_chunk (p : pointer) (c : memory_chunk) : arange :=
  (p, Int.repr (size_chunk c)).

Lemma pointer_chunk_aligned_dec:
  forall p c, {pointer_chunk_aligned p c} + {~ pointer_chunk_aligned p c}.
Proof.
  intros [b ofs] c. unfold pointer_chunk_aligned.
  by destruct (Zdivide_dec (align_chunk c) (Int.unsigned ofs) (align_chunk_pos c));
     [left|right]. 
Qed.

(* ========================================================================= *)
(** * Operations on allocation range lists *)

(** This section defines the following operations: 

  - [pointer_in_range_list p l]: is the pointer [p] the beginning of an 
    allocation block in [l]?
  - [chunk_inside_range_list p c l]: is the chunk [(p,c)] allocated inside [l]?
  - [range_remove p l]: remove range [(p,...)] from [l].
  - [range_list_disjoint r l]: is range [r] disjoint from all ranges in [l]?
  - [range_lists_disjoint]: are two range lists disjoint?
*)

Fixpoint pointer_in_range_list (p : pointer) (l : list arange) : bool :=
  match l with
    | nil => false
    | (p', _) :: t => 
        if Ptr.eq_dec p p' 
          then true
          else pointer_in_range_list p t
  end.

Lemma pointer_in_range_listD:
  forall {p l},
    pointer_in_range_list p l ->
    exists n, In (p, n) l.
Proof.
  intros p. induction l as [|[p' n'] l IH]. done.
  simpl; destruct (Ptr.eq_dec p p') as [-> | N].
    intro. eexists. left; reflexivity.
  intro H. destruct (IH H). eexists; right; eassumption.
Qed.

Lemma pointer_in_range_listI:
  forall p l n,
    In (p, n) l ->
    pointer_in_range_list p l.
Proof.
  intros p l n. induction l as [|[p' n'] l IH]; clarify.
  simpl; destruct (Ptr.eq_dec p p') as [-> | N]; intros [X|]; clarify. 
Qed.

(** [chunk_inside_range_list] *)

Fixpoint chunk_inside_range_list (p : pointer) (c : memory_chunk)
                                 (l : list arange) : bool :=
  match l with
    | nil => false
    | h :: t => 
        if range_inside_dec (range_of_chunk p c) h
          then true
          else chunk_inside_range_list p c t
  end.

Lemma chunk_inside_range_listD:
  forall {p c l}
    (CIL: chunk_inside_range_list p c l),
    exists r, In r l /\ range_inside (range_of_chunk p c) r.
Proof.
  intros; induction l as [|h l IH]; simpl in *; try done.
  destruct (range_inside_dec) as [RI | NRI].  
    by exists h; split; [apply in_eq|].
  destruct (IH CIL) as [r [IN RI]].
  by exists r; split; [apply in_cons|]. 
Qed.

Lemma chunk_inside_range_listI:
  forall p c l r
    (IN: In r l)
    (INS: range_inside (range_of_chunk p c) r),
    chunk_inside_range_list p c l.
Proof.
  intros p c l; induction l as [|h l IH]; simpl in *; try done.
  intros r [->|IN] INS; destruct (range_inside_dec); try done.
  eby eapply IH.
Qed.

(** [range_not_in] *)

Definition range_not_in (r : arange) (l : list arange) :=
  forall r', In r' l -> ranges_disjoint r r'.

Lemma range_in_dec:
  forall r l, {r' | In r' l /\ ranges_overlap r r'} + {range_not_in r l}.
Proof.
  by intros r l; apply (strong_in_dec_neg _ (ranges_disjoint_dec r) l).
Qed.

(** [range_remove] *)

Fixpoint range_remove (p : pointer) (rs : list arange) : list arange :=
  match rs with
    | nil => nil
    | (p', s')::rest => 
        if Ptr.eq_dec p' p 
          then range_remove p rest 
          else (p', s')::(range_remove p rest)
  end.

Lemma in_range_removeD:
  forall {p p' n' l} (IN: In (p', n') (range_remove p l)),
    p' <> p /\ In (p', n') l.
Proof.
  induction l as [|[ph nh] l IH]; simpl; try done.
  destruct (Ptr.eq_dec ph p) as [-> | N]; simpl.
    tauto.
  intros [E | IN]; clarify; tauto. 
Qed.

Lemma in_range_removeI:
  forall p p' n' l,
    In (p', n') l -> p' <> p -> In (p', n') (range_remove p l).
Proof.
  induction l as [|[ph nh] l IH]; simpl; try done.
  intros [E | IN]; clarify; 
  destruct (Ptr.eq_dec); clarify; simpl; tauto.
Qed.

Lemma in_range_remove:
  forall p p' n' l,
    In (p', n') (range_remove p l) -> In (p', n') l.
Proof.
  intros p p' n' l.
  induction l as [|[ph nh] l IH]; simpl; try done.
  destruct (Ptr.eq_dec ph p) as [-> | N].
     tauto.
  intros [E | IN]; [by left |by right; apply IH].
Qed.

Lemma in_range_remove_back:
  forall p p' n' l,
    In (p', n') l -> p = p' \/ In (p', n') (range_remove p l).
Proof.
  induction l as [|[ph nh] l IH]; simpl; try done.
  destruct (Ptr.eq_dec ph p) as [-> | N].
    intros [E | IN]. inv E; by left.
    tauto.
  intros [E | IN]. inv E. right; by apply in_eq.
  destruct (IH IN). by left.
  by right; apply in_cons.
Qed.

(** [range_lists_disjoint] *)

Fixpoint range_list_disjoint (l : list arange) :=
  match l with
    | nil => True
    | r :: t => range_list_disjoint t /\ range_not_in r t
  end.

Definition range_lists_disjoint (l : list arange) (l' : list arange) :=
  forall e, In e l -> range_not_in e l'.

Lemma range_lists_disjoint_comm:
  forall x y,
    range_lists_disjoint x y ->
    range_lists_disjoint y x.
Proof.
  intros x y RLD r IN r' IN'.
  by apply ranges_disjoint_comm, RLD.
Qed.

Lemma range_lists_disjoint_tail1:
  forall h t l,
    range_lists_disjoint (h :: t) l ->
    range_lists_disjoint t l.
Proof.
  intros h t l RLD r IN r' IN'.
  eapply RLD; try done. by apply in_cons.
Qed.

Lemma range_lists_disjoint_tail2:
  forall h t l,
    range_lists_disjoint l (h :: t) ->
    range_lists_disjoint l t.
Proof.
  intros h t l RLD r IN r' IN'.
  eapply RLD; try done. by apply in_cons.
Qed.

Lemma range_list_disjoint_app:
  forall l1 l2,
    range_list_disjoint (l1 ++ l2) <->
    range_list_disjoint l1 /\
    range_list_disjoint l2 /\
    range_lists_disjoint l1 l2.
Proof.
  intros l1 l2; induction l1 as [|h t IH].
    repeat (split; try done); tauto.
  rewrite <- app_comm_cons. simpl.
  split.
    intros (RLD & RNI).
    apply IH in RLD. destruct RLD as (RLDt & RLDl2 & RLSD).
    repeat split; try done.  
      by intros r IN; apply RNI, in_or_app; left.
    intros r1 IN1 r2 IN2.
    destruct IN1 as [-> | IN1].
      by apply RNI, in_or_app; right.
    by apply RLSD.
  intros ((RLDt & RNI) & RLDl2 & RLSD).
  split. 
    apply IH.
    repeat split; try done.
    by intros r1 IN1 r2 IN2; apply RLSD; [apply in_cons|]. 
  intros r IN.
  apply in_app_or in IN. destruct IN as [IN | IN].
    by apply RNI.
  by apply RLSD; vauto. 
Qed.

Require Import Permutation.

Lemma range_list_disjoint_perm:
  forall l l',
    Permutation l l' ->
    range_list_disjoint l ->
    range_list_disjoint l'.
Proof.
  induction l as [|h t IH]; intros l' P RLD.
    by rewrite Permutation_nil.
  pose proof (Permutation_in _ P (in_eq _ _)) as IN.
  destruct (In_split _ _ IN) as [l1 [l2 ->]].
  simpl in RLD; destruct RLD as [RLD RNI].
  apply Permutation_cons_app_inv in P. 
  specialize (IH _ P RLD).
  destruct (proj1 (range_list_disjoint_app _ _) IH) as (RLDl1 & RLD2 & RLSD).
  apply (proj2 (range_list_disjoint_app _ _)).
  split. done.
  split. split. done.
    intros r' IN'. apply RNI. apply Permutation_sym in P.
    apply (Permutation_in _ P). apply in_or_app. by right.
  intros r1 IN1 r2 IN2.
  simpl in IN2. destruct IN2 as [-> | IN2].
    apply ranges_disjoint_comm, RNI. apply Permutation_sym in P.
    apply (Permutation_in _ P). apply in_or_app. by left.
  by apply RLSD.
Qed.

Lemma range_list_disjoint_remove:
  forall p l,
    range_list_disjoint l ->
    range_list_disjoint (range_remove p l).
Proof.
  induction l as [|[ph nh]  l IH]; simpl; try done.
  intros [DISJ RNI].
  destruct (Ptr.eq_dec ph p) as [-> | N]. tauto. 
  simpl. split. by apply IH. 
  intros [] IN'. eby eapply RNI, in_range_remove.
Qed.  

(*
Lemma range_list_disjoint_remove_not_in:
  forall p l,
    (forall r, In r l -> range_non_empty r) ->
    range_list_disjoint l ->
    forall n, ~ In (p, n) (range_remove p l).
Proof.
  induction l as [|[ph nh] l IH]; simpl.
    by intros.
  intros RNE [RD RNI] n IN.
  destruct (Ptr.eq_dec ph p) as [-> | N].
    assert (PNE: range_non_empty (p, n)). eby apply RNE; right; eapply in_range_remove.
    assert (PHNE: range_non_empty (p, nh)) by (apply RNE; left; done).
    apply RNI in IN.
    by eapply non_empty_same_ptr_overlap in IN. 
  simpl in IN. destruct IN as [E | IN]. by inv E. 
  by eapply IH; try edone; intros; apply RNE; right.
Qed.
*)

Definition range_list_of_mem (m: mem) : list arange :=
  ZTree.fold (fun r b c => List.fold_left 
                 (fun r a => (Ptr b (Int.repr (mobj_low a)), 
                              (Int.repr (mobj_high a - mobj_low a)))::r) 
                 (allocs c) r) (mcont m) nil.

Lemma range_list_of_mem_alloc:
  forall r m, In r (range_list_of_mem m) <-> (exists k, range_allocated r k m).
Proof.
  unfold range_allocated, range_list_of_mem.
  intros [[b ofs] sz] [mc mr mv]; simpl; rewrite ZTree.fold_spec.

  replace 
        (fun (a : list (pointer * int)) (p : ZTree.elt * block_contents) =>
         fold_left
           (fun (r : list (pointer * int)) (a0 : mobject_desc) =>
            (Ptr (fst p) (Int.repr (mobj_low a0)),
            Int.repr (mobj_high a0 - mobj_low a0)) :: r) 
           (allocs (snd p)) a)
   with
        (fun a p =>
          map
           (fun a0 =>
            (Ptr (fst p) (Int.repr (mobj_low a0)),
            Int.repr (mobj_high a0 - mobj_low a0))) 
           (rev (allocs (snd p))) ++ a).
  2: by do 2 (apply extensionality; intro); symmetry; apply fold_left_cons.
  rewrite fold_left_app_red, <- app_nil_end.
  eapply iff_trans; [by apply in_flatten|].
  rewrite map_rev. 
  split.
    intros (y & IN1 & IN2).
    apply <- In_rev in IN2.
    apply -> in_map_iff in IN2.
    destruct IN2 as ([? ?] & ? & IN2); clarify.
    rewrite map_rev in *.
    apply <- In_rev in IN1.
    apply -> in_map_iff in IN1.
    destruct IN1 as ([? ? ?] & ? & IN1); clarify.
    pose proof (ZTree.elements_complete _ _ _ IN2) as EQ. 
    pose proof (proj1 (proj2 (proj2 mv _ _ EQ))) as (_ & _ & hbnd & HBND & ?). 
    pose proof (alloclist_hbound_impl_l_lt_h HBND IN1).
    by rewrite !Int.unsigned_repr, Zplus_minus, EQ; [eby eexists| |]; 
       unfold Int.max_unsigned; omega.
  intros (k & IN).
  destruct (ZTree.get b mc) as [] _eqn: EQ; simpl in *; try done.
  pose proof (ZTree.elements_correct _ _ EQ) as H.
  eexists; split; [|by apply -> In_rev; apply (in_map _ _ _ H)].  
  simpl.
  rewrite map_rev; apply -> In_rev.
  apply <- in_map_iff.
  by eexists; split; try edone; simpl; rewrite Zminus_plus, !Int.repr_unsigned.
Qed.

(*============================================================================*)
(** * Properties about alloc  *)

Definition restricted_pointer (p : pointer) (m : mem) : bool :=
  let '(Ptr b ofs) := p in mrestr m b.

Lemma Zplus_minus2:
  forall a b, a + b - a = b.
Proof. intros; omega. Qed.

Lemma alloc_ptr_inv: 
  forall {b ofs k i m m'}
    (AP: alloc_ptr (Ptr b ofs, i) k m = Some m'),
    (let bc := block_contents_o2e (ZTree.get b (mcont m)) in 
     let bc' := block_contents_o2e (ZTree.get b (mcont m')) in
      alloc_in_alloclist (Int.unsigned ofs)
                         (Int.unsigned ofs + Int.unsigned i) 
                         k
                        (allocs bc) = Some (allocs bc') /\
      contents bc' = contents bc) /\
    (forall b' : Z, b <> b' ->  ZTree.get b' (mcont m) = ZTree.get b' (mcont m')) /\
    mrestr m b /\
    1 <= Int.unsigned ofs /\
    0 < Int.unsigned i /\
    Int.unsigned ofs + Int.unsigned i <= Int.modulus /\
    (align_size (Int.unsigned i) | Int.unsigned ofs).
Proof.
  intros.
  destruct(memop_with_inv_spec AP) as [AB [OTH MR]]. 
  by destruct (alloc_block_inv _ _ _ _ _ AB) as (AL & ? & ? & ? & ? & ALG);
    repeat split; try assumption; try omega; rewrite Zplus_minus2 in ALG.
Qed.

Lemma range_allocated_empty:
  forall mr r k,
    ~ range_allocated r k (empty mr).
Proof.
  intros mr [[b ofs] n] k.
  unfold range_allocated.
  simpl. by rewrite ZTree.gempty.
Qed.

Lemma alloc_cond_spec:
  forall r k m,
    match alloc_ptr r k m with
      | Some m' => range_allocated r k m' /\
                   valid_alloc_range r /\
                   restricted_pointer (fst r) m /\
                   forall r' k', ranges_overlap r r' -> 
                     ~ range_allocated r' k' m
      | None => ~ valid_alloc_range r \/
                ~ restricted_pointer (fst r) m \/
                exists r', exists k', ranges_overlap r r' /\
                                      range_allocated r' k' m
    end.
Proof.
  intros r k m.
  destruct r as [[b ofs] s]. 
  pose proof (mem_valid_to_hbound m b) as MB.
  destruct (alloc_ptr (Ptr b ofs, s) k m) as [m'|] _eqn : AP.
    destruct (alloc_ptr_inv AP) as [[AL CON] [_ [MR C]]].
    split.
      by apply (alloc_allocates AL).
    split.
      done.
    split; [done|]. 
    intros [[b' ofs'] s'] k' OVER.
    destruct (ranges_overlapD OVER) as [Beq [Llth1 Llth2]]; clarify. 
    unfold range_allocated.
    destruct (ZTree.get b' (mcont m)); try done.
    destruct MB as [hbnd [HBND _]].
    apply (alloc_allocated_was_free HBND AL); omega.
  simpl in AP. 
  destruct (memop_with_inv_spec_fail AP) as [AB | R].
    unfold alloc_block in AB.
    destruct (Z_le_dec 1 (Int.unsigned ofs));
      destruct (aligned_rng_dec (Int.unsigned ofs) 
                                (Int.unsigned ofs + Int.unsigned s)) 
          as [[]|[|]];
        destruct (Z_le_dec (Int.unsigned ofs + Int.unsigned s) Int.modulus);
          try (left; unfold valid_alloc_range; omega).
    destruct (alloc_in_alloclist (Int.unsigned ofs)
              (Int.unsigned ofs + Int.unsigned s) k 
              (allocs (block_contents_o2e (ZTree.get b (mcont m))))) 
      as [] _eqn:E; try done.
    destruct (alloc_fail_overlap E) as [l' [h' [k' [RA OVER]]]].
    right; right. exists (Ptr b (Int.repr l'), Int.repr (h' - l')). exists k'.
    unfold ranges_overlap, range_allocated.
    destruct (ZTree.get b (mcont m)); clarify.
    destruct MB as [hbnd [HBND HBNDMOD]].
    pose proof (alloclist_hbound_impl_l_lt_h HBND RA).
    split.
      apply ranges_overlapI; rewrite ?Int.unsigned_repr; try unfold Int.max_unsigned; try omega.
    rewrite !Int.unsigned_repr; try unfold Int.max_unsigned; try omega.
    replace (l' + (h' - l')) with h'; [done|omega].
  by left; intros (_&_&_&?); elim H; rewrite Zplus_minus2.
  by right; left; simpl; rewrite R. 
Qed.

Lemma alloc_someD: 
  forall {r k m m'} (H: alloc_ptr r k m = Some m'),
    range_allocated r k m' /\
    valid_alloc_range r /\
    restricted_pointer (fst r) m /\
    forall r' k', ranges_overlap r r' -> 
      ~ range_allocated r' k' m.
Proof.
  by intros; generalize (alloc_cond_spec r k m); rewrite H.
Qed.

Lemma alloc_allocatedD: 
  forall {r k m m' r' k'} 
    (H: alloc_ptr r k m = Some m')
    (RA: range_allocated r' k' m),
    ranges_disjoint r r'.
Proof.
  intros. destruct (alloc_someD H) as (AL & _ & _ & X). 
  destruct (ranges_disjoint_dec r r'); try done.
  eby ecase X.
Qed.

Lemma alloc_noneD: 
  forall {r k m} (H: alloc_ptr r k m = None),
    ~ valid_alloc_range r \/
    ~ restricted_pointer (fst r) m \/
    exists r', exists k', ranges_overlap r r' /\
      range_allocated r' k' m.
Proof.
  by intros; generalize (alloc_cond_spec r k m); rewrite H.
Qed.

Lemma ranges_are_disjoint:
  forall {m r1 k1 r2 k2} 
    (RA1: range_allocated r1 k1 m)
    (RA2: range_allocated r2 k2 m),
    r1 = r2 /\ k1 = k2 \/ ranges_disjoint r1 r2.
Proof.
  intros; destruct r1 as [[b1 o1] s1]; destruct r2 as [[b2 o2] s2].
  destruct (Z_eq_dec b1 b2) as [Eq|Neq].
  rewrite Eq in *. simpl in *. 
  pose proof (mem_valid_to_hbound m b2) as MV. 
  destruct (ZTree.get b2 (mcont m)) as [] _eqn : EQs; try done.
  destruct MV as [hbnd [HBND _]].
  destruct (alloclist_no_overlap HBND RA1 RA2) 
    as [RA1L | [RA1H | [Leq [Heq Keq]]]].
  by right; right; left.
  by right; right; right.
  left; split; [|done]; f_equal; f_equal; apply Int.unsigned_eq; omega.
  by right; left.
Qed.

Lemma allocated_range_valid:
  forall r k m,
    range_allocated r k m ->
    valid_alloc_range r.
Proof.
  intros [[b ofs] s] k m RA. pose proof (mem_valid_to_hbound m b) as MB.
  simpl in RA. destruct (ZTree.get b (mcont m)); try done.
  destruct MB as [hbnd [HBND HBNDMOD]].
  destruct (alloclist_hbound_impl_l_lt_h HBND RA) as (?&?&?&ALG).
  rewrite Zplus_minus2 in ALG.
  by repeat split; try omega.
Qed.

Remark alloc_ranges_same:
  forall {p n1 n2 k1 k2 m},
    range_allocated (p, n1) k1 m ->
    range_allocated (p, n2) k2 m ->
    n1 = n2 /\ k1 = k2.
Proof.
  intros [b ofs] n1 n2 k1 k2 m RA1 RA2.
  destruct (ranges_are_disjoint RA1 RA2) as
    [[Req Keq] | [DISJ | [DISJ | DISJ]]]. 
        by inv Req.
      done.
    apply allocated_range_valid in RA1. unfold valid_alloc_range in RA1.
    omegaContradiction.
  apply allocated_range_valid in RA2. unfold valid_alloc_range in RA2.
  omegaContradiction.
Qed.

Lemma alloc_preserves_allocated:
  forall {r k m m'},
    alloc_ptr r k m = Some m' ->
    forall r' k',
      range_allocated r' k' m -> range_allocated r' k' m'.
Proof.
  intros [[b ofs] s] k m m' AP [[b' ofs'] s'] k' RA.
  destruct (alloc_ptr_inv AP) as [[AL CON] [OB _]].
  simpl in *.
  destruct (Z_eq_dec b b') as [Eq|Neq]; clarify.
    eby eapply alloc_preserves_allocated_al.
  by rewrite <- (OB b').
Qed.

Lemma alloc_preserves_allocated_back:
  forall {r k m m'},
    alloc_ptr r k m = Some m' ->
    forall r' k',
      range_allocated r' k' m' -> 
      r' = r /\ k' = k \/ range_allocated r' k' m.
Proof.
  intros [[b ofs] s] k m m' AP [[b' ofs'] s'] k' RA.
  destruct (alloc_ptr_inv AP) as [[AL CON] [OB _]].
  simpl in *.
  destruct (Z_eq_dec b b') as [Eq|Neq]; clarify. 
  destruct (alloc_preserves_allocated_bw AL RA).
    by right.
    left. split. repeat f_equal; try (apply Int.unsigned_eq; omega). tauto.
  by right; rewrite (OB b').
Qed.

Lemma alloc_preserves_allocated_iff:
  forall {r k m m'},
    alloc_ptr r k m = Some m' ->
    forall r' k',
      range_allocated r' k' m' <-> 
      r' = r /\ k' = k \/ range_allocated r' k' m.
Proof.
  intros r k m m' H. 
  split; [by apply alloc_preserves_allocated_back|].
  intros [[? ?]|]; subst; [|eby eapply alloc_preserves_allocated].
  by apply (proj1 (alloc_someD H)).
Qed.

(*============================================================================*)
(** * Properties about free  *)

Lemma free_cond_spec: 
  forall p k m,
    match free_ptr p k m with
      | Some m' => exists n, range_allocated (p, n) k m
      | None => forall n, ~ range_allocated (p, n) k m
    end.
Proof.
  intros [b ofs] k m.
  destruct (free_ptr (Ptr b ofs) k m) as [m'|] _eqn: FE.
    destruct (memop_with_inv_spec FE) as [FB [OTH RA]].
    unfold free_block in FB. 
    destruct (free_in_alloclist (Int.unsigned ofs) k (allocs (block_contents_o2e (ZTree.get b (mcont m)))))
      as [[na h]|] _eqn:FBE; try done.
    apply free_must_have_been_allocated in FBE.
    exists (Int.repr(h - Int.unsigned ofs)).
    unfold range_allocated.
    rewrite Int.unsigned_repr. 
    replace (Int.unsigned ofs + (h - Int.unsigned ofs)) with h; [done|omega].
    pose proof (mem_valid_to_hbound m b) as MB.
    destruct MB as [hbnd [HBND HBNDMOD]].
    pose proof (alloclist_hbound_impl_l_lt_h HBND FBE).
    by unfold Int.max_unsigned; omega.
  destruct (memop_with_inv_spec_fail FE) as [AB | R].
    intros n RA. simpl in RA. 
    unfold free_block in AB.
    destruct (free_in_alloclist (Int.unsigned ofs) k (allocs (block_contents_o2e (ZTree.get b (mcont m)))))
      as [[na h]|] _eqn:FBE; try done.
    pose proof (mem_valid_to_hbound m b) as [hbnd [HBND HBNDMOD]].
    eby eapply free_fail.
  intros n; clear FE; unfold range_allocated, block_contents_o2e. 
  destruct m as [mc mr [? mv]]; simpl in *.
  specialize (mv b); rewrite R in mv.
  destruct (ZTree.get b mc).
    by pose proof (proj1 (mv _ (refl_equal _))).
  by simpl; intro H; inversion H.
Qed.

Lemma free_someD: 
  forall {p k m m'}, free_ptr p k m = Some m' ->
    exists n, range_allocated (p, n) k m.
Proof.
  by intros p k m m' H; generalize (free_cond_spec p k m); rewrite H.
Qed.

Lemma free_noneD: 
  forall {p k m}, free_ptr p k m = None -> 
    forall n, ~ range_allocated (p, n) k m.
Proof.
  by intros p k m H; generalize (free_cond_spec p k m); rewrite H.
Qed.

Lemma free_preserves_allocated:
  forall {p k m m'},
    free_ptr p k m = Some m' ->
    forall r' k', 
      range_allocated r' k' m ->
      range_allocated r' k' m' \/ fst r' = p /\ k' = k.
Proof.
  intros [b ofs] k m m' FP [[b' ofs'] s'] k' RA.
  destruct (memop_with_inv_spec FP) as [FB [OTH _]].
  destruct (Z_eq_dec b b') as [<-|Neq]. 
    simpl. simpl in RA.
    unfold free_block in FB.
    destruct (free_in_alloclist (Int.unsigned ofs) k (allocs (block_contents_o2e (ZTree.get b (mcont m))))) as 
      [[nal h]|] _eqn : FIA.
      inv FB. simpl.
      destruct (free_in_alloclist_fw _ _ _ _ _ FIA _ _ _ RA) as [? | [E [-> ->]]].
        by left.
      right. split. f_equal. by apply Int.unsigned_eq. done.
    done.
  simpl. by left; rewrite <- OTH. 
Qed.


Lemma free_preserves_allocated_back:
  forall {p k m m'},
    free_ptr p k m = Some m' ->
    forall r' k',
      range_allocated r' k' m' -> range_allocated r' k' m.
Proof.
  intros [b ofs] k m m' FP [[b' ofs'] s'] k' RA.
  destruct (memop_with_inv_spec FP) as [FB [OTH MR]].
  destruct (Z_eq_dec b b') as [<-|Neq].
    simpl. simpl in RA.
    unfold free_block in FB.
    destruct (block_contents_o2e (ZTree.get b (mcont m))) as [bc ba]; simpl in *.
    destruct (free_in_alloclist (Int.unsigned ofs) k ba) as [[nal h]|] _eqn : FIA; clarify.
    destruct (block_contents_o2e (ZTree.get b (mcont m'))) as [bc' ba']; clarify.
    by apply (free_in_alloclist_bw _ _ _ _ _ FIA _ _ _ RA).
  by simpl; rewrite OTH. 
Qed.

Lemma free_not_allocated:
  forall {p k m m'},
    free_ptr p k m = Some m' ->
    forall n k',
      ~ range_allocated (p, n) k' m'.
Proof.
  intros [b ofs] k m m' FP s' k' RA.

  destruct (memop_with_inv_spec FP) as [FB OTH].
  unfold free_block in FB. 
  destruct
    (free_in_alloclist (Int.unsigned ofs) k
           (allocs (block_contents_o2e (ZTree.get b (mcont m))))) as 
    [[nal h]|] _eqn : FIA; [|done].
  destruct (block_contents_o2e (ZTree.get b (mcont m'))) as [bc' ba'] _eqn: EQ; clarify.
  destruct (allocated_range_valid _ _ _ RA). 
  simpl in RA. 
  pose proof (proj2 (mvalid m) b) as BVO.
  destruct (ZTree.get b (mcont m)); simpl in *; clarify.
  destruct (BVO _ (refl_equal _)) as [_ [[_ [? [hbnd [AHBND HBNDM]]]]]].
  rewrite EQ in *.
  destruct (free_frees _ _ _ _ _ _ _ AHBND FIA _ _ _ RA). omega.
  pose proof (free_hight_gt_low _ _ _ _ _ _ _ AHBND FIA).
  omega.
Qed.

(*============================================================================*)
(** * Properties about store  *)

Lemma store_preserves_allocated_ranges:
  forall {m c p v m'},
    store_ptr c m p v = Some m' ->
    forall r k, range_allocated r k m <-> range_allocated r k m'.
Proof.
  intros m c p v m' SP r k.
  destruct p as [b ofs]. simpl in SP.
  unfold store_mem in SP.
  destruct(memop_with_inv_spec SP) as [SB [OTH MR]].
  apply store_in_block_inv in SB. apply proj2 in SB.
  destruct r as [[b' ofs'] s']. simpl.
  destruct (Z_eq_dec b b') as [Beq | Bneq]. rewrite Beq in *.
    rewrite SB; tauto.
    rewrite OTH; tauto.
Qed.

Definition valid_block_access_lifted
  (p : pointer) (c : memory_chunk) (m : mem) : Prop :=
  let (b, ofs) := p in
  let bc := block_contents_o2e (ZTree.get b (mcont m)) in
  valid_access c (Int.unsigned ofs) (allocs bc).

Definition chunk_allocated_and_aligned 
  (p : pointer) (c : memory_chunk) (m : mem) : Prop :=
  range_in_allocated (range_of_chunk p c) m /\
  pointer_chunk_aligned p c.

Lemma store_preserves_chunk_allocation:
  forall {m c p v m'},
    store_ptr c m p v = Some m' ->
    forall p c, chunk_allocated_and_aligned p c m <-> 
                chunk_allocated_and_aligned p c m'.
Proof.
  intros m c p v m' STORE p' c'.
  split.
    intros [[r [k [RI RA]]] AL].
    split; [|done]. exists r; exists k; split; try done. 
    by apply (proj1 (store_preserves_allocated_ranges STORE _ _)).
  intros [[r [k [RI RA]]] AL].
  split; [|done]. exists r; exists k; split; try done. 
  by apply (proj2 (store_preserves_allocated_ranges STORE _ _)).
Qed.

Lemma size_chunk_repr:
  forall c, Int.unsigned (Int.repr (size_chunk c)) = size_chunk c.
Proof.
  by destruct c; rewrite Int.unsigned_repr.
Qed.

Lemma vba_impl_chunk_allocated:
  forall {p c m},
    valid_block_access_lifted p c m -> 
    chunk_allocated_and_aligned p c m.
Proof.
  intros [b ofs] c [mc mr [MB BV]] VBA.
  pose proof (BV b) as BVB. 
  unfold valid_block_access_lifted, chunk_allocated_and_aligned in *; simpl in *.
  destruct (ZTree.get b mc) as [bc|] _eqn : Emc;
     [|by apply invalid_access_nil in VBA].
  destruct VBA as [k [l [h [RA [LOW HIGH]]]] ALG].
  unfold range_in_allocated, range_of_chunk, range_allocated, range_inside.
  split; [|done].
  exists (Ptr b (Int.repr l), Int.repr (h - l)). exists k. 
  destruct (BVB _ (refl_equal _)) as [_ [[UU [? [hbnd [BND HBND]]]]]].
  destruct (alloclist_hbound_impl_l_lt_h BND RA) as [LH [LB HB]].
  rewrite size_chunk_repr.
  rewrite !Int.unsigned_repr; try unfold Int.max_unsigned; try omega.
  replace (l + (h - l)) with h; [|omega].
  simpl. rewrite Emc.
  repeat split; try done; omega.
Qed.

Lemma chunk_allocated_impl_vba:
  forall {p c m},
    chunk_allocated_and_aligned p c m -> valid_block_access_lifted p c m.
Proof.
  intros [b ofs] c [mc mr [MB BV]].
  pose proof (BV b) as BVB. 
  unfold valid_block_access_lifted, chunk_allocated_and_aligned in *;
    simpl in *.
  intros [[[[b' ofs'] n'] [k [[<- [[_ [SZERO _]]|[L H]]] RA]]] ALG].
    by destruct c.
  simpl in RA. destruct (ZTree.get b mc) as [bc|] _eqn : Emc; try done.
  econstructor; try done.
  exists (Int.unsigned ofs'); exists (Int.unsigned ofs' + Int.unsigned n').
  repeat split; try edone. omega. by rewrite size_chunk_repr in H. 
Qed.

Lemma store_chunk_allocated_spec:
  forall c m p v,
    match store_ptr c m p v with
      | Some v => chunk_allocated_and_aligned p c m
      | None => ~ chunk_allocated_and_aligned p c m
    end.
Proof.
  intros c m p v.
  destruct (store_ptr c m p v) as [nm|] _eqn : EQnm;
    destruct p as [b ofs]; destruct m as [mc mr mv]; simpl in *.
    apply vba_impl_chunk_allocated. unfold valid_block_access_lifted. simpl.

    destruct (memop_with_inv_spec EQnm) as [BOP [OTH MR]]; simpl in *.
    unfold store_in_block in BOP.
    destruct (ZTree.get b mc) as [b0|] _eqn: EQ; try done; simpl in *.
      by destruct (in_block c (allocs b0) (Int.unsigned ofs)).
    by rewrite in_block_empty in *.
  intro CA; apply chunk_allocated_impl_vba in CA; revert CA.
  destruct (memop_with_inv_spec_fail EQnm) as [BOP | PS]; simpl in *; 
    destruct (ZTree.get b mc) as [b0|] _eqn: EQ; try (by apply invalid_access_nil); simpl in *.
    by unfold store_in_block in BOP; destruct (in_block c (allocs b0) (Int.unsigned ofs)). 
  by rewrite (proj1 (proj2 mv b b0 EQ)) in PS.
Qed.

Lemma store_chunk_allocated_someD:
  forall {c m p v m'}, store_ptr c m p v = Some m' -> chunk_allocated_and_aligned p c m.
Proof.
  by intros c m p v m' H; generalize (store_chunk_allocated_spec c m p v); rewrite H.
Qed.

Lemma store_chunk_allocated_noneD:
  forall {c m p v}, store_ptr c m p v = None -> ~ chunk_allocated_and_aligned p c m.
Proof.
  by intros c m p  v H; generalize (store_chunk_allocated_spec c m p v); rewrite H.
Qed.

(*============================================================================*)
(** * Properties about load  *)

Lemma load_chunk_allocated_spec:
  forall c m p,
    match load_ptr c m p with
      | Some v => chunk_allocated_and_aligned p c m
      | None => ~ chunk_allocated_and_aligned p c m
    end.
Proof.
  intros c m p. 
  destruct p as [b ofs]; destruct m as [mc mv]; simpl.
  unfold load; simpl. destruct (ZTree.get b mc) as [bc|] _eqn : E; simpl; [|rewrite in_block_empty];
  [destruct (in_block c (allocs bc) (Int.unsigned ofs)) as [VBA | NVBA];
   [apply vba_impl_chunk_allocated; simpl; rewrite E; done|]|];
     intro CA; apply chunk_allocated_impl_vba in CA; simpl in CA; 
       rewrite E in CA; [done|eby eapply invalid_access_nil].
Qed.

Lemma load_empty_mem:
  forall c mr p,
    load_ptr c (empty mr) p = None.
Proof.
  intros.
  pose proof (load_chunk_allocated_spec c (empty mr) p) as LS.
  destruct load_ptr; [|done].
  destruct LS as [[r [k [_ RA]]] _].
  destruct (range_allocated_empty _ _ _ RA).
Qed.

Lemma load_chunk_allocated_someD:
  forall {c m p v}, load_ptr c m p = Some v -> chunk_allocated_and_aligned p c m.
Proof.
  by intros c m p v H; generalize (load_chunk_allocated_spec c m p); rewrite H.
Qed.

Lemma load_chunk_allocated_noneD:
  forall {c m p}, load_ptr c m p = None -> ~ chunk_allocated_and_aligned p c m.
Proof.
  by intros c m p H; generalize (load_chunk_allocated_spec c m p); rewrite H.
Qed.

Lemma load_store_similar:
  forall {c c' m p v m'},
    store_ptr c m p v = Some m' ->
    size_chunk c = size_chunk c' ->
    load_ptr c' m' p = Some (if compatible_chunks c c' then Val.load_result c' v else Vundef).
Proof.
  intros c c' m p v m' STORE EQcs.
  destruct p as [b ofs]. simpl.
  destruct (memop_with_inv_spec STORE) 
    as [SB [OTHER MR]]; try done.
  unfold store_in_block in SB.
  
  destruct (ZTree.get b (mcont m)) as [bc ba|]; simpl in *; clarify.
    destruct (in_block c (allocs bc) (Int.unsigned ofs)) as [VBA | NVBA]; clarify. 
    unfold load.
    destruct (ZTree.get b (mcont m')) as [bc' ba'|]; simpl in *; clarify.
      simpl in_block.
      destruct (in_block c' (allocs bc) (Int.unsigned ofs)) as [VBA' | NVBA'].
        f_equal. simpl. 
        replace (pred_size_chunk c) with (pred_size_chunk c').
        destruct (stored_value c v) as [] _eqn: STeq.
          rewrite getN_setN_same, (load_result_stored_value_some _ _ _ _ STeq); try done. 
            by destruct c; destruct c'; destruct v; simpl in *; clarify. 
          by destruct c; destruct c'.
        rewrite getN_clear_value_same, load_result_undef.
          by destruct c; destruct c'; destruct v; clarify; simpl in *.
        by destruct c; destruct c'.
      elim NVBA'. 
      by apply valid_access_same_size with (c:=c). 
    byContradiction.
    injection H0; intros ALLOCS_EMP _.
    destruct VBA as [? [? [? [ALL _]]] _].
    rewrite ALLOCS_EMP in ALL.
    by inversion ALL.
  by rewrite in_block_empty in *.
Qed.  

Lemma cont_bytes_ok_mem:
   forall b m,
   cont_bytes_ok (block_contents_o2e (ZTree.get b (mcont m))).
Proof.
  intros b [m mr [mb mv]]; simpl; specialize (mv b).
  destruct ZTree.get; simpl.
    by apply (proj1 (proj2 (mv _ (refl_equal _)))).
  by split; intros; rewrite ZTree.gempty in *.
Qed.

Hint Resolve cont_bytes_ok_mem.

Lemma load_store_other:
  forall {c m p v m' c' p'},
    store_ptr c m p v = Some m' ->
    ranges_disjoint (range_of_chunk p c) (range_of_chunk p' c') ->
    load_ptr c' m p' = load_ptr c' m' p'.
Proof.
  intros c m p v m' c' p' STORE DISJ.
  destruct p as [b ofs]. destruct p' as [b' ofs']. simpl.
  destruct (memop_with_inv_spec STORE) as [SB [OTHER MR]]; try done.
  unfold store_in_block in SB. 
  destruct in_block; try done.
  (*destruct (in_block c bc (Int.unsigned ofs)) as [VBA | NVBA]; try done.*)
  (* If loading in another block, it is easy *)
  destruct (zeq b b') as [<- | N]; [|by unfold load; rewrite OTHER].
  destruct DISJ as [Bneq | RD]; try done.
  unfold load. apply sym_eq in SB. injection SB as SB'.
  destruct (in_block c' (allocs (block_contents_o2e (ZTree.get b (mcont m)))) (Int.unsigned ofs')) as [VBAO | NVBAO];
  destruct (in_block c' (allocs (block_contents_o2e (ZTree.get b (mcont m')))) (Int.unsigned ofs')) as [VBAO' | NVBAO'];
  rewrite SB' in *; try done.
  (* Both loads succeed *)
  destruct ((block_contents_o2e (ZTree.get b (mcont m)))) as [bc al] _eqn:EQ; unfold contents, allocs in *.
  simpl; destruct stored_value.
    rewrite getN_setN_other with (al := al); try done.
      by rewrite <- ?EQ.
    by rewrite ! size_chunk_repr, ! size_chunk_pred in RD; omega.
  rewrite <- getN_clear_values_other with (n1 := pred_size_chunk c) (p1 := (Int.unsigned ofs)) (al:=al); try done.
    by rewrite <- EQ.
  by rewrite ! size_chunk_repr, ! size_chunk_pred in RD; omega.
Qed.

Lemma load_store_overlap:
  forall {c c' m p p' v m'},
    store_ptr c m p v = Some m' ->
    ranges_overlap (range_of_chunk p c) (range_of_chunk p' c') ->
    range_of_chunk p c <> range_of_chunk p' c' ->
    chunk_allocated_and_aligned p' c' m' -> 
    load_ptr c' m' p' = Some Vundef.
Proof.
  intros c c' m p p' v m' STORE Ro Rneq CA.
  apply chunk_allocated_impl_vba in CA.
  destruct p as [b ofs]. destruct p' as [b' ofs']. simpl in *.
  destruct (memop_with_inv_spec STORE) as [SB OTHER]; try done.
  destruct (ranges_overlapD Ro) as [-> [O1 O2]]. 
  unfold store_in_block in SB. 
  destruct in_block; try done.  
  unfold load.
  destruct in_block; try done.  
  inv SB; simpl.
  destruct stored_value.
  (* stored value some *)
   destruct (Int.eq_dec ofs ofs') as [-> | Neqofs].
    unfold range_of_chunk in Rneq. 
    destruct (Int.eq_dec (Int.repr (size_chunk c)) 
                         (Int.repr (size_chunk c'))) as [Ec | Neqc].
    rewrite Ec in Rneq; done.
    rewrite getN_setN_mismatch. destruct c'; done. 
    by intro Epsc; rewrite !size_chunk_pred, Epsc in Neqc.
  destruct ((block_contents_o2e (ZTree.get b' (mcont m)))) as [bc al] _eqn:EQ; unfold contents, allocs in *.
  rewrite getN_setN_overlap with (al:=al); try done.
    by destruct c'. 
    by rewrite <- EQ.
    by intro Ne; elim Neqofs; apply Int.unsigned_eq.
    rewrite size_chunk_repr, size_chunk_pred in O1, O2; omega.
  rewrite size_chunk_repr, size_chunk_pred in O1, O2; omega.
  (* stored value none *)
  replace Vundef with (Val.load_result c' Vundef); [|by destruct c']. 
  f_equal; f_equal.
  destruct ((block_contents_o2e (ZTree.get b' (mcont m)))) as [bc al] _eqn:EQ; unfold contents, allocs in *.
  apply getN_clear_values_overlap with (al:=al); try done.
      by rewrite <- EQ.
    rewrite size_chunk_repr, size_chunk_pred in O1, O2; omega.
  rewrite size_chunk_repr, size_chunk_pred in O1, O2; omega.
Qed.

Lemma load_store_mismatch:
  forall {c c' m p p' v v' m'}
    (STO: store_ptr c m p v = Some m')
    (LD: load_ptr c' m p' = Some v')
    (OVER: ranges_overlap (range_of_chunk p c) (range_of_chunk p' c'))
    (NEQ: range_of_chunk p c <> range_of_chunk p' c'),
    load_ptr c' m' p' = Some Vundef.
Proof.
  intros; eapply load_store_overlap; try edone.
  destruct (load_chunk_allocated_someD LD) as [(? & ? & ? & ?) ?].
  split; try done; repeat eexists; try edone.
  eby eapply (store_preserves_allocated_ranges STO).
Qed.

Lemma load_alloc_inside:
  forall {r k m m' c' p'},
    alloc_ptr r k  m = Some m' ->
    range_inside (range_of_chunk p' c') r ->
    pointer_chunk_aligned p' c' ->
    load_ptr c' m' p' = Some Vundef.
Proof.
  intros [[b ofs] s] k m m' c' [b' ofs'] AP RI PA.
  destruct RI as [-> [[_ [Z _]]|Ineqs]]; [by destruct c'|].
  rewrite size_chunk_repr in Ineqs.
  simpl in *.
  destruct (alloc_ptr_inv AP) as [[AL CON] [OTH Ineqs2]].
  pose proof (alloc_allocates AL) as RA.
  unfold load.
  destruct in_block.
    (* Load success *)
    f_equal. f_equal.
    rewrite CON.
    pose proof (proj2 (mvalid m) b) as BV.
    pose proof (mem_valid_to_hbound m b) as [hnd [AHBND BNM]].
    destruct (ZTree.get b (mcont m)) as [[bc ba]|]; simpl;
      [|by rewrite getN_empty; destruct c'].
    destruct (BV _ (refl_equal _)) as [_ [[UU _] _]].
    exploit (UU (Int.unsigned ofs')).
      intros k' [l' [h' [RA' Ineqs']]]. 
      assert (1 <= size_chunk c'). by destruct c'.
      refine (alloc_allocated_was_free AHBND AL 
                    _ _ _ _ _ RA'); omega.
    by unfold getN; simpl; intros ->; destruct c'. 
  elim n; econstructor; try edone.
  eexists; eexists; split. apply RA. omega.
Qed.


Lemma load_alloc_overlap:
  forall {r k m m' c' p'},
    alloc_ptr r k  m = Some m' ->
    ~ range_inside (range_of_chunk p' c') r ->
    ranges_overlap (range_of_chunk p' c') r ->
    load_ptr c' m' p' = None.
Proof.
  intros r k m m' c' p' AP RNI RO.
  pose proof (load_chunk_allocated_spec c' m' p') as LDS. 
  destruct (load_ptr c' m' p'); try done.
  destruct LDS as [[r' [k' [RI' RA']]] ALG].
  destruct (alloc_someD AP) as [RA _].
  byContradiction.
  destruct (ranges_are_disjoint RA RA') as [[-> ->] | DISJ]; [by apply RNI|].
  elim RO; eapply disjoint_inside_disjoint; [|eassumption].
  eby apply ranges_disjoint_comm, DISJ.
Qed.


Lemma load_alloc_other:
  forall {r k m m' c' p'}
    (AP: alloc_ptr r k  m = Some m')
    (RDISJ: ranges_disjoint (range_of_chunk p' c') r),
    load_ptr c' m' p' = load_ptr c' m p'.
Proof.
  intros [[b ofs] s]  k m m' c' [b' ofs'] AP RDISJ.
  destruct (alloc_ptr_inv AP) as [[AL CON] [OTH Ineqs2]].
  destruct (zeq b b') as [<- | Neqb].
    (* Same block load *)
    simpl in *. unfold load. rewrite CON.
    destruct (in_block) (* c' bc' (Int.unsigned ofs'))*) as [IN' | NIN'];
      destruct (in_block) (* c' bc (Int.unsigned ofs'))*) as [IN | NIN]; 
        try done.
      elim NIN; destruct IN' as [k' [l [h [RA IE]]] ALG]. 
      econstructor; [|done]. 
      exists l; exists h; split; [|done].
      destruct (alloc_preserves_allocated_bw AL RA) as [? | [? [? ?]]].
        edone.
      unfold ranges_disjoint, range_of_chunk in RDISJ. 
      rewrite size_chunk_repr in RDISJ. 
      assert (1 <= size_chunk c') by (destruct c'; done).
      by destruct RDISJ as [NBB | [IE1 | IE2]]; omegaContradiction. 
    elim NIN'; destruct IN as [k' [l [h [RA IE]]] ALG].
    econstructor; [|done].
    exists l; exists h; split; [|done].
    eby eapply alloc_preserves_allocated_al.
  by simpl; unfold load; rewrite OTH.
Qed.

Lemma load_some_alloc:
  forall {c m p v r k m'}
    (LD: load_ptr c m p = Some v)
    (AL: alloc_ptr r k m = Some m'),
  load_ptr c m' p = Some v.
Proof.
  intros; rewrite (load_alloc_other AL); [done|].
  destruct (load_chunk_allocated_someD LD) as [[r' [k' [RI RA]]] _].
  destruct (alloc_someD AL) as [_ [_ [_ ONA]]].
  destruct (ranges_disjoint_dec r' r).
    eby eapply disjoint_inside_disjoint.
  byContradiction.
  eby eapply ONA; [apply ranges_overlap_comm|].
Qed.

Lemma abs_unsigned:
  forall x,  Z_of_nat (Zabs_nat (Int.unsigned x)) = Int.unsigned x.
Proof.
  intro x.
  rewrite inj_Zabs_nat, Zabs_eq; [done|exact (proj1 (Int.unsigned_range x))].
Qed.

Lemma getN_clear_values_other1:
  forall n p n' p' cm al,
    cont_bytes_ok (mkblock cm al) ->
    (p + Z_of_nat n < p' \/ p' + Z_of_nat n' <= p) ->
    getN n p (clear_values p' n' cm) = getN n p cm.
Proof.
  intros n p n' p' cm al OK Ineq.
  unfold getN. 
  destruct (ZTree.get p (clear_values p' n' cm)) as [[m|]|] _eqn: EQ; 
    destruct (ZTree.get p cm) as [[m'|]|] _eqn: EQ'; 
    try rewrite (clear_values_some _ _ _ _ _ EQ) in EQ'; clarify.
  apply clear_values_datum with (q:=p') (n1:=n') (al:=al) in EQ'; try done.
  rewrite EQ in EQ'.
  destruct eq_nat_dec; clarify.
  omegaContradiction.
Qed.

Lemma load_free_other:
  forall {p n k m m' c' p'},
    free_ptr p k  m = Some m' ->
    range_allocated (p, n) k m ->
    ranges_disjoint (range_of_chunk p' c') (p, n) ->
    load_ptr c' m' p' = load_ptr c' m p'.
Proof.
  intros [b ofs] s k m m' c' [b' ofs'] FP RA RDISJ.
  destruct (memop_with_inv_spec FP) as [FB [OTH _]].
  destruct (zeq b b') as [<- | Neqb].
    (* Same block load *)
    unfold free_block in FB.
    destruct ((free_in_alloclist (Int.unsigned ofs) k 
                (allocs (block_contents_o2e (ZTree.get b (mcont m))))))
      as [[nal fh]|] _eqn : FBE; [|done].
    simpl in RA.
    pose proof (free_must_have_been_allocated _ _ _ _ _ FBE) as RA2.
    pose proof (mem_valid_to_hbound m b) as [hbnd [AHBND BNM]].
    simpl in *. unfold load. 
    destruct (in_block) as [IN' | NIN'];
      destruct (in_block) as [IN | NIN]; try done.
        inv FB. simpl.
        destruct ((block_contents_o2e (ZTree.get b (mcont m)))) as [bc al] _eqn:EQ; 
          unfold contents, allocs in *.
        rewrite getN_clear_values_other1 with (al:=al); try done.
          by rewrite <- EQ.
        destruct (allocated_al_same AHBND RA RA2) as [<- _].
        rewrite Zminus_plus, abs_unsigned.
        by destruct RDISJ as [? | [? | ?]]; 
          [done|rewrite size_chunk_repr, size_chunk_pred in *|]; omega.
      elim NIN. destruct IN' as [k' [l' [h' [RA' IE']]] ALG].
      econstructor; try done; exists l'; exists h'.
      split; [|omega]; inv FB.
      destruct (block_contents_o2e (ZTree.get b (mcont m'))); simpl in *; clarify.
      by apply (free_in_alloclist_bw _ _ _ _ _ FBE _ _ _ RA').
    elim NIN'. destruct IN as [k' [l' [h' [RA' IE']]] ALG].
    constructor 1 with (k:=k'); [|done]. exists l'; exists h'.
    split; [|done]. inv FB.
    assert (SC: 0 < size_chunk c'); [destruct c'; simpl; by compute|].
    destruct (free_in_alloclist_fw _ _ _ _ _ FBE _ _ _ RA')
      as [ | [-> [-> ->]]]; try done.
    destruct (allocated_al_same AHBND RA RA2) as [<- _].
    destruct RDISJ as [NB | [NE1 | NE2]];
      [done|rewrite size_chunk_repr in *|]; omegaContradiction. 
  by simpl; unfold load; rewrite OTH.
Qed.


Lemma load_free_overlap:
  forall {p n k m m' c' p'},
    free_ptr p k m = Some m' ->
    range_allocated (p, n) k m ->
    ranges_overlap (range_of_chunk p' c') (p, n) ->
    load_ptr c' m' p' = None.
Proof.
  intros p n k m m' c' p' FP RA RO.
  pose proof (load_chunk_allocated_spec c' m' p') as LDS.
  destruct (load_ptr c' m' p'); try done.
  byContradiction.
  destruct LDS as [[r' [k' [RI' RA']]] ALG].
  pose proof (free_preserves_allocated_back FP _ _ RA') as RAO.
  destruct (ranges_are_disjoint RA RAO) as [[<- <-] | DISJ].
    by destruct (free_not_allocated FP _ _ RA').
  eby elim RO; eapply disjoint_inside_disjoint; [eapply ranges_disjoint_comm|]. 
Qed.


Lemma load_clear_other:
  forall p c r m,
    ranges_disjoint (range_of_chunk p c) r ->
    load_ptr c (clear_range r m) p = load_ptr c m p.
Proof.
  intros [b ofs] c' [[b' ofs'] s'] m RDISJ.
  unfold clear_range, clear_mem; simpl.
  unfold load; simpl.
  unfold clear_block. simpl.
  destruct (zeq b b') as [<- | Neqb].
  2: by destruct block_contents_eq_dec; clarify; 
        rewrite ?ZTree.gro, ?ZTree.gso; try intro; clarify.

  destruct block_contents_eq_dec; clarify; 
        rewrite ?ZTree.grs, ?ZTree.gss; clarify; simpl in *.

  destruct ZTree.get; try done; simpl in *.
  inv e.
  destruct in_block as [VALID|]; [|done]. 
  by rewrite H1 in VALID; destruct VALID as (? & ? & ? & XXX & _); inv XXX.

  destruct in_block as [VALID|]; [|done]. 
  destruct ((block_contents_o2e (ZTree.get b (mcont m)))) as [bc al] _eqn:EQ; 
    unfold contents, allocs in *.
  rewrite getN_clear_values_other1 with (al:=al); try done.
  - by rewrite <- EQ.
  unfold ranges_disjoint, range_of_chunk in RDISJ. 
  rewrite Zminus_plus, abs_unsigned, size_chunk_repr, size_chunk_pred in *; omega.
Qed.


Lemma clear_preserves_allocated:
  forall r k r' m,
    range_allocated r k (clear_range r' m) <-> 
    range_allocated r k m.
Proof.
  intros [[b ofs] s] k [[b' ofs'] s'] m; simpl.
  unfold clear_block.
  destruct block_contents_eq_dec; destruct (zeq b b'); clarify;
    rewrite ?ZTree.grs, ?ZTree.gss, ?ZTree.gro, ?ZTree.gso; clarify.
  by simpl; inv e.
Qed.


Lemma load_clear_none:
  forall p c r m,
    load_ptr c m p = None <-> load_ptr c (clear_range r m) p = None.
Proof.
  intros.
  assert (X:= load_chunk_allocated_spec c m p).
  assert (Y:= load_chunk_allocated_spec c (clear_range r m) p).
  do 2 destruct load_ptr; split; try done.
  - destruct X as [(? & ? & ? & ?) ?]; destruct Y; repeat econstructor; try edone. 
    eby eapply clear_preserves_allocated.
  - destruct X; destruct Y as [(? & ? & ? & ?) ?]; repeat econstructor; try edone. 
    eby eapply clear_preserves_allocated.
Qed.

Lemma load_clear_overlap:
  forall {p c r m v}
    (LD: load_ptr c m p = Some v)
    (ROVER: ranges_overlap (range_of_chunk p c) r)
    (RNE: range_non_empty r),
    load_ptr c (clear_range r m) p = Some Vundef.
Proof.
  intros [b ofs] c [[b' ofs'] s'] m v; intros. 
  destruct (ranges_overlapD ROVER) as (? & ? & ?); clarify.
  unfold clear_range, clear_mem, range_non_empty, snd in *; simpl in LD; simpl.
  unfold load in *; simpl.
  unfold clear_block.

  destruct block_contents_eq_dec; clarify; 
        rewrite ?ZTree.grs, ?ZTree.gss; clarify; simpl.

  inv e.
  destruct in_block as [VALID|]; clarify; []. 
  by rewrite H3 in VALID; destruct VALID as (? & ? & ? & XXX & _); inv XXX.

  destruct in_block as [VALID|]; clarify; []. 
  destruct ((block_contents_o2e (ZTree.get b' (mcont m)))) as [bc al] _eqn:EQ; 
    unfold contents, allocs in *.

  rewrite Zminus_plus, size_chunk_repr, size_chunk_pred in *. 
  f_equal.
  destruct (Zabs_nat (Int.unsigned s')) as [] _eqn: ZEQ. 
  - eapply (f_equal Z_of_nat) in ZEQ; rewrite abs_unsigned in ZEQ. 
    replace (Z_of_nat 0) with 0 in * by done.
    rewrite ZEQ in *; omegaContradiction.
  rewrite getN_clear_values_overlap with (al:=al); try done. 
  - by destruct c.
  - by rewrite <- EQ.
  - eapply (f_equal Z_of_nat) in ZEQ; rewrite inj_S, abs_unsigned in ZEQ; omega.
  omega.
Qed.

Lemma clear_empty:
  forall p c r m, ~ range_non_empty r ->
    load_ptr c (clear_range r m) p = load_ptr c m p.
Proof.
  unfold range_non_empty, clear_range, clear_mem.
  intros [pb po] c [[b ofs] s] m LT; simpl in *.
  unfold load; simpl. 
  unfold clear_block.
  rewrite Zminus_plus.
  assert (Int.unsigned s = 0) as -> by (pose proof (Int.unsigned_range s); omega).
  simpl.
  destruct (zeq pb b); clarify.
    destruct block_contents_eq_dec; clarify; 
    rewrite ?ZTree.grs, ?ZTree.gss; clarify; simpl in *; [].
    by inv e; destruct in_block as [VALID|]; clarify. 
  by destruct block_contents_eq_dec; clarify; 
     rewrite ?ZTree.gro, ?ZTree.gso; clarify.
Qed.

Lemma load_clear_back:
  forall {p c r m v}
    (LD: load_ptr c (clear_range r m) p = Some v), 
    exists v'', load_ptr c m p = Some v'' /\ Val.lessdef v v''.
Proof.
  intros.
  destruct (ranges_disjoint_dec (range_of_chunk p c) r) as [DISJ|OVER].
    by rewrite load_clear_other in LD; eauto.
  assert (range_non_empty r \/ ~ range_non_empty r) as [?|?].
    by destruct r; unfold range_non_empty; simpl; omega.
  2: by rewrite clear_empty in LD; eauto.
  destruct (load_ptr c m p) as [] _eqn: LD'.
    erewrite @load_clear_overlap in LD; clarify; eauto. 
  by apply (load_clear_none _ _ r) in LD'; clarify'. 
Qed.

(*============================================================================*)
(** * Initialization *)

(** Build a block filled with the given initialization data. *)

Definition size_init_data (id: init_data) : Z :=
  match id with
  | Init_int8 _ => 1
  | Init_int16 _ => 2
  | Init_int32 _ => 4
  | Init_float32 _ => 4
  | Init_float64 _ => 8
  | Init_space n => Zmax n 0
  | Init_pointer _ => 4
  end.


Definition size_init_data_list (id: list init_data): Z :=
  List.fold_right (fun id sz => size_init_data id + sz) 0 id.

Remark size_init_data_list_pos:
  forall id, size_init_data_list id >= 0.
Proof.
  induction id; simpl.
  omega.
  assert (size_init_data a >= 0). destruct a; simpl; try omega. 
  generalize (Zmax2 z 0). omega. omega.
Qed.

Definition store_init_data (pos: pointer) (init : init_data) (m : mem)
                           : option mem := 
  match init with
  | Init_int8 n => store_ptr Mint8signed m pos (Vint n)
  | Init_int16 n => store_ptr Mint16signed m pos (Vint n)
  | Init_int32 n => store_ptr Mint32 m pos (Vint n)
  | Init_float32 f => store_ptr Mfloat32 m pos (Vfloat f)
  | Init_float64 f => store_ptr Mfloat64 m pos (Vfloat f)
  | Init_space n => Some m
  | Init_pointer x => None (* Not handled yet *)
  end.

Fixpoint store_init_data_list (pos: pointer) (id: list init_data) (m : mem)
                              {struct id} : option mem:=
  match id with
    | nil => Some m
    | init :: t =>
      let newpos := Ptr.add pos (Int.repr (size_init_data init)) in
      optbind (store_init_data pos init)
              (store_init_data_list newpos t m)
  end.

Definition initialize_data (pos: pointer) (id: list init_data) 
                           (k : mobject_kind) (m : mem)
                           : option mem :=
  let size := size_init_data_list id in
  let (b, ofs) := pos in
    if (Z_le_dec (Int.unsigned ofs + size) Int.modulus)
      then optbind (store_init_data_list pos id)
                   (alloc_ptr (pos, Int.repr size) k m)
      else None.

(*============================================================================*)
(** * Useful facts about memory restrictions *)

Lemma restr_of_memop:
  forall {m blockop pf b m'},
    memop_with_inv blockop pf b m = Some m' ->
    mrestr m' = mrestr m.
Proof.
  intros [mc mr mv] blockop pf b m'; simpl. 
  unfold memop_with_inv, trans; simpl.
  by destruct transsig as [[]|]; intro X; clarify.
Qed.

Lemma restr_of_store:
  forall {m p c v m'},
    store_ptr c m p v = Some m' ->
    mrestr m' = mrestr m.
Proof.
  by intros m [b ofs] c v m'; apply restr_of_memop.
Qed.

Lemma restr_of_alloc:
  forall {m r k m'},
    alloc_ptr r k m = Some m' ->
    mrestr m' = mrestr m.
Proof.
  by intros m [[b ofs] c] k m'; apply restr_of_memop.
Qed.

Lemma restr_of_free:
  forall {m r k m'},
    free_ptr r k m = Some m' ->
    mrestr m' = mrestr m.
Proof.
  by intros m [b ofs] k m'; apply restr_of_memop.
Qed.

Ltac optbind_dest H x E :=
  match type of H with
    context[optbind _ ?a] => 
      try destruct a as [x|] _eqn : E; try done; simpl in H
  end.

Lemma restr_of_store_init_data:
  forall {id p m m'},
    store_init_data p id m = Some m' ->
    mrestr m' = mrestr m.
Proof.
  intros [] p m m' SID; simpl in SID; 
    try apply (restr_of_store SID); by inv SID.
Qed.

Lemma restr_of_store_init_data_list:
  forall {id p m m'},
    store_init_data_list p id m = Some m' ->
    mrestr m' = mrestr m.
Proof.
  induction id as [|h id IH]; intros p m m' SIDL. by inv SIDL. 
  simpl in SIDL. optbind_dest SIDL mi Emi.
  rewrite <- (IH _ _ _ Emi).
  apply (restr_of_store_init_data SIDL).
Qed.  

Lemma restr_of_initialize_data:
  forall {p id k m m'},
    initialize_data p id k m = Some m' ->
    mrestr m' = mrestr m.
Proof.
  intros [b ofs] id k m m' INIT.
  simpl in *.
  destruct Z_le_dec as [LE|]; [|done].
  optbind_dest INIT m'' E.
  rewrite <- (restr_of_alloc E).
  apply (restr_of_store_init_data_list INIT).
Qed.

Lemma range_allocated_consistent_with_restr:
  forall p n k m,
    range_allocated (p, n) k m ->
    mrestr m (Ptr.block p) = true.
Proof.
  intros [b ofs] n k m RA; simpl.
  unfold range_allocated in RA.
  destruct (ZTree.get b (mcont m)) as [bc|] _eqn : BC.
    apply (proj1 (proj2 (mvalid m) _ _ BC)).
  simpl in RA. unfold range_allocated_al in RA. done.
Qed.
