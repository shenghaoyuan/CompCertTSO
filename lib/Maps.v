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

(** Applicative finite maps are the main data structure used in this
  project.  A finite map associates data to keys.  The two main operations
  are [set k d m], which returns a map identical to [m] except that [d]
  is associated to [k], and [get k m] which returns the data associated
  to key [k] in map [m].  In this library, we distinguish two kinds of maps:
- Trees: the [get] operation returns an option type, either [None]
  if no data is associated to the key, or [Some d] otherwise.
- Maps: the [get] operation always returns a data.  If no data was explicitly
  associated with the key, a default data provided at map initialization time
  is returned.

  In this library, we provide efficient implementations of trees and
  maps whose keys range over the type [positive] of binary positive
  integers or any type that can be injected into [positive].  The
  implementation is based on radix-2 search trees (uncompressed
  Patricia trees) and guarantees logarithmic-time operations.  An
  inefficient implementation of maps as functions is also provided.
*)

Require Import Coqlib.

Set Implicit Arguments.

(** * The abstract signatures of trees *)

Module Type TREE.
  Variable elt: Type.
  Variable elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Variable t: Type -> Type.
  Variable eq: forall (A: Type), (forall (x y: A), {x=y} + {x<>y}) ->
                forall (a b: t A), {a = b} + {a <> b}.
  Variable empty: forall (A: Type), t A.
  Variable get: forall (A: Type), elt -> t A -> option A.
  Variable set: forall (A: Type), elt -> A -> t A -> t A.
  Variable remove: forall (A: Type), elt -> t A -> t A.

  (** The ``good variables'' properties for trees, expressing
    commutations between [get], [set] and [remove]. *)
  Hypothesis gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Hypothesis gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Hypothesis gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Hypothesis gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Hypothesis gsident:
    forall (A: Type) (i: elt) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.

  (* We could implement the following, but it's not needed for the moment.
    Hypothesis grident:
      forall (A: Type) (i: elt) (m: t A) (v: A),
      get i m = None -> remove i m = m.
  *)
  Hypothesis grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Hypothesis gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Hypothesis grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.

  (** Extensional equality between trees. *)
  Variable beq: forall (A: Type), (A -> A -> bool) -> t A -> t A -> bool.
  Hypothesis beq_correct:
    forall (A: Type) (P: A -> A -> Prop) (cmp: A -> A -> bool),
    (forall (x y: A), cmp x y = true -> P x y) ->
    forall (t1 t2: t A), beq cmp t1 t2 = true ->
    forall (x: elt),
    match get x t1, get x t2 with
    | None, None => True
    | Some y1, Some y2 => P y1 y2
    | _, _ => False
    end.
  Implicit Arguments beq_correct [A].

  Hypothesis ext: forall A (m1 m2: t A),
    (forall (x: elt), get x m1 = get x m2) -> m1 = m2.

  Hypothesis sss:
    forall (A: Type) (i: elt) (m: t A) (v v': A),
    set i v (set i v' m) = set i v m.
  Hypothesis sso:
    forall (A: Type) (i j: elt) (m: t A) (v v': A),
    i <> j ->
    set i v (set j v' m) = set j v' (set i v m).

  (** Applying a function to all data of a tree. *)
  Variable map:
    forall (A B: Type), (elt -> A -> B) -> t A -> t B.
  Hypothesis gmap:
    forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).

  (** Applying a function pairwise to all data of two trees. *)
  Variable combine:
    forall (A: Type), (option A -> option A -> option A) -> t A -> t A -> t A.
  Hypothesis gcombine:
    forall (A: Type) (f: option A -> option A -> option A),
    f None None = None ->
    forall (m1 m2: t A) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).
  Hypothesis combine_commut:
    forall (A: Type) (f g: option A -> option A -> option A),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.

  (** Enumerating the bindings of a tree. *)
  Variable elements:
    forall (A: Type), t A -> list (elt * A).
  Hypothesis elements_correct:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Hypothesis elements_complete:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Hypothesis elements_keys_norepet:
    forall (A: Type) (m: t A), 
    NoDup (List.map (@fst elt A) (elements m)).

  (** Folding a function over all bindings of a tree. *)
  Variable fold:
    forall (A B: Type), (B -> elt -> A -> B) -> t A -> B -> B.
  Hypothesis fold_spec:
    forall (A B: Type) (f: B -> elt -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.

  (** Lifting well_founded relation on elements to trees. *)
  Variable order: 
    forall (A : Type), (A -> A -> Prop) -> t A -> t A -> Prop.
  Hypothesis order_wf:
    forall (A : Type) (oel : A -> A -> Prop),
      well_founded oel -> well_founded (order oel).
  Hypothesis order_set_lt:
    forall (A : Type) (lt : A -> A -> Prop) (tr : t A) (el : elt)
           (val nval : A),
      get el tr = Some val -> lt nval val ->
      (order lt) (set el nval tr) tr.

End TREE.

(** * The abstract signatures of maps *)

Module Type MAP.
  Variable elt: Type.
  Variable elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Variable t: Type -> Type.
  Variable init: forall (A: Type), A -> t A.
  Variable get: forall (A: Type), elt -> t A -> A.
  Variable set: forall (A: Type), elt -> A -> t A -> t A.
  Hypothesis gi:
    forall (A: Type) (i: elt) (x: A), get i (init x) = x.
  Hypothesis gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = x.
  Hypothesis gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Hypothesis gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Hypothesis gsident:
    forall (A: Type) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
  Variable map: forall (A B: Type), (A -> B) -> t A -> t B.
  Hypothesis gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
End MAP.

(** * An implementation of trees over type [positive] *)

(* Ideally we would do:

   Module PTree : 
     TREE with Definition elt := positive
          with Definition elt_eq := peq.

but extraction leads to a mysterious error *)

Module PTree <: TREE.
  Definition elt := positive.
  Definition elt_eq := peq.

  Inductive tree (A : Type) : Type :=
    | Leaf : tree A
    | Node : tree A -> option A -> tree A -> tree A
  .
  Implicit Arguments Leaf [A].
  Implicit Arguments Node [A].

  Fixpoint wf (A : Type) (m : tree A) {struct m} : bool :=
    match m with
    | Leaf => true
    | Node t1 None t2 => match t1, t2 with Leaf, Leaf => false | _, _ => wf t1 && wf t2 end
    | Node t1 (Some _) t2 => wf t1 && wf t2
    end.

  Lemma wfNode (A : Type):
     forall (m1: tree A) o m2, wf (Node m1 o m2) -> wf m1 /\ wf m2.
  Proof.
     by simpl; intros m1 o m2 H; destruct o; destruct m1; destruct m2;
        clarify; case (andP H).
  Qed.

  Definition t A := {x : tree A | wf x = true}.

  Lemma prove_eq:
    forall A (x : tree A) y Px Py, x = y -> exist (fun x => wf x) x Px = exist _ y Py.
  Proof.
    intros; clarify.
    generalize (proof_irrelevance _ Px Py); intro; clarify.
  Qed.

  Theorem tree_eq : forall (A : Type),
    (forall (x y: A), {x=y} + {x<>y}) ->
    forall (a b : tree A), {a = b} + {a <> b}.
  Proof.
    intros A eqA.
    decide equality.
    generalize o o0; decide equality.
  Qed.

  Theorem eq : forall (A : Type),
    (forall (x y: A), {x=y} + {x<>y}) ->
    forall (a b : t A), {a = b} + {a <> b}.
  Proof.
    intros A eqA a b.
    destruct a as [a aPF]; destruct b as [b bPF].
    destruct (tree_eq eqA a b); clarify.
      by left; rewrite (proof_irrelevance _ aPF bPF).
    by right; intro H; inv H. 
  Qed.

  Definition empty (A : Type) : t A := 
    exist _ Leaf (refl_equal true).  

  Fixpoint tree_get (A : Type) (i : positive) (m : tree A) {struct i} : option A :=
    match m with
    | Leaf => None
    | Node l o r =>
        match i with
        | xH => o
        | xO ii => tree_get ii l
        | xI ii => tree_get ii r
        end
    end.

  Definition get (A : Type) (i : positive) (m : t A) := 
    tree_get i (proj1_sig m). 

  Fixpoint tree_set (A : Type) (i : positive) (v : A) (m : tree A) {struct i} : tree A :=
    match m with
    | Leaf =>
        match i with
        | xH => Node Leaf (Some v) Leaf
        | xO ii => Node (tree_set ii v Leaf) None Leaf
        | xI ii => Node Leaf None (tree_set ii v Leaf)
        end
    | Node l o r =>
        match i with
        | xH => Node l (Some v) r
        | xO ii => Node (tree_set ii v l) o r
        | xI ii => Node l o (tree_set ii v r)
        end
    end.

  Lemma tree_set_wf: forall (A: Type) i (v : A) m, 
      wf m -> wf (tree_set i v m).
  Proof.
    by intros A i v; induction i; intros m mWF; destruct m; simpl in *; try done;
       try rewrite IHi; try destruct i; try done;
       destruct m1; destruct o; destruct m2; try done;
       destruct (andP mWF) as [X1 X2]; rewrite ?X1, ?X2.
  Qed.

  Definition set (A : Type) (i : positive) (v : A) (m : t A) : t A := 
    exist _ (tree_set i v (proj1_sig m)) (tree_set_wf i v (proj1_sig m) (proj2_sig m)).

  Fixpoint tree_remove (A : Type) (i : positive) (m : tree A) {struct i} : tree A :=
    match i with
    | xH =>
        match m with
        | Leaf => Leaf
        | Node Leaf o Leaf => Leaf
        | Node l o r => Node l None r
        end
    | xO ii =>
        match m with
        | Leaf => Leaf
        | Node l None Leaf =>
            match tree_remove ii l with
            | Leaf => Leaf
            | mm => Node mm None Leaf
            end
        | Node l o r => Node (tree_remove ii l) o r
        end
    | xI ii =>
        match m with
        | Leaf => Leaf
        | Node Leaf None r =>
            match tree_remove ii r with
            | Leaf => Leaf
            | mm => Node Leaf None mm
            end
        | Node l o r => Node l o (tree_remove ii r)
        end
    end.

  Lemma tree_remove_wf (A : Type) : forall i (m: tree A),
      wf m -> wf (tree_remove i m).
  Proof.
    induction i; intros m mWF; destruct m; simpl in *; try done;
       try rewrite IHi; try (by destruct i); try done;
       destruct m1; destruct o; destruct m2; try done;
       destruct (andP mWF) as [X1 X2]; clear mWF; rewrite ?X1, ?X2; simpl;
       try done; try rewrite IHi; try (by destruct i);
       try generalize (IHi _ X1); try generalize (IHi _ X2); simpl in *; try done;
       by repeat destruct tree_remove; simpl; rewrite ?andbT.
  Qed.

  Definition remove (A : Type) (i : positive) (m : t A) : t A :=
    exist _ (tree_remove i (proj1_sig m)) (tree_remove_wf i (proj1_sig m) (proj2_sig m)).

  Theorem gempty:
    forall (A: Type) (i: positive), get i (empty A) = None.
  Proof.
    induction i; simpl; auto.
  Qed.

  Theorem gss:
    forall (A: Type) (i: positive) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof.
    destruct m as [m mPF]; unfold get, set; simpl.
    clear mPF; revert m; induction i; destruct m; simpl; auto.
  Qed.

    Lemma gleaf : forall (A : Type) (i : positive), tree_get i (Leaf : tree A) = None.
    Proof. exact gempty. Qed.

  Theorem gso:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    destruct m as [m mPF]; unfold get, set; simpl; clear mPF; revert j m.
    induction i; intros; destruct j; destruct m; simpl;
       try rewrite <- (gleaf A i); auto; try apply IHi; congruence.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    get i (set j x m) = if peq i j then Some x else get i m.
  Proof.
    intros.
    destruct (peq i j); [ rewrite e; apply gss | apply gso; auto ].
  Qed.

  Theorem gsident:
    forall (A: Type) (i: positive) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  Proof.
    intros A i [m mPF] v G; unfold get, set in *; simpl in *.
    apply prove_eq.
    clear mPF; revert m v G.
    by induction i; intros; destruct m; simpl in *; try congruence; rewrite IHi.
  Qed.

    Lemma rleaf : forall (A : Type) (i : positive), tree_remove i (Leaf : tree A) = Leaf.
    Proof. destruct i; simpl; auto. Qed.

  Theorem grs:
    forall (A: Type) (i: positive) (m: t A), get i (remove i m) = None.
  Proof.
    intros A i [m mPF]; unfold get, set; simpl; clear mPF; revert m.
    induction i; destruct m.
     simpl; auto.
     destruct m1; destruct o; destruct m2 as [ | ll oo rr]; simpl; auto.
      rewrite (rleaf A i); auto.
      cut (tree_get i (tree_remove i (Node ll oo rr)) = None).
        destruct tree_remove; try done; apply IHi.
        apply IHi.
     simpl; auto.
     destruct m1 as [ | ll oo rr]; destruct o; destruct m2; simpl; auto.
      rewrite (rleaf A i); auto.
      cut (tree_get i (tree_remove i (Node ll oo rr)) = None).
        destruct tree_remove; try done; apply IHi.
        apply IHi.
     simpl; auto.
     destruct m1; destruct m2; simpl; auto.
  Qed.

  Theorem gro:
    forall (A: Type) (i j: positive) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof.
    intros A i j [m mPF]; unfold get, remove; simpl; clear mPF; revert j m.
    induction i; intros; destruct j; destruct m;
        try rewrite (rleaf A (xI j));
        try rewrite (rleaf A (xO j));
        try rewrite (rleaf A 1); auto;
        destruct m1; destruct o; destruct m2;
        simpl;
        try apply IHi; try congruence;
        try rewrite (rleaf A j); auto;
        try rewrite (gleaf A i); auto;
        try (by destruct tree_remove; simpl; try rewrite (gleaf A i)).
     cut (tree_get i (tree_remove j (Node m2_1 o m2_2)) = tree_get i (Node m2_1 o m2_2));
        [ destruct tree_remove; try rewrite (gleaf A i); auto
        | apply IHi; congruence ].
     cut (tree_get i (tree_remove j (Node m1_1 o0 m1_2)) = tree_get i (Node m1_1 o0 m1_2));
        [ by destruct tree_remove; try rewrite (gleaf A i)
        | apply IHi; congruence ].
  Qed.

  Theorem grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    intros. destruct (elt_eq i j). subst j. apply grs. apply gro; auto.
  Qed.

  Section EXTENSIONAL_EQUALITY.

    Variable A: Type.
    Variable eqA: A -> A -> Prop.
    Variable beqA: A -> A -> bool.
    Hypothesis beqA_correct: forall x y, beqA x y = true -> eqA x y.

    Definition exteq (m1 m2: t A) : Prop :=
      forall (x: elt),
      match get x m1, get x m2 with
      | None, None => True
      | Some y1, Some y2 => eqA y1 y2
      | _, _ => False
      end.

    Definition bempty (m: t A) : bool :=
      match proj1_sig m with
      | Leaf => true
      | Node _ _ _ => false
      end.

    Lemma bempty_correct:
      forall m, bempty m = true -> forall x, get x m = None.
    Proof.
      destruct m as [[] mPF]; unfold bempty, get; simpl; try done.
      by intros ? [].
    Qed.

    Fixpoint tree_beq (m1 m2: tree A) {struct m1} : bool :=
      match m1, m2 with
      | Leaf, Leaf => true
      | Leaf, Node _ _ _ => false
      | Node _ _ _, Leaf => false
      | Node l1 o1 r1, Node l2 o2 r2 =>
          match o1, o2 with
          | None, None => true
          | Some y1, Some y2 => beqA y1 y2
          | _, _ => false
          end
          && tree_beq l1 l2 && tree_beq r1 r2
      end.

    Definition beq (m1 m2: t A) : bool :=
       tree_beq (proj1_sig m1) (proj1_sig m2).

    Lemma beq_correct:
      forall m1 m2, beq m1 m2 -> exteq m1 m2.
    Proof.
      intros [m1 m1PF] [m2 m2PF]; unfold beq, exteq, get; simpl.
      revert m1PF m2 m2PF.
      induction m1; destruct m2; simpl; try done.
        by intros ? ? [].
      intros B.
      cut (wf m1_1 /\ wf m1_2 /\ wf m2_1 /\ wf m2_2);
        [ intros [X1 [X2 [Y1 Y2]]]
        | by destruct o; destruct o0; clarify;
             destruct m1_1; destruct m1_2; destruct m2_1; destruct m2_2; 
             clarify; try case (andP m1PF); try case (andP B)].

     intros X4 x; 
        destruct (andP X4) as [X5 Z2]; 
        destruct (andP X5) as [Z0 Z1]; clear X4 X5.
      specialize (IHm1_1 X1 m2_1 Y1 Z1). 
      specialize (IHm1_2 X2 m2_2 Y2 Z2). 

      destruct m1_1; destruct m1_2; try done;
      destruct m2_1; destruct m2_2; try done;
      destruct x; try done; simpl; 
      solve [by destruct o; destruct o0; try apply beqA_correct|by apply IHm1_1|by apply IHm1_2].
    Qed.

  End EXTENSIONAL_EQUALITY.

  Theorem ext: forall (A: Type) (m1 m2: t A), 
    (forall (x: elt), get x m1 = get x m2) -> m1 = m2.
  Proof.
    intros A [m1 W1] [m2 W2] EE; unfold get in *; simpl in *; apply prove_eq.
    revert m2 W2 EE. 
    induction m1; induction m2; try done; intros; simpl;
      try pose proof (wfNode _ _ _ W1) as [X11 X12];
      try pose proof (wfNode _ _ _ W2) as [X21 X22].
        exploit (IHm2_1 X21); [intro y; rewrite gleaf; apply (EE (xO y))|intro; subst m2_1].  
        exploit (IHm2_2 X22); [intro y; rewrite gleaf; apply (EE (xI y))|intro; subst m2_2].  
        by destruct o; try done; generalize (EE xH); rewrite gleaf.
      exploit (IHm1_1 X11 _ W2); [intro y; rewrite gleaf; apply (EE (xO y))|intro; subst m1_1].  
      exploit (IHm1_2 X12 _ W2); [intro y; rewrite gleaf; apply (EE (xI y))|intro; subst m1_2].  
      by destruct o; try done; generalize (EE xH); rewrite gleaf.
    generalize (EE xH); simpl; intro X; subst o0.
    rewrite (IHm1_1 X11 _ X21 (fun y => EE (xO y))). 
    by rewrite (IHm1_2 X12 _ X22 (fun y => EE (xI y))). 
  Qed.

  Theorem sss:
    forall (A: Type) (i: elt) (m: t A) (v v': A),
    set i v (set i v' m) = set i v m.
  Proof.
    by intros; eapply ext; intro x; destruct (peq x i); [subst; rewrite !gss | rewrite !gso].
  Qed.

  Theorem sso:
    forall (A: Type) (i j: elt) (m: t A) (v v': A),
    i <> j -> set i v (set j v' m) = set j v' (set i v m).
  Proof.
    intros; eapply ext; intro x.
    destruct (peq x i); destruct (peq x j); clarify;
      repeat first [done|rewrite gss|rewrite gso].
  Qed.

    Fixpoint append (i j : positive) {struct i} : positive :=
      match i with
      | xH => j
      | xI ii => xI (append ii j)
      | xO ii => xO (append ii j)
      end.

    Lemma append_assoc_0 : forall (i j : positive),
                           append i (xO j) = append (append i (xO xH)) j.
    Proof.
      induction i; intros; destruct j; simpl;
      try rewrite (IHi (xI j));
      try rewrite (IHi (xO j));
      try rewrite <- (IHi xH);
      auto.
    Qed.

    Lemma append_assoc_1 : forall (i j : positive),
                           append i (xI j) = append (append i (xI xH)) j.
    Proof.
      induction i; intros; destruct j; simpl;
      try rewrite (IHi (xI j));
      try rewrite (IHi (xO j));
      try rewrite <- (IHi xH);
      auto.
    Qed.

    Lemma append_neutral_r : forall (i : positive), append i xH = i.
    Proof.
      induction i; simpl; congruence.
    Qed.

    Lemma append_neutral_l : forall (i : positive), append xH i = i.
    Proof.
      simpl; auto.
    Qed.

    Fixpoint xmap (A B : Type) (f : positive -> A -> B) (m : tree A) (i : positive)
             {struct m} : tree B :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node (xmap f l (append i (xO xH)))
                           (option_map (f i) o)
                           (xmap f r (append i (xI xH)))
      end.

  Lemma xmap_wf (A B: Type) : forall (f : positive -> A -> B) (m : tree A) i,
      wf m -> wf (xmap f m i).
  Proof.
    induction m; intros i mWF; simpl; try done.
    rewrite IHm1, IHm2;
    by simpl in mWF; destruct o; clarify;
       destruct m1; clarify;
       destruct m2; clarify; destruct (andP mWF).
   Qed.

  Definition map (A B : Type) f (m : t A) : t B := 
    exist _ (xmap f (proj1_sig m) xH) (xmap_wf f (proj1_sig m) xH (proj2_sig m)).

    Lemma xgmap:
      forall (A B: Type) (f: positive -> A -> B) (i j : positive) (m: tree A),
      tree_get i (xmap f m j) = option_map (f (append j i)) (tree_get i m).
    Proof.
      induction i; intros; destruct m; simpl; auto.
      rewrite (append_assoc_1 j i); apply IHi.
      rewrite (append_assoc_0 j i); apply IHi.
      rewrite (append_neutral_r j); auto.
    Qed.

  Theorem gmap:
    forall (A B: Type) (f: positive -> A -> B) (i: positive) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
  Proof.
    intros.
    unfold map.
    replace (f i) with (f (append xH i)).
    apply xgmap.
    rewrite append_neutral_l; auto.
  Qed.

  Definition Node' (A: Type) (l: tree A) (x: option A) (r: tree A): tree A :=
    match l, x, r with
    | Leaf, None, Leaf => Leaf
    | _, _, _ => Node l x r
    end.

  Lemma Node'_wf: forall A (l : tree A) x r, wf l -> wf r -> wf (Node' l x r).
  Proof.
    intros A l x r Wl Wr; unfold Node'.
    by destruct x; destruct l; destruct r; clarify; simpl in *; rewrite ?Wl, ?Wr.
  Qed.

  Lemma gnode':
    forall (A: Type) (l r: tree A) (x: option A) (i: positive),
    tree_get i (Node' l x r) = tree_get i (Node l x r).
  Proof.
    intros. unfold Node'. 
    destruct l; destruct x; destruct r; auto.
    destruct i; simpl; auto; rewrite gleaf; auto.
  Qed.

  Section COMBINE.

  Variable A: Type.
  Variable f: option A -> option A -> option A.
  Hypothesis f_none_none: f None None = None.

  Fixpoint xcombine_l (m : tree A) {struct m} : tree A :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node' (xcombine_l l) (f o None) (xcombine_l r)
      end.

  Lemma xgcombine_l :
          forall (m: tree A) (i : positive),
          tree_get i (xcombine_l m) = f (tree_get i m) None.
    Proof.
      induction m; intros; simpl.
      repeat rewrite gleaf. auto.
      rewrite gnode'. destruct i; simpl; auto.
    Qed.

  Lemma xcombine_l_wf:
    forall (m : tree A), wf m -> wf (xcombine_l m).
  Proof.
    induction m; clarify. simpl; intro W.
    apply Node'_wf; [apply IHm1|apply IHm2];
    by destruct o; destruct m1; destruct m2; clarify; destruct (andP W).
  Qed.

  Fixpoint xcombine_r (m : tree A) {struct m} : tree A :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node' (xcombine_r l) (f None o) (xcombine_r r)
      end.

  Lemma xgcombine_r :
          forall (m: tree A) (i : positive),
          tree_get i (xcombine_r m) = f None (tree_get i m).
    Proof.
      induction m; intros; simpl.
      repeat rewrite gleaf. auto.
      rewrite gnode'. destruct i; simpl; auto.
    Qed.

  Lemma xcombine_r_wf:
    forall (m : tree A), wf m -> wf (xcombine_r m).
  Proof.
    induction m; clarify. simpl; intro W.
    apply Node'_wf; [apply IHm1|apply IHm2];
    by destruct o; destruct m1; destruct m2; clarify; destruct (andP W).
  Qed.

  Fixpoint xcombine (m1 m2 : tree A) {struct m1} : tree A :=
    match m1 with
    | Leaf => xcombine_r m2
    | Node l1 o1 r1 =>
        match m2 with
        | Leaf => xcombine_l m1
        | Node l2 o2 r2 => Node' (xcombine l1 l2) (f o1 o2) (xcombine r1 r2)
        end
    end.

  Lemma xcombine_wf:
    forall (m1 m2 : tree A), wf m1 -> wf m2 -> wf (xcombine m1 m2).
  Proof.
    induction m1; destruct m2; simpl; intros W1 W2; clarify;
    repeat first [apply Node'_wf | apply xcombine_l_wf | apply xcombine_r_wf | apply IHm1_1 | apply IHm1_2];
    by simpl in W1, W2; destruct o; try destruct o0; clarify;
       try destruct m1_1; try destruct m1_2;
       try destruct m2_1; try destruct m2_2;
       clarify; try destruct (andP W1); try destruct (andP W2).
  Qed.

  Definition combine (m1 m2 : t A) : t A :=
    exist _ (xcombine (proj1_sig m1) (proj1_sig m2))
            (xcombine_wf (proj1_sig m1) (proj1_sig m2) (proj2_sig m1) (proj2_sig m2)).

  Theorem gcombine:
      forall (m1 m2: t A) (i: positive),
      get i (combine m1 m2) = f (get i m1) (get i m2).
  Proof.
    intros [m1 W1] [m2 W2]; unfold get, combine; simpl; clear W1 W2; revert m2.
    induction m1; intros; simpl.
    rewrite gleaf. apply xgcombine_r.
    destruct m2; simpl.
    rewrite gleaf. rewrite <- xgcombine_l. auto. 
    repeat rewrite gnode'. destruct i; simpl; auto.
  Qed.

  End COMBINE.

  Lemma xcombine_lr :
    forall (A : Type) (f g : option A -> option A -> option A) (m : tree A),
    (forall (i j : option A), f i j = g j i) ->
    xcombine_l f m = xcombine_r g m.
    Proof.
      induction m; intros; simpl; auto.
      rewrite IHm1; auto.
      rewrite IHm2; auto.
      rewrite H; auto.
    Qed.

  Theorem combine_commut:
    forall (A: Type) (f g: option A -> option A -> option A),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
  Proof.
    intros A f g EQ1.
    assert (EQ2: forall (i j: option A), g i j = f j i).
      intros; auto.
    intros [m1 W1] [m2 W2]; unfold combine; simpl; apply prove_eq; clear W1 W2; revert m2.
    induction m1; intros; destruct m2; simpl;
      try rewrite EQ1;
      repeat rewrite (xcombine_lr f g);
      repeat rewrite (xcombine_lr g f);
      auto.
     rewrite IHm1_1.
     rewrite IHm1_2.
     auto. 
  Qed.

    Fixpoint xelements (A : Type) (m : tree A) (i : positive) {struct m}
             : list (positive * A) :=
      match m with
      | Leaf => nil
      | Node l None r =>
          (xelements l (append i (xO xH))) ++ (xelements r (append i (xI xH)))
      | Node l (Some x) r =>
          (xelements l (append i (xO xH)))
          ++ ((i, x) :: xelements r (append i (xI xH)))
      end.

  (* Note: function [xelements] above is inefficient.  We should apply
     deforestation to it, but that makes the proofs even harder. *)

  Definition elements A (m : t A) := xelements (proj1_sig m) xH.

    Lemma xelements_correct:
      forall (A: Type) (m: tree A) (i j : positive) (v: A),
      tree_get i m = Some v -> In (append j i, v) (xelements m j).
    Proof.
      induction m; intros.
       rewrite (gleaf A i) in H; congruence.
       destruct o; destruct i; simpl; simpl in H.
        rewrite append_assoc_1; apply in_or_app; right; apply in_cons;
          apply IHm2; auto.
        rewrite append_assoc_0; apply in_or_app; left; apply IHm1; auto.
        rewrite append_neutral_r; apply in_or_app; injection H;
          intro EQ; rewrite EQ; right; apply in_eq.
        rewrite append_assoc_1; apply in_or_app; right; apply IHm2; auto.
        rewrite append_assoc_0; apply in_or_app; left; apply IHm1; auto.
        congruence.
    Qed.

  Theorem elements_correct:
    forall (A: Type) (m: t A) (i: positive) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Proof.
    intros A m i v H.
    exact (xelements_correct (proj1_sig m) i xH H).
  Qed.

    Fixpoint xget (A : Type) (i j : positive) (m : tree A) {struct j} : option A :=
      match i, j with
      | _, xH => tree_get i m
      | xO ii, xO jj => xget ii jj m
      | xI ii, xI jj => xget ii jj m
      | _, _ => None
      end.

    Lemma xget_left :
      forall (A : Type) (j i : positive) (m1 m2 : tree A) (o : option A) (v : A),
      xget i (append j (xO xH)) m1 = Some v -> xget i j (Node m1 o m2) = Some v.
    Proof.
      induction j; intros; destruct i; simpl; simpl in H; auto; try congruence.
      destruct i; congruence.
    Qed.

    Lemma xelements_ii :
      forall (A: Type) (m: tree A) (i j : positive) (v: A),
      In (xI i, v) (xelements m (xI j)) -> In (i, v) (xelements m j).
    Proof.
      induction m.
       simpl; auto.
       intros; destruct o; simpl; simpl in H; destruct (in_app_or _ _ _ H);
         apply in_or_app.
        left; apply IHm1; auto.
        right; destruct (in_inv H0).
         injection H1; intros EQ1 EQ2; rewrite EQ1; rewrite EQ2; apply in_eq.
         apply in_cons; apply IHm2; auto.
        left; apply IHm1; auto.
        right; apply IHm2; auto.
    Qed.

    Lemma xelements_io :
      forall (A: Type) (m: tree A) (i j : positive) (v: A),
      ~In (xI i, v) (xelements m (xO j)).
    Proof.
      induction m.
       simpl; auto.
       intros; destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
        apply (IHm1 _ _ _ H0).
        destruct (in_inv H0).
         congruence.
         apply (IHm2 _ _ _ H1).
        apply (IHm1 _ _ _ H0).
        apply (IHm2 _ _ _ H0).
    Qed.

    Lemma xelements_oo :
      forall (A: Type) (m: tree A) (i j : positive) (v: A),
      In (xO i, v) (xelements m (xO j)) -> In (i, v) (xelements m j).
    Proof.
      induction m.
       simpl; auto.
       intros; destruct o; simpl; simpl in H; destruct (in_app_or _ _ _ H);
         apply in_or_app.
        left; apply IHm1; auto.
        right; destruct (in_inv H0).
         injection H1; intros EQ1 EQ2; rewrite EQ1; rewrite EQ2; apply in_eq.
         apply in_cons; apply IHm2; auto.
        left; apply IHm1; auto.
        right; apply IHm2; auto.
    Qed.

    Lemma xelements_oi :
      forall (A: Type) (m: tree A) (i j : positive) (v: A),
      ~In (xO i, v) (xelements m (xI j)).
    Proof.
      induction m.
       simpl; auto.
       intros; destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
        apply (IHm1 _ _ _ H0).
        destruct (in_inv H0).
         congruence.
         apply (IHm2 _ _ _ H1).
        apply (IHm1 _ _ _ H0).
        apply (IHm2 _ _ _ H0).
    Qed.

    Lemma xelements_ih :
      forall (A: Type) (m1 m2: tree A) (o: option A) (i : positive) (v: A),
      In (xI i, v) (xelements (Node m1 o m2) xH) -> In (i, v) (xelements m2 xH).
    Proof.
      destruct o; simpl; intros; destruct (in_app_or _ _ _ H).
        absurd (In (xI i, v) (xelements m1 2)); auto; apply xelements_io; auto.
        destruct (in_inv H0).
         congruence.
         apply xelements_ii; auto.
        absurd (In (xI i, v) (xelements m1 2)); auto; apply xelements_io; auto.
        apply xelements_ii; auto.
    Qed.

    Lemma xelements_oh :
      forall (A: Type) (m1 m2: tree A) (o: option A) (i : positive) (v: A),
      In (xO i, v) (xelements (Node m1 o m2) xH) -> In (i, v) (xelements m1 xH).
    Proof.
      destruct o; simpl; intros; destruct (in_app_or _ _ _ H).
        apply xelements_oo; auto.
        destruct (in_inv H0).
         congruence.
         absurd (In (xO i, v) (xelements m2 3)); auto; apply xelements_oi; auto.
        apply xelements_oo; auto.
        absurd (In (xO i, v) (xelements m2 3)); auto; apply xelements_oi; auto.
    Qed.

    Lemma xelements_hi :
      forall (A: Type) (m: tree A) (i : positive) (v: A),
      ~In (xH, v) (xelements m (xI i)).
    Proof.
      induction m; intros.
       simpl; auto.
       destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
        generalize H0; apply IHm1; auto.
        destruct (in_inv H0).
         congruence.
         generalize H1; apply IHm2; auto.
        generalize H0; apply IHm1; auto.
        generalize H0; apply IHm2; auto.
    Qed.

    Lemma xelements_ho :
      forall (A: Type) (m: tree A) (i : positive) (v: A),
      ~In (xH, v) (xelements m (xO i)).
    Proof.
      induction m; intros.
       simpl; auto.
       destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
        generalize H0; apply IHm1; auto.
        destruct (in_inv H0).
         congruence.
         generalize H1; apply IHm2; auto.
        generalize H0; apply IHm1; auto.
        generalize H0; apply IHm2; auto.
    Qed.

    Lemma get_xget_h :
      forall (A: Type) (m: tree A) (i: positive), tree_get i m = xget i xH m.
    Proof.
      destruct i; simpl; auto.
    Qed.

    Lemma xelements_complete:
      forall (A: Type) (i j : positive) (m: tree A) (v: A),
      In (i, v) (xelements m j) -> xget i j m = Some v.
    Proof.
      induction i; simpl; intros; destruct j; simpl.
       apply IHi; apply xelements_ii; auto.
       absurd (In (xI i, v) (xelements m (xO j))); auto; apply xelements_io.
       destruct m.
        simpl in H; tauto.
        rewrite get_xget_h. apply IHi. apply (xelements_ih _ _ _ _ _ H).
       absurd (In (xO i, v) (xelements m (xI j))); auto; apply xelements_oi.
       apply IHi; apply xelements_oo; auto.
       destruct m.
        simpl in H; tauto.
        rewrite get_xget_h. apply IHi. apply (xelements_oh _ _ _ _ _ H).
       absurd (In (xH, v) (xelements m (xI j))); auto; apply xelements_hi.
       absurd (In (xH, v) (xelements m (xO j))); auto; apply xelements_ho.
       destruct m.
        simpl in H; tauto.
        destruct o; simpl in H; destruct (in_app_or _ _ _ H).
         absurd (In (xH, v) (xelements m1 (xO xH))); auto; apply xelements_ho.
         destruct (in_inv H0).
          congruence.
          absurd (In (xH, v) (xelements m2 (xI xH))); auto; apply xelements_hi.
         absurd (In (xH, v) (xelements m1 (xO xH))); auto; apply xelements_ho.
         absurd (In (xH, v) (xelements m2 (xI xH))); auto; apply xelements_hi.
    Qed.

  Theorem elements_complete:
    forall (A: Type) (m: t A) (i: positive) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Proof.
    intros A [m W] i v H.
    unfold elements, get in *; simpl.
    rewrite get_xget_h.
    exact (xelements_complete i xH m v H).
  Qed.

  Lemma in_xelements:
    forall (A: Type) (m: tree A) (i k: positive) (v: A),
    In (k, v) (xelements m i) ->
    exists j, k = append i j.
  Proof.
    induction m; simpl; intros.
    tauto.
    assert (k = i \/ In (k, v) (xelements m1 (append i 2))
                  \/ In (k, v) (xelements m2 (append i 3))).
      destruct o.
      elim (in_app_or _ _ _ H); simpl; intuition.
      replace k with i. tauto. congruence.
      elim (in_app_or _ _ _ H); simpl; intuition.
    elim H0; intro.
    exists xH. rewrite append_neutral_r. auto.
    elim H1; intro.
    elim (IHm1 _ _ _ H2). intros k1 EQ. rewrite EQ.
    rewrite <- append_assoc_0. exists (xO k1); auto.
    elim (IHm2 _ _ _ H2). intros k1 EQ. rewrite EQ.
    rewrite <- append_assoc_1. exists (xI k1); auto.
  Qed.

  Definition xkeys (A: Type) (m: tree A) (i: positive) :=
    List.map (@fst positive A) (xelements m i).

  Lemma in_xkeys:
    forall (A: Type) (m: tree A) (i k: positive),
    In k (xkeys m i) ->
    exists j, k = append i j.
  Proof.
    unfold xkeys; intros. 
    elim (list_in_map_inv _ _ _ H). intros [k1 v1] [EQ IN].
    simpl in EQ; subst k1. apply in_xelements with A m v1. auto.
  Qed.

  Remark list_append_cons_norepet:
    forall (A: Type) (l1 l2: list A) (x: A),
    NoDup l1 -> NoDup l2 -> list_disjoint l1 l2 ->
    ~In x l1 -> ~In x l2 ->
    NoDup (l1 ++ x :: l2).
  Proof.
    intros. apply nodup_append_commut. simpl; constructor.
    red; intros. elim (in_app_or _ _ _ H4); intro; tauto.
    apply nodup_append; auto. 
    apply list_disjoint_sym; auto.
  Qed.

  Lemma append_injective:
    forall i j1 j2, append i j1 = append i j2 -> j1 = j2.
  Proof.
    induction i; simpl; intros.
    apply IHi. congruence.
    apply IHi. congruence.
    auto.
  Qed.

  Lemma xelements_keys_norepet:
    forall (A: Type) (m: tree A) (i: positive),
    NoDup (xkeys m i).
  Proof.
    induction m; unfold xkeys; simpl; fold xkeys; intros.
    constructor.
    assert (list_disjoint (xkeys m1 (append i 2)) (xkeys m2 (append i 3))).
      red; intros; red; intro. subst y. 
      elim (in_xkeys _ _ _ H); intros j1 EQ1.
      elim (in_xkeys _ _ _ H0); intros j2 EQ2.
      rewrite EQ1 in EQ2. 
      rewrite <- append_assoc_0 in EQ2. 
      rewrite <- append_assoc_1 in EQ2. 
      generalize (append_injective _ _ _ EQ2). congruence.
    assert (forall (m: tree A) j,
            j = 2%positive \/ j = 3%positive ->
            ~In i (xkeys m (append i j))).
      intros; red; intros. 
      elim (in_xkeys _ _ _ H1); intros k EQ.
      assert (EQ1: append i xH = append (append i j) k).
        rewrite append_neutral_r. auto.
      elim H0; intro; subst j;
      try (rewrite <- append_assoc_0 in EQ1);
      try (rewrite <- append_assoc_1 in EQ1);
      generalize (append_injective _ _ _ EQ1); congruence.
    destruct o; rewrite list_append_map; simpl;
    change (List.map (@fst positive A) (xelements m1 (append i 2)))
      with (xkeys m1 (append i 2));
    change (List.map (@fst positive A) (xelements m2 (append i 3)))
      with (xkeys m2 (append i 3)).
    apply list_append_cons_norepet; auto. 
    apply nodup_append; auto.
  Qed.

  Theorem elements_keys_norepet:
    forall (A: Type) (m: t A), 
    NoDup (List.map (@fst elt A) (elements m)).
  Proof.
    intros A [m W]. change (NoDup (xkeys m 1)). apply xelements_keys_norepet.
  Qed.

  Fixpoint xfold (A B: Type) (f: B -> positive -> A -> B)
                 (i: positive) (m: tree A) (v: B) {struct m} : B :=
    match m with
    | Leaf => v
    | Node l None r =>
        let v1 := xfold f (append i (xO xH)) l v in
        xfold f (append i (xI xH)) r v1
    | Node l (Some x) r =>
        let v1 := xfold f (append i (xO xH)) l v in
        let v2 := f v1 i x in
        xfold f (append i (xI xH)) r v2
    end.

  Definition fold (A B : Type) (f: B -> positive -> A -> B) (m: t A) (v: B) :=
    xfold f xH (proj1_sig m) v.

  Lemma xfold_xelements:
    forall (A B: Type) (f: B -> positive -> A -> B) m i v,
    xfold f i m v =
    List.fold_left (fun a p => f a (fst p) (snd p))
                   (xelements m i)
                   v.
  Proof.
    induction m; intros.
    simpl. auto.
    simpl. destruct o.
    rewrite fold_left_app. simpl. 
    rewrite IHm1. apply IHm2. 
    rewrite fold_left_app. simpl.
    rewrite IHm1. apply IHm2.
  Qed.

  Theorem fold_spec:
    forall (A B: Type) (f: B -> positive -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  Proof.
    intros. unfold fold, elements. apply xfold_xelements. 
  Qed.

  Section ORDER_WF.

  Inductive tree_struct :=
  | TSLeaf : tree_struct
  | TSNode : tree_struct -> tree_struct -> tree_struct.

  Fixpoint struct_of_tree (A : Type) (t : tree A) : tree_struct :=
    match t with
    | Leaf => TSLeaf
    | Node l _ r => TSNode (struct_of_tree l) (struct_of_tree r)
    end.

  Variable (A : Type).
  Variable (lt : A -> A -> Prop).
  Hypothesis (lt_wf : well_founded lt).

  Inductive tlt : tree A -> tree A -> Prop :=
  | tlt_left: forall l1 l2 o1 o2 r1 r2,
      tlt l1 l2 -> struct_of_tree r1 = struct_of_tree r2 ->
      tlt (Node l1 o1 r1) (Node l2 o2 r2)
  | tlt_el_none: forall l o r1 r2,
      struct_of_tree r1 = struct_of_tree r2 ->
      tlt (Node l None r1) (Node l (Some o) r2)
  | tlt_el: forall l o1 o2 r1 r2,
      lt o1 o2 -> struct_of_tree r1 = struct_of_tree r2 ->
      tlt (Node l (Some o1) r1) (Node l (Some o2) r2)
  | tlt_right: forall l o r1 r2, 
      tlt r1 r2 ->
      tlt (Node l o r1) (Node l o r2).

  Definition order (m1 m2 : t A) := tlt (proj1_sig m1) (proj1_sig m2).

  Lemma order_impl_same_struct:
    forall a b, tlt a b -> struct_of_tree a = struct_of_tree b.
  Proof.
    intros a b LT.
    induction LT; simpl; try f_equal; try assumption.
  Qed.

  Definition restricted_lt (s : tree_struct) (x y : tree A) : Prop :=
    struct_of_tree x = s /\ struct_of_tree y = s /\ tlt x y.

  Lemma leaf_no_order:
    forall t, ~ tlt t Leaf.
  Proof.
    intros tr OR. inversion OR.
  Qed.

  Lemma struct_leaf:
    forall t, struct_of_tree t = TSLeaf -> t = @Leaf A.
  Proof.
    intros tr STR. induction tr.
    reflexivity. 
    simpl in STR; discriminate.
  Qed.

  (* First, lift the relation to option and prove wf *)
  Inductive lt_opt : option A -> option A -> Prop :=
  | lt_opt_none : forall o, lt_opt None (Some o)
  | lt_opt_some : forall o1 o2, lt o1 o2 -> lt_opt (Some o1) (Some o2).
  
  Lemma wf_lt_opt_base: Acc lt_opt None.
  Proof.
    apply Acc_intro.
    intros y LT. inversion LT.
  Qed.

  Lemma wf_lt_opt: well_founded lt_opt.
  Proof.
    intro a.
    destruct a as [o|].
      set (IH o := Acc lt_opt (Some o)).
      apply (well_founded_ind lt_wf IH). unfold IH. clear IH o.
      intros o IH.
      apply Acc_intro.
      intros o' LT.
      destruct o' as [|o']; try (by apply wf_lt_opt_base).
      inversion LT. by apply IH.

    apply wf_lt_opt_base.
  Qed.

  (* Now prepare the leaf cases... *)
  Lemma restricted_wf_base:
    well_founded (restricted_lt TSLeaf). 
  Proof.
    intro a. apply Acc_intro.
    intros x RL. destruct RL as [_ [H LT]].
    rewrite struct_leaf in LT.
    apply leaf_no_order in LT. 
    contradiction.
    assumption.
  Qed.

  Lemma acc_restricted_node_leaf:
    forall s, Acc (restricted_lt s) Leaf.
  Proof.
    intro s. apply Acc_intro.
    intros x RLT.
    destruct RLT as [_ [_ LT]].
    inversion LT.
  Qed.
  
  (* Prove the restricted version of well-foundedness *)
  Lemma restricted_wf :
    forall s, well_founded (restricted_lt s). 
  Proof.
    induction s as [|ls l_wf rs r_wf]. 
    apply restricted_wf_base.
    
    (* Step case *)
    intro x. destruct x as [| xl xo xr]. 
      apply  acc_restricted_node_leaf.

    set (rt_lr := restricted_lt (TSNode ls rs)).
    set (rt_l := restricted_lt ls).
    set (rt_r := restricted_lt rs).

    (* Induction on the left subtree *)
    revert xo xr. 
    set (IH l := forall o r, Acc rt_lr (Node l o r)).
    apply (well_founded_ind l_wf IH). unfold IH. clear IH xl.
    intros xl IHl.

    (* Induction on the element *)
    set (IH o := forall r, Acc rt_lr (Node xl o r)).
    apply (well_founded_ind wf_lt_opt IH). unfold IH. clear IH.
    intros xo IHo.

    (* Induction on the right subtree *)
    set (IH r := Acc rt_lr (Node xl xo r)).
    apply (well_founded_ind r_wf IH). unfold IH. clear IH.
    intros xr IHr.

    (* The actual proof *)
    apply Acc_intro.
    intros y RLT. destruct y as [| yl yo yr].
      apply acc_restricted_node_leaf.
    destruct RLT as [Lstr [Rstr LT]].
    injection Lstr as Syr Syl.
    injection Rstr as Sxr Sxl.
    inversion LT as [l1 l2 o1 o2 r1 r2 TLTl Seq [El1 Eo1 Er1] [El2 Eo2 Er2]|
                     l o r1 r2 Seq [El1 Eo1 Er1] [El2 Eo2 Er2] | 
                     l o1 o2 r1 r2 LTo Seq [El1 Eo1 Er1] [El2 Eo2 Er2] |
                     l o r1 r2 TLTr [El1 Eo1 Er1] [El2 Eo2 Er2]].
    (* tlt_left case *)
    apply IHl. repeat split; try assumption.

    (* tlt_el_none case *)
    apply IHo. rewrite <- Eo2. apply lt_opt_none.

    (* tlt_el case *)
    apply IHo. rewrite <- Eo2. apply lt_opt_some.
    assumption.
    
    (* tlt_right case *)
    apply IHr. repeat split; try assumption.
  Qed.

  Lemma tlt_wf:
    well_founded tlt.
  Proof.
    intros a.  
    set (IH x := struct_of_tree x = struct_of_tree a -> Acc tlt x).
    apply (well_founded_ind (restricted_wf (struct_of_tree a)) IH).
    unfold IH. clear IH.
    intros x IH Seq. rewrite <- Seq in IH.
    apply Acc_intro.
    intros y LT. 
    apply IH; try repeat split; try apply order_impl_same_struct; assumption.
    reflexivity.
  Qed.

  Lemma order_wf:
    well_founded order.
  Proof.
    intros [a W]; revert W.
    set (IH a := forall W : wf a = true,
         Acc order (exist (fun x : tree A => wf x = true) a W)).
    apply (well_founded_ind tlt_wf IH); subst IH; simpl.
    by intros x IH; constructor; intros [y Wy] LT; apply IH. 
  Qed.

  Lemma order_set_lt:
    forall (tr : t A) (el : elt) (val nval : A),
      get el tr = Some val -> lt nval val ->
      order (set el nval tr) tr.
  Proof.
    intros [tr W]. unfold get, order; simpl; clear W. 
    induction tr as [| l IHl o r IHr].
    (* Tree cannot be leaf (otherwise get would fail) *)
    intros e v v' G. destruct e; simpl in G; discriminate.
    (* ... so the tree is a node ... *)
    intros e v v' G LT. destruct e as [e|e|]; simpl in G; simpl.
    apply tlt_right. exact (IHr _ _ _ G LT).
    apply tlt_left. exact (IHl _ _ _ G LT). reflexivity.
    rewrite G. apply tlt_el. assumption. reflexivity.
  Qed.

  End ORDER_WF.

End PTree.


Module ZTree <: TREE. (*: TREE with Definition elt := Z
                    with Definition elt_eq := Z_eq_dec. -- see comment above for PTree *)
  Definition elt := Z.
  Definition elt_eq := Z_eq_dec.
  Definition t := PTree.t.

  Definition index (z: Z): positive :=
    match z with
    | Z0 => xH
    | Zpos p => xO p
    | Zneg p => xI p
    end.

  Definition index_inverse (p: positive) : Z :=
    match p with
    | xH => Z0
    | xO p => Zpos p
    | xI p => Zneg p
    end.

  Lemma index_inv1 : forall x, index (index_inverse x) = x.
  Proof. by destruct x. Qed.

  Lemma index_inv2 : forall x, index_inverse (index x) = x.
  Proof. by destruct x. Qed.

  Lemma index_inj: forall x y, index x = index y -> x = y.
  Proof. by destruct x; destruct y; intros; clarify. Qed.

  Lemma index_inv_inj: forall x y, index_inverse x = index_inverse y -> x = y.
  Proof. by destruct x; destruct y; intros; clarify. Qed.

  Definition eq := PTree.eq. 
  Definition empty := PTree.empty.
  Definition get A z (m: t A) := PTree.get (index z) m. 
  Definition set A z v (m: t A) := PTree.set (index z) v m.
  Definition remove A z (m : t A) := PTree.remove (index z) m.

  Theorem gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Proof. by intros; apply PTree.gempty. Qed.

  Theorem gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof. intros; apply PTree.gss. Qed.

  Theorem gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof. intros; apply PTree.gso. intro M; apply index_inj in M; clarify. Qed.

  Theorem gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Proof. 
    intros; unfold get, set; rewrite PTree.gsspec.
    by destruct PTree.elt_eq as [EQ|]; [apply index_inj in EQ|]; destruct elt_eq; clarify. 
  Qed.

  Theorem gsident:
    forall (A: Type) (i: elt) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  Proof. by intros; apply PTree.gsident. Qed.

  Theorem grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Proof. by intros; apply PTree.grs. Qed.

  Theorem gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof. intros; apply PTree.gro; intro M; apply index_inj in M; clarify. Qed.

  Theorem grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof. 
    intros; unfold get, remove; rewrite PTree.grspec.
    by destruct PTree.elt_eq as [EQ|]; [apply index_inj in EQ|]; destruct elt_eq; clarify. 
  Qed.

  (** Extensional equality between trees. *)
  Definition beq := PTree.beq.
  Theorem beq_correct:
    forall (A: Type) (P: A -> A -> Prop) (cmp: A -> A -> bool),
    (forall (x y: A), cmp x y = true -> P x y) ->
    forall (t1 t2: t A), beq cmp t1 t2 = true ->
    forall (x: elt),
    match get x t1, get x t2 with
    | None, None => True
    | Some y1, Some y2 => P y1 y2
    | _, _ => False
    end.
  Proof.
    intros A P cmp E1 t1 t2 E2 x; unfold get.
    by apply (@PTree.beq_correct _ _ cmp). 
  Qed.

  Theorem ext: forall A (m1 m2: t A),
    (forall (x: elt), get x m1 = get x m2) -> m1 = m2.
  Proof.
    intros A m1 m2 E; apply PTree.ext; try done.
    by intros x; generalize (E (index_inverse x)); unfold get; rewrite index_inv1. 
  Qed.

  Theorem sss:
    forall (A: Type) (i: elt) (m: t A) (v v': A),
    set i v (set i v' m) = set i v m.
  Proof.
    intros; eapply PTree.sss.
  Qed.

  Theorem sso:
    forall (A: Type) (i j: elt) (m: t A) (v v': A),
    i <> j -> set i v (set j v' m) = set j v' (set i v m).
  Proof.
    intros; eapply PTree.sso.
    intro; destruct i; destruct j; clarify.
  Qed.

  (** Applying a function to all data of a tree. *)
  Definition map := fun (A B: Type) (f: elt -> A -> B) (t: t A) =>
    PTree.map (fun x => f (index_inverse x)) t.
  
  Theorem gmap:
    forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
  Proof. by intros; unfold get, map; rewrite PTree.gmap, index_inv2. Qed.

  (** Applying a function pairwise to all data of two trees. *)
  Definition combine :=  PTree.combine.

  Theorem gcombine:
    forall (A: Type) (f: option A -> option A -> option A),
    f None None = None ->
    forall (m1 m2: t A) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).
  Proof. by intros; apply PTree.gcombine. Qed.

  Theorem combine_commut:
    forall (A: Type) (f g: option A -> option A -> option A),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
  Proof. by intros; apply PTree.combine_commut. Qed.

  (** Enumerating the bindings of a tree. *)
  Definition elements (A : Type) (m : t A) := 
    List.map (fun p => (index_inverse (fst p), snd p)) (PTree.elements m).

  Theorem elements_correct:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Proof.
    intros. unfold elements.
    apply PTree.elements_correct in H.
    apply List.in_map with (f := (fun p : positive * A => (index_inverse (fst p), snd p))) in H.
    by simpl in H; rewrite index_inv2 in H.
  Qed.

  Theorem elements_complete:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Proof. 
    intros; unfold elements in *.
    apply PTree.elements_complete.
    apply List.in_map_iff in H; destruct H as [[? ?] [? ?]]; clarify.
    by rewrite index_inv1.
  Qed.

  Lemma NoDup_map1 : forall A B (f : A -> B) l, NoDup (List.map f l) -> NoDup l.
  Proof.
    induction l; intros H; [by apply NoDup_nil|]. 
    inv H. constructor; auto.
    by intro; elim H2; apply List.in_map.
  Qed.
   
  Theorem elements_keys_norepet:
    forall (A: Type) (m: t A), 
    NoDup (List.map (@fst elt A) (elements m)).
  Proof.
    intros; unfold elements.
    rewrite List.map_map; simpl.
    generalize (PTree.elements_keys_norepet m).
    generalize (PTree.elements m).
    intro l; induction l; simpl.
      by auto using NoDup_nil.
    intro X; inv X.
    constructor; auto.
    destruct a; simpl in *; intro Y; elim H1; generalize Y; clear.
    by induction l; simpl; clarify; intros [|]; auto using index_inv_inj. 
  Qed.

  (** Folding a function over all bindings of a tree. *)
  Definition fold (A B: Type) (f: B -> elt -> A -> B) (m: t A) (e: B) :=
    PTree.fold (fun e x => f e (index_inverse x)) m e.

  Theorem fold_spec:
    forall (A B: Type) (f: B -> elt -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  Proof.
    intros; unfold fold, elements.
    rewrite PTree.fold_spec.
    revert v; generalize (PTree.elements m); intro l; induction l; simpl; clarify.
  Qed.

  (** Lifting well_founded relation on elements to trees. *)
  Definition order := PTree.order. 
  Definition order_wf := PTree.order_wf.

  Theorem order_set_lt:
    forall (A : Type) (lt : A -> A -> Prop) (tr : t A) (el : elt)
           (val nval : A),
      get el tr = Some val -> lt nval val ->
      (order lt) (set el nval tr) tr.
  Proof. by intros until 0; apply PTree.order_set_lt. Qed.

End ZTree.



(** * An implementation of maps over type [positive] *)

Module PMap <: MAP.
  Definition elt := positive.
  Definition elt_eq := peq.

  Definition t (A : Type) : Type := (A * PTree.t A)%type.

  Definition eq: forall (A: Type), (forall (x y: A), {x=y} + {x<>y}) ->
                 forall (a b: t A), {a = b} + {a <> b}.
  Proof.
    intros. 
    generalize (PTree.eq X). intros. 
    decide equality.
  Qed.

  Definition init (A : Type) (x : A) :=
    (x, PTree.empty A).

  Definition get (A : Type) (i : positive) (m : t A) :=
    match PTree.get i (snd m) with
    | Some x => x
    | None => fst m
    end.

  Definition set (A : Type) (i : positive) (x : A) (m : t A) :=
    (fst m, PTree.set i x (snd m)).

  Theorem gi:
    forall (A: Type) (i: positive) (x: A), get i (init x) = x.
  Proof.
    intros. unfold init. unfold get. simpl. rewrite PTree.gempty. auto.
  Qed.

  Theorem gss:
    forall (A: Type) (i: positive) (x: A) (m: t A), get i (set i x m) = x.
  Proof.
    intros. unfold get. unfold set. simpl. rewrite PTree.gss. auto.
  Qed.

  Theorem gso:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. unfold get. unfold set. simpl. rewrite PTree.gso; auto.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    get i (set j x m) = if peq i j then x else get i m.
  Proof.
    intros. destruct (peq i j).
     rewrite e. apply gss. auto.
     apply gso. auto.
  Qed.

  Theorem gsident:
    forall (A: Type) (i j: positive) (m: t A),
    get j (set i (get i m) m) = get j m.
  Proof.
    intros. destruct (peq i j).
     rewrite e. rewrite gss. auto.
     rewrite gso; auto.
  Qed.

  Definition map (A B : Type) (f : A -> B) (m : t A) : t B :=
    (f (fst m), PTree.map (fun _ => f) (snd m)).

  Theorem gmap:
    forall (A B: Type) (f: A -> B) (i: positive) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold map. unfold get. simpl. rewrite PTree.gmap.
    unfold option_map. destruct (PTree.get i (snd m)); auto.
  Qed.

End PMap.

(** * An implementation of maps over any type that injects into type [positive] *)

Module Type INDEXED_TYPE.
  Variable t: Type.
  Variable index: t -> positive.
  Hypothesis index_inj: forall (x y: t), index x = index y -> x = y.
  Variable eq: forall (x y: t), {x = y} + {x <> y}.
End INDEXED_TYPE.

Module IMap(X: INDEXED_TYPE).

  Definition elt := X.t.
  Definition elt_eq := X.eq.
  Definition t : Type -> Type := PMap.t.
  Definition eq: forall (A: Type), (forall (x y: A), {x=y} + {x<>y}) ->
                 forall (a b: t A), {a = b} + {a <> b} := PMap.eq.
  Definition init (A: Type) (x: A) := PMap.init x.
  Definition get (A: Type) (i: X.t) (m: t A) := PMap.get (X.index i) m.
  Definition set (A: Type) (i: X.t) (v: A) (m: t A) := PMap.set (X.index i) v m.
  Definition map (A B: Type) (f: A -> B) (m: t A) : t B := PMap.map f m.

  Lemma gi:
    forall (A: Type) (x: A) (i: X.t), get i (init x) = x.
  Proof.
    intros. unfold get, init. apply PMap.gi. 
  Qed.

  Lemma gss:
    forall (A: Type) (i: X.t) (x: A) (m: t A), get i (set i x m) = x.
  Proof.
    intros. unfold get, set. apply PMap.gss.
  Qed.

  Lemma gso:
    forall (A: Type) (i j: X.t) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. unfold get, set. apply PMap.gso. 
    red. intro. apply H. apply X.index_inj; auto. 
  Qed.

  Lemma gsspec:
    forall (A: Type) (i j: X.t) (x: A) (m: t A),
    get i (set j x m) = if X.eq i j then x else get i m.
  Proof.
    intros. unfold get, set. 
    rewrite PMap.gsspec.
    case (X.eq i j); intro.
    subst j. rewrite peq_true. reflexivity.
    rewrite peq_false. reflexivity. 
    red; intro. elim n. apply X.index_inj; auto.
  Qed.

  Lemma gmap:
    forall (A B: Type) (f: A -> B) (i: X.t) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold map, get. apply PMap.gmap. 
  Qed.

End IMap.

Module ZIndexed.
  Definition t := Z.
  Definition index (z: Z): positive :=
    match z with
    | Z0 => xH
    | Zpos p => xO p
    | Zneg p => xI p
    end.
  Lemma index_inj: forall (x y: Z), index x = index y -> x = y.
  Proof.
    unfold index; destruct x; destruct y; intros;
    try discriminate; try reflexivity.
    congruence.
    congruence.
  Qed.
  Definition eq := zeq.
End ZIndexed.

Module ZMap := IMap(ZIndexed).

Module NIndexed.
  Definition t := N.
  Definition index (n: N): positive :=
    match n with
    | N0 => xH
    | Npos p => xO p
    end.
  Lemma index_inj: forall (x y: N), index x = index y -> x = y.
  Proof.
    unfold index; destruct x; destruct y; intros;
    try discriminate; try reflexivity.
    congruence.
  Qed.
  Lemma eq: forall (x y: N), {x = y} + {x <> y}.
  Proof.
    decide equality. apply peq.
  Qed.
End NIndexed.

Module NMap := IMap(NIndexed).

(** * An implementation of maps over any type with decidable equality *)

Module Type EQUALITY_TYPE.
  Variable t: Type.
  Variable eq: forall (x y: t), {x = y} + {x <> y}.
End EQUALITY_TYPE.

Module EMap(X: EQUALITY_TYPE) <: MAP.

  Definition elt := X.t.
  Definition elt_eq := X.eq.
  Definition t (A: Type) := X.t -> A.
  Definition init (A: Type) (v: A) := fun (_: X.t) => v.
  Definition get (A: Type) (x: X.t) (m: t A) := m x.
  Definition set (A: Type) (x: X.t) (v: A) (m: t A) :=
    fun (y: X.t) => if X.eq y x then v else m y.
  Lemma gi:
    forall (A: Type) (i: elt) (x: A), init x i = x.
  Proof.
    intros. reflexivity.
  Qed.
  Lemma gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), (set i x m) i = x.
  Proof.
    intros. unfold set. case (X.eq i i); intro.
    reflexivity. tauto.
  Qed.
  Lemma gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> (set j x m) i = m i.
  Proof.
    intros. unfold set. case (X.eq i j); intro.
    congruence. reflexivity.
  Qed.
  Lemma gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Proof.
    intros. unfold get, set, elt_eq. reflexivity.
  Qed.
  Lemma gsident:
    forall (A: Type) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
  Proof.
    intros. unfold get, set. case (X.eq j i); intro.
    congruence. reflexivity.
  Qed.
  Definition map (A B: Type) (f: A -> B) (m: t A) :=
    fun (x: X.t) => f(m x).
  Lemma gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold get, map. reflexivity.
  Qed.
End EMap.

(** * Additional properties over trees *)

Module Tree_Properties(T: TREE).

(** An induction principle over [fold]. *)

Section TREE_FOLD_IND.

Variables V A: Type.
Variable f: A -> T.elt -> V -> A.
Variable P: T.t V -> A -> Prop.
Variable init: A.
Variable m_final: T.t V.

Hypothesis P_compat:
  forall m m' a,
  (forall x, T.get x m = T.get x m') ->
  P m a -> P m' a.

Hypothesis H_base: 
  P (T.empty _) init.

Hypothesis H_rec:
  forall m a k v,
  T.get k m = None -> T.get k m_final = Some v -> P m a -> P (T.set k v m) (f a k v).

Definition f' (a: A) (p : T.elt * V) := f a (fst p) (snd p).

Definition P' (l: list (T.elt * V)) (a: A) : Prop :=
  forall m, list_equiv l (T.elements m) -> P m a.

Remark H_base':
  P' nil init.
Proof.
  red; intros. apply P_compat with (T.empty _); auto.
  intros. rewrite T.gempty. symmetry. case_eq (T.get x m); intros; auto.
  assert (In (x, v) nil). rewrite (H (x, v)). apply T.elements_correct. auto.
  contradiction.
Qed.

Remark H_rec':
  forall k v l a,
  ~In k (List.map (@fst T.elt V) l) ->
  In (k, v) (T.elements m_final) ->
  P' l a ->
  P' (l ++ (k, v) :: nil) (f a k v).
Proof.
  unfold P'; intros.  
  set (m0 := T.remove k m). 
  apply P_compat with (T.set k v m0).
    intros. unfold m0. rewrite T.gsspec. destruct (T.elt_eq x k).
    symmetry. apply T.elements_complete. rewrite <- (H2 (x, v)).
    apply in_or_app. simpl. intuition congruence.
    apply T.gro. auto.
  apply H_rec. unfold m0. apply T.grs. apply T.elements_complete. auto. 
  apply H1. red. intros [k' v']. 
  split; intros. 
  apply T.elements_correct. unfold m0. rewrite T.gro. apply T.elements_complete. 
  rewrite <- (H2 (k', v')). apply in_or_app. auto. 
  red; intro; subst k'. elim H. change k with (fst (k, v')). apply in_map. auto.
  assert (T.get k' m0 = Some v'). apply T.elements_complete. auto.
  unfold m0 in H4. rewrite T.grspec in H4. destruct (T.elt_eq k' k). congruence.
  assert (In (k', v') (T.elements m)). apply T.elements_correct; auto.
  rewrite <- (H2 (k', v')) in H5. destruct (in_app_or _ _ _ H5). auto. 
  simpl in H6. intuition congruence.
Qed.

Lemma fold_rec_aux:
  forall l1 l2 a,
  list_equiv (l2 ++ l1) (T.elements m_final) ->
  list_disjoint (List.map (@fst T.elt V) l1) (List.map (@fst T.elt V) l2) ->
  NoDup (List.map (@fst T.elt V) l1) ->
  P' l2 a -> P' (l2 ++ l1) (List.fold_left f' l1 a).
Proof.
  induction l1; intros; simpl.
  rewrite <- List.app_nil_end. auto.
  destruct a as [k v]; simpl in *. inv H1. 
  change ((k, v) :: l1) with (((k, v) :: nil) ++ l1). rewrite <- List.app_ass. apply IHl1.
  rewrite app_ass. auto.
  red; intros. rewrite map_app in H3. destruct (in_app_or _ _ _ H3). apply H0; auto with coqlib. 
  simpl in H4. intuition congruence.
  auto.
  unfold f'. simpl. apply H_rec'; auto. eapply list_disjoint_notin; eauto with coqlib.
  rewrite <- (H (k, v)). apply in_or_app. simpl. auto.
Qed.

Theorem fold_rec:
  P m_final (T.fold f m_final init).
Proof.
  intros. rewrite T.fold_spec. fold f'.
  assert (P' (nil ++ T.elements m_final) (List.fold_left f' (T.elements m_final) init)).
    apply fold_rec_aux.
    simpl. red; intros; tauto.
    simpl. red; intros. elim H0.
    apply T.elements_keys_norepet. 
    apply H_base'. 
  simpl in H. red in H. apply H. red; intros. tauto.
Qed.

End TREE_FOLD_IND.

End Tree_Properties.

Module PTree_Properties := Tree_Properties(PTree).

(** * Useful notations *)

Notation "a ! b" := (PTree.get b a) (at level 1).
Notation "a !! b" := (PMap.get b a) (at level 1).
Notation "a ! b <- c" := (PTree.set b c a) (at level 1, b at next level).

Module IndexedPair(X Y: INDEXED_TYPE).
  Definition t := (X.t * Y.t)%type.

  Fixpoint indexp (t1 t2 : positive) : positive :=
    match t1, t2 with
    | xH   , xH    => xH
    | xH   , xO p2 => xI(xI(xO(p2)))
    | xH   , xI p2 => xI(xI(xI(p2)))
    | xO p1, xH    => xI(xO(xO(p1)))
    | xO p1, xO p2 => xO(xO(xO(indexp p1 p2)))
    | xO p1, xI p2 => xO(xO(xI(indexp p1 p2)))
    | xI p1, xH    => xI(xO(xI(p1)))
    | xI p1, xO p2 => xO(xI(xO(indexp p1 p2)))
    | xI p1, xI p2 => xO(xI(xI(indexp p1 p2)))
    end.

  Lemma indexp_inj: 
    forall (p1 p2 q1 q2: positive), 
      indexp p1 p2 = indexp q1 q2 -> p1 = q1 /\ p2 = q2.
  Proof.
    intro p1. 
    induction p1 as [p IH|p IH|];
      intros p2 q1 q2;
      destruct p2; destruct q1; destruct q2; 
      intro H; try discriminate; try reflexivity; simpl in H;
      try injection H as H1; try apply IH in H1;
      try destruct H1; try split; try congruence.
  Qed.
      
  Definition index (p: X.t * Y.t): positive :=
    match p with (a, b) => indexp (X.index a) (Y.index b) end. 

  Lemma index_inj: forall (x y: X.t * Y.t), index x = index y -> x = y.
  Proof.
    intros x y. destruct x. destruct y. unfold index.
    intro H. apply indexp_inj in H. destruct H as [H1 H2].
    apply X.index_inj in H1. apply Y.index_inj in H2.
    congruence.
  Qed.
  Lemma eq: forall (x y: X.t * Y.t), {x = y} + {x <> y}.
  Proof.
    decide equality; try apply Y.eq; try apply X.eq.
  Qed.
End IndexedPair.

Module ZZIndexed := IndexedPair(ZIndexed)(ZIndexed).

Module ZZMap := IMap(ZZIndexed).

(* $Id: Maps.v,v 1.12.4.4 2006/01/07 11:46:55 xleroy Exp $ *)
