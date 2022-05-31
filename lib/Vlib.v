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
(*                   Viktor's lemmas & tactics                         *)
(*                                                                     *)
(* *********************************************************************)

(** This file collects a number of basic lemmas and tactics, mostly
    inspired from ss-reflect. *)

Require Import Bool.
Require Import List.
Set Implicit Arguments.

(** Adaptation of the "done" tactic from ss-reflect *)

(*Ltac done := trivial; hnf; intros; solve
  [ repeat (first [solve [trivial | apply sym_equal; trivial]
                   | discriminate | contradiction | split])
  | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].*)

Ltac basic_done_internal := 
  solve [trivial | apply sym_equal; trivial | discriminate | contradiction].

Ltac done := trivial; hnf; intros;
  solve [try basic_done_internal; split; 
         try basic_done_internal; split; 
         try basic_done_internal; split; 
         try basic_done_internal; split; 
         try basic_done_internal; split; basic_done_internal
    | match goal with H : ~ _ |- _ => solve [case H; trivial] end].


(** A variant that performs "eassumption". *)

Ltac edone := try eassumption; trivial; hnf; intros;
  solve [try eassumption; try basic_done_internal; split; 
         try eassumption; try basic_done_internal; split; 
         try eassumption; try basic_done_internal; split; 
         try eassumption; try basic_done_internal; split; 
         try eassumption; try basic_done_internal; split;
         try eassumption; basic_done_internal
    | match goal with H : ~ _ |- _ => solve [case H; trivial] end].

Tactic Notation "by" tactic(tac) := (tac; done).
Tactic Notation "eby" tactic(tac) := (tac; edone).

(** Lightweight case tactics *)

Tactic Notation "-" tactic(c) :=
  first [
    assert (WithinCaseM := True); move WithinCaseM at top
  | fail 1 "because we are working on a different case." ]; c.

Tactic Notation "+" tactic(c) :=
  first [
    assert (WithinCaseP := True); move WithinCaseP at top
  | fail 1 "because we are working on a different case." ]; c.

(** Protect the goal from manipulation *)

Ltac with_protect_goal tac :=
  let X := fresh in
  match goal with
  | [|- ?P ] => set (X := P)
  end;
  tac;
  subst X.

Ltac complaining_injection f H :=
  with_protect_goal
    ltac:(
      injection H;
      (lazymatch goal with | [ |- f _ = f _ -> _] => fail | _ => idtac end);
      clear H; intros).

(** Perform injections & discriminations on all hypotheses *)

Ltac clarify :=
  try subst;
  repeat match goal with
    | [ H : ?f _             = ?f _             |- _ ] => complaining_injection f H; try subst
    | [ H : ?f _ _           = ?f _ _           |- _ ] => complaining_injection f H; try subst
    | [ H : ?f _ _ _         = ?f _ _ _         |- _ ] => complaining_injection f H; try subst
    | [ H : ?f _ _ _ _       = ?f _ _ _ _       |- _ ] => complaining_injection f H; try subst
    | [ H : ?f _ _ _ _ _     = ?f _ _ _ _ _     |- _ ] => complaining_injection f H; try subst
    | [ H : ?f _ _ _ _ _ _   = ?f _ _ _ _ _ _   |- _ ] => complaining_injection f H; try subst
    | [ H : ?f _ _ _ _ _ _ _ = ?f _ _ _ _ _ _ _ |- _ ] => complaining_injection f H; try subst
  end; try done.

Ltac clarify' :=
  clarify;
  repeat match goal with
    | H1: ?x = Some _, H2: ?x = None   |- _ => rewrite H2 in H1; clarify
    | H1: ?x = Some _, H2: ?x = Some _ |- _ => rewrite H2 in H1; clarify
    | H1: ?x = _ :: _, H2: ?x = nil    |- _ => rewrite H2 in H1; clarify
    | H1: ?x = _ :: _, H2: ?x = _ :: _ |- _ => rewrite H2 in H1; clarify
  end.

Ltac des :=
  repeat match goal with
    | H : exists x, _ |- _ => destruct H as [x H] (* try to preserve name if possible *)
    | H : exists x, _ |- _ => destruct H as [? H]
    | H : _ /\ _ |- _ => destruct H
    | H : _ \/ _ |- _ => destruct H
  end.

(** Kill simple goals that require up to two econstructor calls. *)

Ltac vauto := (clarify; try (econstructor (solve [edone | econstructor edone ]))).

(** Check that the hypothesis [id] is defined. This is useful to make sure that an [assert]
    has been completely finished. *)
    
Ltac end_assert id := 
  let m := fresh in 
  pose (m := refl_equal id); clear m.

(** * Boolean reflection: definitions & lemmas ported from ssrbool.v *)


(** Coersion of bools into Prop *)
Coercion is_true (b : bool) : Prop := b = true.

(* Hints for auto *)
Lemma is_true_true : true.               Proof. done. Qed.
Lemma not_false_is_true : ~ false.       Proof. done. Qed.
Hint Resolve is_true_true not_false_is_true.


(** Negation lemmas *)
Section NegationLemmas.

  Variables (b c : bool).

  Lemma negbT : b = false -> negb b.       Proof. by case b. Qed.
  Lemma negbTE: negb b -> b = false.       Proof. by case b. Qed.
  Lemma negbF : b -> negb b = false.       Proof. by case b. Qed.
  Lemma negbFE: negb b = false -> b.       Proof. by case b. Qed.
  Lemma negbNE: negb (negb b) -> b.        Proof. by case b. Qed.

  Lemma negbLR : b = negb c -> negb b = c. Proof. by case c; intro X; rewrite X. Qed.

  Lemma negbRL : negb b = c -> b = negb c. Proof. by case b; intro X; rewrite <- X. Qed.

  Lemma contra : (c -> b) -> negb b -> negb c.
  Proof. by case b; case c. Qed.

End NegationLemmas.

(** Lemmas for ifs, which allow reasoning about the condition without 
    repeating it inside the proof. *)
Section BoolIf.

Variables (A B : Type) (x : A) (f : A -> B) (b : bool) (vT vF : A).

CoInductive if_spec : A -> bool -> Set :=
  | IfSpecTrue  : b         -> if_spec vT true
  | IfSpecFalse : b = false -> if_spec vF false.

Lemma ifP : if_spec (if b then vT else vF) b.
Proof. by case_eq b; constructor. Qed.

Lemma if_same : (if b then vT else vT) = vT.
Proof. by case b. Qed.

Lemma if_neg : (if negb b then vT else vF) = if b then vF else vT.
Proof. by case b. Qed.

Lemma fun_if : f (if b then vT else vF) = if b then f vT else f vF.
Proof. by case b. Qed.

Lemma if_arg : forall fT fF : A -> B,
  (if b then fT else fF) x = if b then fT x else fF x.
Proof. by case b. Qed.

End BoolIf.

(** The reflection predicate *)
Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

(** Internal reflection lemmas *)
Section ReflectCore.

Variables (P Q : Prop) (b c : bool).

Hypothesis Hb : reflect P b.

Lemma introNTF : (if c then ~ P else P) -> negb b = c.
Proof. by case c; case Hb. Qed.

Lemma introTF : (if c then P else ~ P) -> b = c.
Proof. by case c; case Hb. Qed.

Lemma elimNTF : negb b = c -> if c then ~ P else P.
Proof. by intro X; rewrite <- X; case Hb. Qed.

Lemma elimTF : b = c -> if c then P else ~ P.
Proof. by intro X; rewrite <- X; case Hb. Qed.

Lemma equivPif : (Q -> P) -> (P -> Q) -> if b then Q else ~ Q.
Proof. by case Hb; auto. Qed.

Lemma xorPif : Q \/ P -> ~ (Q /\ P) -> if b then ~ Q else Q.
Proof. by case Hb; [intros ? _ H ? | intros ? H _]; case H. Qed.

End ReflectCore.

(** Internal negated reflection lemmas *)
Section ReflectNegCore.

Variables (P Q : Prop) (b c : bool).
Hypothesis Hb : reflect P (negb b).

Lemma introTFn : (if c then ~ P else P) -> b = c.
Proof. by intro X; apply (introNTF _ Hb) in X; rewrite <- X; case b. Qed.

Lemma elimTFn : b = c -> if c then ~ P else P.
Proof. by intro X; rewrite <- X; apply (elimNTF Hb); case b. Qed.

Lemma equivPifn : (Q -> P) -> (P -> Q) -> if b then ~ Q else Q.
Proof. by rewrite <- if_neg; apply equivPif. Qed.

Lemma xorPifn : Q \/ P -> ~ (Q /\ P) -> if b then Q else ~ Q.
Proof. by rewrite <- if_neg; apply xorPif. Qed.

End ReflectNegCore.


(* User-oriented reflection lemmas *)
Section Reflect.

Variables (P Q : Prop) (b b' c : bool).
Hypotheses (Pb : reflect P b) (Pb' : reflect P (negb b')).

Lemma introT  : P -> b.              Proof. by apply (introTF true). Qed.
Lemma introF  : ~ P -> b = false.    Proof. by apply (introTF false). Qed.
Lemma introN  : ~ P -> negb b.       Proof. by apply (introNTF true). Qed.
Lemma introNf : P -> negb b = false. Proof. by apply (introNTF false). Qed.
Lemma introTn : ~ P -> b'.           Proof. by apply (introTFn _ true). Qed.
Lemma introFn : P -> b' = false.     Proof. by apply (introTFn _ false). Qed.

Lemma elimT  : b -> P.             Proof. by apply (@elimTF _ _ true). Qed.
Lemma elimF  : b = false -> ~ P.   Proof. by apply (@elimTF  _ _ false). Qed.
Lemma elimN  : negb b -> ~P.         Proof. by apply (@elimNTF _ _ true). Qed.
Lemma elimNf : negb b = false -> P.  Proof. by apply (@elimNTF _ _ false). Qed.
Lemma elimTn : b' -> ~ P.          Proof. by apply (@elimTFn _ _ true). Qed.
Lemma elimFn : b' = false -> P.    Proof. by apply (@elimTFn _ _ false). Qed.

Lemma introP : (b -> Q) -> (negb b -> ~ Q) -> reflect Q b.
Proof. by case b; constructor; auto. Qed.

Lemma iffP : (P -> Q) -> (Q -> P) -> reflect Q b.
Proof. by case Pb; constructor; auto. Qed.

Lemma appP : reflect Q b -> P -> Q.
Proof. by intro Qb; intro X; apply introT in X; revert X; case Qb. Qed.

Lemma sameP : reflect P c -> b = c.
Proof. intro X; case X; [exact introT | exact introF]. Qed.

Lemma decPcases : if b then P else ~ P. Proof. by case Pb. Qed.

Definition decP : {P} + {~ P}. by generalize decPcases; case b; [left | right]. Defined.

End Reflect.

(* Allow the direct application of a reflection lemma to a boolean assertion.  *)
Coercion elimT : reflect >-> Funclass.


Section ReflectConnectives.

Variable b1 b2 b3 b4 b5 : bool.

Lemma idP : reflect b1 b1.
Proof. by case b1; constructor. Qed.

Lemma idPn : reflect (negb b1) (negb b1).
Proof. by case b1; constructor. Qed.

Lemma negP : reflect (~ b1) (negb b1).
Proof. by case b1; constructor; auto. Qed.

Lemma negPn : reflect b1 (negb (negb b1)).
Proof. by case b1; constructor. Qed.

Lemma negPf : reflect (b1 = false) (negb b1).
Proof. by case b1; constructor. Qed.

Lemma andP : reflect (b1 /\ b2) (b1 && b2).
Proof. by case b1; case b2; constructor; try done; intro X; case X. Qed.

Lemma orP : reflect (b1 \/ b2) (b1 || b2).
Proof. by case b1; case b2; constructor; auto; intro X; case X. Qed.

Lemma nandP : reflect (negb b1 \/ negb b2) (negb (b1 && b2)).
Proof. by case b1; case b2; constructor; auto; intro X; case X; auto. Qed.

Lemma norP : reflect (negb b1 /\ negb b2) (negb (b1 || b2)).
Proof. by case b1; case b2; constructor; auto; intro X; case X; auto. Qed.

End ReflectConnectives.

Implicit Arguments idP [b1].
Implicit Arguments idPn [b1].
Implicit Arguments negP [b1].
Implicit Arguments negPn [b1].
Implicit Arguments negPf [b1].
Implicit Arguments andP [b1 b2].
Implicit Arguments orP [b1 b2].
Implicit Arguments nandP [b1 b2].
Implicit Arguments norP [b1 b2].


(* Shorter, more systematic names for the boolean connectives laws.       *)

Lemma andTb : forall x, true && x = x.       Proof. done. Qed.
Lemma andFb : forall x, false && x = false.  Proof. done. Qed.
Lemma andbT : forall x, x && true = x.       Proof. by intro X; case X. Qed.
Lemma andbF : forall x, x && false = false.  Proof. by intro X; case X. Qed.
Lemma andbb : forall x, x && x = x.          Proof. by intro X; case X. Qed.

Lemma andbC : forall x y, x && y = y && x.
Proof. by intros x y; case x; case y. Qed.
Lemma andbA : forall x y z, x && (y && z) = x && y && z.       
Proof. by intros x y z; case x; case y; case z. Qed.
Lemma andbCA : forall x y z, x && (y && z) = y && (x && z).
Proof. by intros x y z; case x; case y; case z. Qed.
Lemma andbAC : forall x y z, x && y && z = x && z && y.
Proof. by intros x y z; case x; case y; case z. Qed.

Lemma orTb : forall x, true || x = true.   Proof. done. Qed.
Lemma orFb : forall x, false || x = x.     Proof. done. Qed.
Lemma orbT : forall x, x || true = true.   Proof. by intro x; case x. Qed.
Lemma orbF : forall x, x || false = x.     Proof. by intro x; case x. Qed.
Lemma orbb : forall x, x || x = x.         Proof. by intro x; case x. Qed.

Lemma orbC : forall x y, x || y = y || x.
Proof. by intros x y; case x; case y. Qed.
Lemma orbA : forall x y z, x || (y || z) = x || y || z.       
Proof. by intros x y z; case x; case y; case z. Qed.
Lemma orbCA : forall x y z, x || (y || z) = y || (x || z).
Proof. by intros x y z; case x; case y; case z. Qed.
Lemma orbAC : forall x y z, x || y || z = x || z || y.
Proof. by intros x y z; case x; case y; case z. Qed.

Lemma andbN : forall b, b && negb b = false. Proof. by intro x; case x. Qed.
Lemma andNb : forall b, negb b && b = false. Proof. by intro x; case x. Qed.
Lemma orbN : forall b, b || negb b = true.   Proof. by intro x; case x. Qed.
Lemma orNb : forall b, negb b || b = true.   Proof. by intro x; case x. Qed.

Lemma andb_orl : forall x y z, (x || y) && z = x && z || y && z.
Proof. by intros x y z; case x; case y; case z. Qed.

Lemma andb_orr : forall x y z, x && (y || z) = x && y || x && z.
Proof. by intros x y z; case x; case y; case z. Qed.

Lemma orb_andl : forall x y z, (x && y) || z = (x || z) && (y || z).
Proof. by intros x y z; case x; case y; case z. Qed.

Lemma orb_andr : forall x y z, x || (y && z) = (x || y) && (x || z).
Proof. by intros x y z; case x; case y; case z. Qed.

Lemma negb_and : forall b1 b2, negb (b1 && b2) = negb b1 || negb b2.
Proof. by intros x y; case x; case y. Qed.

Lemma negb_or : forall b1 b2, negb (b1 || b2) = negb b1 && negb b2.
Proof. by intros x y; case x; case y. Qed.

(* Pseudo-cancellation -- i.e, absorbtion *)

Lemma andbK : forall b1 b2, b1 && b2 || b1 = b1.  Proof. by intros x y; case x; case y. Qed.
Lemma andKb : forall b1 b2, b1 || b2 && b1 = b1.  Proof. by intros x y; case x; case y. Qed.
Lemma orbK : forall b1 b2, (b1 || b2) && b1 = b1. Proof. by intros x y; case x; case y. Qed.
Lemma orKb : forall b1 b2, b1 && (b2 || b1) = b1. Proof. by intros x y; case x; case y. Qed.



(** * Three-valued Logic *) 

Inductive bool3 := b3_true | b3_false | b3_unknown.

Lemma bool3_dec_eq (x y: bool): { x = y } + { x <> y }.
Proof. decide equality. Qed. 

Definition negb3 (b:bool3) : bool3 :=
  match b with 
   | b3_true    => b3_false
   | b3_false   => b3_true
   | b3_unknown => b3_unknown
  end.

Definition andb3 (b1 b2:bool3) : bool3 := 
  match b1, b2 with 
    | b3_true, _    => b2 
    | b3_false, _   => b3_false
    | b3_unknown, b3_false => b3_false
    | b3_unknown, _ => b3_unknown
  end.

Definition orb3 (b1 b2:bool3) : bool3 :=
  match b1, b2 with 
    | b3_true, _    => b3_true 
    | b3_false, _   => b2
    | b3_unknown, b3_true => b3_true
    | b3_unknown, _ => b3_unknown
  end.

Definition bool2bool3 (b: bool) : bool3 :=
   if b then b3_true else b3_false.

Definition b3_moredef (b1 : bool3) (b2: bool) : bool :=
  match b1 with
    | b3_true    => b2
    | b3_false   => negb b2
    | b3_unknown => false
  end.

Lemma andb3T: forall b, andb3 b b3_true = b.           Proof. by destruct b. Qed.
Lemma andb3F: forall b, andb3 b b3_false = b3_false.   Proof. by destruct b. Qed.

Lemma orb3T: forall b, orb3 b b3_true = b3_true.       Proof. by destruct b. Qed.
Lemma orb3F: forall b, orb3 b b3_false = b.            Proof. by destruct b. Qed.

Lemma negb3P: forall x, bool2bool3 (negb x) = negb3 (bool2bool3 x).
Proof. by destruct x. Qed.

Lemma andb3P: forall x y, bool2bool3 (andb x y) = andb3 (bool2bool3 x) (bool2bool3 y).
Proof. by intros [] []. Qed.

Lemma orb3P: forall x y, bool2bool3 (orb x y) = orb3 (bool2bool3 x) (bool2bool3 y).
Proof. by intros [] []. Qed.

Lemma negb3_neg : forall x, negb3 (negb3 x) = x.
Proof. by intros []. Qed.

Lemma negb3_and : forall b1 b2, negb3 (andb3 b1 b2) = orb3 (negb3 b1) (negb3 b2).
Proof. by intros [] []. Qed.

Lemma negb3_or : forall b1 b2, negb3 (orb3 b1 b2) = andb3 (negb3 b1) (negb3 b2).
Proof. by intros [] []. Qed.

Ltac b3_simps := 
   repeat first [ rewrite negb3_neg | rewrite negb3_and | rewrite negb3_or
                | rewrite negb3P | rewrite andb3P | rewrite orb3P ].

