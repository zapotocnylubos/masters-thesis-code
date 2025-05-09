Require Import SLC.Lib.
Require Import SLC.PropBool.
Require Import SLC.Booleans.
Require Import SLC.Sets.
Require Import SLC.Tactics.
Require Import SLC.Ints.
Require Import SLC.Unfolding.

Require Import ZArith.
Require Import Coq.Strings.String.
From Equations Require Import Equations.

Set Program Mode.

Opaque set_elem_of.
Opaque set_union.
Opaque set_intersection.
Opaque set_subset.
Opaque set_empty.
Opaque set_singleton.
Opaque set_difference.

Ltac t19 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t20 :=
  t19 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t20.


Inductive LinkedList :=
| Cons_construct: Z -> (LinkedList -> LinkedList)
| Nil_construct: LinkedList.

Definition isCons (src: LinkedList) : bool :=
match src with
| Cons_construct _ _ => true
| _ => false
end.

Fail Next Obligation.

#[export] Hint Unfold  isCons: recognizers.

Definition isNil (src: LinkedList) : bool :=
match src with
| Nil_construct => true
| _ => false
end.

Fail Next Obligation.

#[export] Hint Unfold  isNil: recognizers.

Lemma Cons_exists: (forall self12: LinkedList, ((true = isCons self12)) <-> ((exists tmp7: LinkedList, exists tmp6: Z, (Cons_construct tmp6 tmp7 = self12)))).
Proof.
	repeat t20 || eauto.
Qed.

Lemma Nil_exists: (forall self13: LinkedList, ((true = isNil self13)) <-> (((Nil_construct = self13)))).
Proof.
	repeat t20 || eauto.
Qed.

Definition Cons_type : Type :=
{src: LinkedList | (isCons src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Cons_type: refinements.

Definition Nil_type : Type :=
{src: LinkedList | (isNil src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Nil_type: refinements.

Ltac LinkedList_tactic3 := match goal with
	| [ H6: (true = isCons ?self14) |- _ ] =>
			poseNew (Mark (self14) "Cons_exists");pose proof ((proj1 (Cons_exists _ _)) H6)
	| [ H6: (isCons ?self14 = true) |- _ ] =>
			poseNew (Mark (self14) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H6))
	| [ H7: (true = isNil ?self15) |- _ ] =>
			poseNew (Mark (self15) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H7)
	| [ H7: (isNil ?self15 = true) |- _ ] =>
			poseNew (Mark (self15) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H7))
	| _ => idtac
end.

Ltac t21 :=
  t_base ||
  LinkedList_tactic3 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t22 :=
  t21 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t22.

Definition head (src: Cons_type) : Z :=
match src with
| Cons_construct f0 f1 => f0
| _ => let contradiction: False := _ in match contradiction with end
end.

Fail Next Obligation.

Definition tail (src: Cons_type) : LinkedList :=
match src with
| Cons_construct f0 f1 => f1
| _ => let contradiction: False := _ in match contradiction with end
end.

Fail Next Obligation.


Inductive Object :=
| Open_construct: Z -> Object.


Definition value (src: Object) : Z :=
match src with
| Open_construct f0 => f0
end.

Fail Next Obligation.


(***********************
  Start of NilRequireForDefault
 ***********************)

Definition NilRequireForDefault : unit :=
let unused := (Nil_construct) in (magic unit).

Fail Next Obligation.

#[export] Hint Unfold NilRequireForDefault: definitions.

(***********************
  End of NilRequireForDefault
 ***********************)
