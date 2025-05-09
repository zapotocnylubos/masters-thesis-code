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

Ltac t64 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t65 :=
  t64 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t65.


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

Lemma Cons_exists: (forall self32: LinkedList, ((true = isCons self32)) <-> ((exists tmp17: LinkedList, exists tmp16: Z, (Cons_construct tmp16 tmp17 = self32)))).
Proof.
	repeat t65 || eauto.
Qed.

Lemma Nil_exists: (forall self33: LinkedList, ((true = isNil self33)) <-> (((Nil_construct = self33)))).
Proof.
	repeat t65 || eauto.
Qed.

Definition Cons_type : Type :=
{src: LinkedList | (isCons src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Cons_type: refinements.

Definition Nil_type : Type :=
{src: LinkedList | (isNil src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Nil_type: refinements.

Ltac LinkedList_tactic8 := match goal with
	| [ H16: (true = isCons ?self34) |- _ ] =>
			poseNew (Mark (self34) "Cons_exists");pose proof ((proj1 (Cons_exists _ _)) H16)
	| [ H16: (isCons ?self34 = true) |- _ ] =>
			poseNew (Mark (self34) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H16))
	| [ H17: (true = isNil ?self35) |- _ ] =>
			poseNew (Mark (self35) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H17)
	| [ H17: (isNil ?self35 = true) |- _ ] =>
			poseNew (Mark (self35) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H17))
	| _ => idtac
end.

Ltac t66 :=
  t_base ||
  LinkedList_tactic8 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t67 :=
  t66 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t67.

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
  Start of empty
 ***********************)

Definition empty (T: Type) : set (T) :=
@set_empty T.

Fail Next Obligation.

#[export] Hint Unfold empty: definitions.

(***********************
  End of empty
 ***********************)
