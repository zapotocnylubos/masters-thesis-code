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

Ltac t1 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t2 :=
  t1 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t2.


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

Lemma Cons_exists: (forall self: LinkedList, ((true = isCons self)) <-> ((exists tmp1: LinkedList, exists tmp: Z, (Cons_construct tmp tmp1 = self)))).
Proof.
	repeat t2 || eauto.
Qed.

Lemma Nil_exists: (forall self1: LinkedList, ((true = isNil self1)) <-> (((Nil_construct = self1)))).
Proof.
	repeat t2 || eauto.
Qed.

Definition Cons_type : Type :=
{src: LinkedList | (isCons src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Cons_type: refinements.

Definition Nil_type : Type :=
{src: LinkedList | (isNil src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Nil_type: refinements.

Ltac LinkedList_tactic := match goal with
	| [ H: (true = isCons ?self2) |- _ ] =>
			poseNew (Mark (self2) "Cons_exists");pose proof ((proj1 (Cons_exists _ _)) H)
	| [ H: (isCons ?self2 = true) |- _ ] =>
			poseNew (Mark (self2) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H))
	| [ H1: (true = isNil ?self3) |- _ ] =>
			poseNew (Mark (self3) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H1)
	| [ H1: (isNil ?self3 = true) |- _ ] =>
			poseNew (Mark (self3) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H1))
	| _ => idtac
end.

Ltac t3 :=
  t_base ||
  LinkedList_tactic ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t4 :=
  t3 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t4.

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
  Start of BigIntAbs
 ***********************)

Definition BigIntAbs (x: Z) : Z :=
ifthenelse (Z.geb x (0)%Z) Z
	(fun _ => x )
	(fun _ => Z.opp x ).

Fail Next Obligation.

#[export] Hint Unfold BigIntAbs: definitions.

(***********************
  End of BigIntAbs
 ***********************)
