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

Ltac t23 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t24 :=
  t23 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t24.


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

Lemma Cons_exists: (forall self16: LinkedList, ((true = isCons self16)) <-> ((exists tmp9: LinkedList, exists tmp8: Z, (Cons_construct tmp8 tmp9 = self16)))).
Proof.
	repeat t24 || eauto.
Qed.

Lemma Nil_exists: (forall self17: LinkedList, ((true = isNil self17)) <-> (((Nil_construct = self17)))).
Proof.
	repeat t24 || eauto.
Qed.

Definition Cons_type : Type :=
{src: LinkedList | (isCons src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Cons_type: refinements.

Definition Nil_type : Type :=
{src: LinkedList | (isNil src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Nil_type: refinements.

Ltac LinkedList_tactic4 := match goal with
	| [ H8: (true = isCons ?self18) |- _ ] =>
			poseNew (Mark (self18) "Cons_exists");pose proof ((proj1 (Cons_exists _ _)) H8)
	| [ H8: (isCons ?self18 = true) |- _ ] =>
			poseNew (Mark (self18) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H8))
	| [ H9: (true = isNil ?self19) |- _ ] =>
			poseNew (Mark (self19) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H9)
	| [ H9: (isNil ?self19 = true) |- _ ] =>
			poseNew (Mark (self19) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H9))
	| _ => idtac
end.

Ltac t25 :=
  t_base ||
  LinkedList_tactic4 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t26 :=
  t25 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t26.

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


(***********************
  Start of ObjectPrimitiveSize
 ***********************)

Definition ObjectPrimitiveSize (x3: Object) : {res2: Z | (Z.geb res2 (0)%Z = true)} :=
match x3 with
| Open_construct value1 => Z.add (1)%Z (BigIntAbs value1)
end.

Fail Next Obligation.

#[export] Hint Unfold ObjectPrimitiveSize: definitions.

(***********************
  End of ObjectPrimitiveSize
 ***********************)
