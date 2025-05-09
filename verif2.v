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

Ltac t5 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t6 :=
  t5 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t6.


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

Lemma Cons_exists: (forall self4: LinkedList, ((true = isCons self4)) <-> ((exists tmp3: LinkedList, exists tmp2: Z, (Cons_construct tmp2 tmp3 = self4)))).
Proof.
	repeat t6 || eauto.
Qed.

Lemma Nil_exists: (forall self5: LinkedList, ((true = isNil self5)) <-> (((Nil_construct = self5)))).
Proof.
	repeat t6 || eauto.
Qed.

Definition Cons_type : Type :=
{src: LinkedList | (isCons src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Cons_type: refinements.

Definition Nil_type : Type :=
{src: LinkedList | (isNil src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Nil_type: refinements.

Ltac LinkedList_tactic1 := match goal with
	| [ H2: (true = isCons ?self6) |- _ ] =>
			poseNew (Mark (self6) "Cons_exists");pose proof ((proj1 (Cons_exists _ _)) H2)
	| [ H2: (isCons ?self6 = true) |- _ ] =>
			poseNew (Mark (self6) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H2))
	| [ H3: (true = isNil ?self7) |- _ ] =>
			poseNew (Mark (self7) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H3)
	| [ H3: (isNil ?self7 = true) |- _ ] =>
			poseNew (Mark (self7) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H3))
	| _ => idtac
end.

Ltac t7 :=
  t_base ||
  LinkedList_tactic1 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t8 :=
  t7 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t8.

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
  Start of IntAbsToBigInt
 ***********************)

Obligation Tactic := idtac.
Definition IntAbsToBigInt_rt_type (x1: Z) : Type :=
{res: Z | (Z.geb res (0)%Z = true)}.

Fail Next Obligation.

#[export] Hint Unfold IntAbsToBigInt_rt_type: core.


Equations (noind) IntAbsToBigInt (x1: Z) : IntAbsToBigInt_rt_type x1
  by wf ignore_termination lt :=
  IntAbsToBigInt x1 := ifthenelse (propInBool ((x1 = (0)%Z))) Z
		(fun _ => (0)%Z )
		(fun _ => ifthenelse (Z.gtb x1 (0)%Z) Z
			(fun _ => Z.add (1)%Z (proj1_sig (IntAbsToBigInt (Z.sub x1 (1)%Z))) )
			(fun _ => Z.add (1)%Z (proj1_sig (IntAbsToBigInt (Z.opp (Z.add x1 (1)%Z)))) ) ).

Solve Obligations with (repeat t8).
Fail Next Obligation.

Ltac rwrtTac_A := match goal with
	| [ H14: context[IntAbsToBigInt ?x1] |- _ ] =>
			poseNew (Mark (x1) "unfolding IntAbsToBigInt_equation")
	| [  |- context[IntAbsToBigInt ?x1] ] =>
			poseNew (Mark (x1) "unfolding IntAbsToBigInt_equation")
end.

Ltac rwrtTac_B := match goal with
	| [ H14: context[IntAbsToBigInt ?x1], H24: Marked (?x1) "unfolding IntAbsToBigInt_equation" |- _ ] =>
			poseNew (Mark (x1) "unfolded IntAbsToBigInt_equation");
			add_equation (IntAbsToBigInt_equation_1 x1)
	| [ H24: Marked (?x1) "unfolding IntAbsToBigInt_equation" |- context[IntAbsToBigInt ?x1] ] =>
			poseNew (Mark (x1) "unfolded IntAbsToBigInt_equation");
			add_equation (IntAbsToBigInt_equation_1 x1)
end.

Ltac rwrtTac := idtac; repeat rwrtTac_A; repeat rwrtTac_B.

Ltac t9 :=
  t_base ||
  LinkedList_tactic1 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t10 :=
  t9 ||
  rwrtTac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t10.

(***********************
  End of IntAbsToBigInt
 ***********************)
