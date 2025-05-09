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

Ltac t11 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t12 :=
  t11 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t12.


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

Lemma Cons_exists: (forall self8: LinkedList, ((true = isCons self8)) <-> ((exists tmp5: LinkedList, exists tmp4: Z, (Cons_construct tmp4 tmp5 = self8)))).
Proof.
	repeat t12 || eauto.
Qed.

Lemma Nil_exists: (forall self9: LinkedList, ((true = isNil self9)) <-> (((Nil_construct = self9)))).
Proof.
	repeat t12 || eauto.
Qed.

Definition Cons_type : Type :=
{src: LinkedList | (isCons src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Cons_type: refinements.

Definition Nil_type : Type :=
{src: LinkedList | (isNil src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Nil_type: refinements.

Ltac LinkedList_tactic2 := match goal with
	| [ H4: (true = isCons ?self10) |- _ ] =>
			poseNew (Mark (self10) "Cons_exists");pose proof ((proj1 (Cons_exists _ _)) H4)
	| [ H4: (isCons ?self10 = true) |- _ ] =>
			poseNew (Mark (self10) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H4))
	| [ H5: (true = isNil ?self11) |- _ ] =>
			poseNew (Mark (self11) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H5)
	| [ H5: (isNil ?self11 = true) |- _ ] =>
			poseNew (Mark (self11) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H5))
	| _ => idtac
end.

Ltac t13 :=
  t_base ||
  LinkedList_tactic2 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t14 :=
  t13 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t14.

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
Definition IntAbsToBigInt_rt1_type (x1: Z) : Type :=
{res: Z | (Z.geb res (0)%Z = true)}.

Fail Next Obligation.

#[export] Hint Unfold IntAbsToBigInt_rt1_type: core.


Equations (noind) IntAbsToBigInt (x1: Z) : IntAbsToBigInt_rt1_type x1
  by wf ignore_termination lt :=
  IntAbsToBigInt x1 := ifthenelse (propInBool ((x1 = (0)%Z))) Z
		(fun _ => (0)%Z )
		(fun _ => ifthenelse (Z.gtb x1 (0)%Z) Z
			(fun _ => Z.add (1)%Z (proj1_sig (IntAbsToBigInt (Z.sub x1 (1)%Z))) )
			(fun _ => Z.add (1)%Z (proj1_sig (IntAbsToBigInt (Z.opp (Z.add x1 (1)%Z)))) ) ).

Admit Obligations.
Fail Next Obligation.

Ltac rwrtTac_A1 := match goal with
	| [ H17: context[IntAbsToBigInt ?x1] |- _ ] =>
			poseNew (Mark (x1) "unfolding IntAbsToBigInt_equation")
	| [  |- context[IntAbsToBigInt ?x1] ] =>
			poseNew (Mark (x1) "unfolding IntAbsToBigInt_equation")
end.

Ltac rwrtTac_B1 := match goal with
	| [ H17: context[IntAbsToBigInt ?x1], H27: Marked (?x1) "unfolding IntAbsToBigInt_equation" |- _ ] =>
			poseNew (Mark (x1) "unfolded IntAbsToBigInt_equation");
			add_equation (IntAbsToBigInt_equation_1 x1)
	| [ H27: Marked (?x1) "unfolding IntAbsToBigInt_equation" |- context[IntAbsToBigInt ?x1] ] =>
			poseNew (Mark (x1) "unfolded IntAbsToBigInt_equation");
			add_equation (IntAbsToBigInt_equation_1 x1)
end.

Ltac rwrtTac1 := idtac; repeat rwrtTac_A1; repeat rwrtTac_B1.

Ltac t15 :=
  t_base ||
  LinkedList_tactic2 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t16 :=
  t15 ||
  rwrtTac1 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t16.

(***********************
  End of IntAbsToBigInt
 ***********************)


(***********************
  Start of LinkedListPrimitiveSize
 ***********************)

Obligation Tactic := idtac.
Definition LinkedListPrimitiveSize_rt_type (x2: LinkedList) : Type :=
{res1: Z | (Z.geb res1 (0)%Z = true)}.

Fail Next Obligation.

#[export] Hint Unfold LinkedListPrimitiveSize_rt_type: core.


Equations (noind) LinkedListPrimitiveSize (x2: LinkedList) : LinkedListPrimitiveSize_rt_type x2
  by wf ignore_termination lt :=
  LinkedListPrimitiveSize x2 := match x2 with
	| Cons_construct head1 tail1 =>
			Z.add (Z.add (1)%Z (proj1_sig (IntAbsToBigInt head1))) (proj1_sig (LinkedListPrimitiveSize tail1))
	| Nil_construct => (0)%Z
	end.

Solve Obligations with (repeat t16).
Fail Next Obligation.

Ltac rwrtTac_A2 := match goal with
	| [ H18: context[LinkedListPrimitiveSize ?x2] |- _ ] =>
			poseNew (Mark (x2) "unfolding LinkedListPrimitiveSize_equation")
	| [  |- context[LinkedListPrimitiveSize ?x2] ] =>
			poseNew (Mark (x2) "unfolding LinkedListPrimitiveSize_equation")
end.

Ltac rwrtTac_B2 := match goal with
	| [ H18: context[LinkedListPrimitiveSize ?x2], H28: Marked (?x2) "unfolding LinkedListPrimitiveSize_equation" |- _ ] =>
			poseNew (Mark (x2) "unfolded LinkedListPrimitiveSize_equation");
			add_equation (LinkedListPrimitiveSize_equation_1 x2)
	| [ H28: Marked (?x2) "unfolding LinkedListPrimitiveSize_equation" |- context[LinkedListPrimitiveSize ?x2] ] =>
			poseNew (Mark (x2) "unfolded LinkedListPrimitiveSize_equation");
			add_equation (LinkedListPrimitiveSize_equation_1 x2)
end.

Ltac rwrtTac2 := rwrtTac1; repeat rwrtTac_A2; repeat rwrtTac_B2.

Ltac t17 :=
  t_base ||
  LinkedList_tactic2 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t18 :=
  t17 ||
  rwrtTac2 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t18.

(***********************
  End of LinkedListPrimitiveSize
 ***********************)
