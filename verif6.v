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

Ltac t27 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t28 :=
  t27 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t28.


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

Lemma Cons_exists: (forall self20: LinkedList, ((true = isCons self20)) <-> ((exists tmp11: LinkedList, exists tmp10: Z, (Cons_construct tmp10 tmp11 = self20)))).
Proof.
	repeat t28 || eauto.
Qed.

Lemma Nil_exists: (forall self21: LinkedList, ((true = isNil self21)) <-> (((Nil_construct = self21)))).
Proof.
	repeat t28 || eauto.
Qed.

Definition Cons_type : Type :=
{src: LinkedList | (isCons src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Cons_type: refinements.

Definition Nil_type : Type :=
{src: LinkedList | (isNil src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Nil_type: refinements.

Ltac LinkedList_tactic5 := match goal with
	| [ H10: (true = isCons ?self22) |- _ ] =>
			poseNew (Mark (self22) "Cons_exists");pose proof ((proj1 (Cons_exists _ _)) H10)
	| [ H10: (isCons ?self22 = true) |- _ ] =>
			poseNew (Mark (self22) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H10))
	| [ H11: (true = isNil ?self23) |- _ ] =>
			poseNew (Mark (self23) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H11)
	| [ H11: (isNil ?self23 = true) |- _ ] =>
			poseNew (Mark (self23) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H11))
	| _ => idtac
end.

Ltac t29 :=
  t_base ||
  LinkedList_tactic5 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t30 :=
  t29 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t30.

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
Definition IntAbsToBigInt_rt2_type (x1: Z) : Type :=
{res: Z | (Z.geb res (0)%Z = true)}.

Fail Next Obligation.

#[export] Hint Unfold IntAbsToBigInt_rt2_type: core.


Equations (noind) IntAbsToBigInt (x1: Z) : IntAbsToBigInt_rt2_type x1
  by wf ignore_termination lt :=
  IntAbsToBigInt x1 := ifthenelse (propInBool ((x1 = (0)%Z))) Z
		(fun _ => (0)%Z )
		(fun _ => ifthenelse (Z.gtb x1 (0)%Z) Z
			(fun _ => Z.add (1)%Z (proj1_sig (IntAbsToBigInt (Z.sub x1 (1)%Z))) )
			(fun _ => Z.add (1)%Z (proj1_sig (IntAbsToBigInt (Z.opp (Z.add x1 (1)%Z)))) ) ).

Admit Obligations.
Fail Next Obligation.

Ltac rwrtTac_A3 := match goal with
	| [ H115: context[IntAbsToBigInt ?x1] |- _ ] =>
			poseNew (Mark (x1) "unfolding IntAbsToBigInt_equation")
	| [  |- context[IntAbsToBigInt ?x1] ] =>
			poseNew (Mark (x1) "unfolding IntAbsToBigInt_equation")
end.

Ltac rwrtTac_B3 := match goal with
	| [ H115: context[IntAbsToBigInt ?x1], H215: Marked (?x1) "unfolding IntAbsToBigInt_equation" |- _ ] =>
			poseNew (Mark (x1) "unfolded IntAbsToBigInt_equation");
			add_equation (IntAbsToBigInt_equation_1 x1)
	| [ H215: Marked (?x1) "unfolding IntAbsToBigInt_equation" |- context[IntAbsToBigInt ?x1] ] =>
			poseNew (Mark (x1) "unfolded IntAbsToBigInt_equation");
			add_equation (IntAbsToBigInt_equation_1 x1)
end.

Ltac rwrtTac3 := idtac; repeat rwrtTac_A3; repeat rwrtTac_B3.

Ltac t31 :=
  t_base ||
  LinkedList_tactic5 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t32 :=
  t31 ||
  rwrtTac3 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t32.

(***********************
  End of IntAbsToBigInt
 ***********************)

(***********************
  Start of LinkedListPrimitiveSize
 ***********************)

Obligation Tactic := idtac.
Definition LinkedListPrimitiveSize_rt1_type (x2: LinkedList) : Type :=
{res1: Z | (Z.geb res1 (0)%Z = true)}.

Fail Next Obligation.

#[export] Hint Unfold LinkedListPrimitiveSize_rt1_type: core.


Equations (noind) LinkedListPrimitiveSize (x2: LinkedList) : LinkedListPrimitiveSize_rt1_type x2
  by wf ignore_termination lt :=
  LinkedListPrimitiveSize x2 := match x2 with
	| Cons_construct head1 tail1 =>
			Z.add (Z.add (1)%Z (proj1_sig (IntAbsToBigInt head1))) (proj1_sig (LinkedListPrimitiveSize tail1))
	| Nil_construct => (0)%Z
	end.

Admit Obligations.
Fail Next Obligation.

Ltac rwrtTac_A4 := match goal with
	| [ H116: context[LinkedListPrimitiveSize ?x2] |- _ ] =>
			poseNew (Mark (x2) "unfolding LinkedListPrimitiveSize_equation")
	| [  |- context[LinkedListPrimitiveSize ?x2] ] =>
			poseNew (Mark (x2) "unfolding LinkedListPrimitiveSize_equation")
end.

Ltac rwrtTac_B4 := match goal with
	| [ H116: context[LinkedListPrimitiveSize ?x2], H216: Marked (?x2) "unfolding LinkedListPrimitiveSize_equation" |- _ ] =>
			poseNew (Mark (x2) "unfolded LinkedListPrimitiveSize_equation");
			add_equation (LinkedListPrimitiveSize_equation_1 x2)
	| [ H216: Marked (?x2) "unfolding LinkedListPrimitiveSize_equation" |- context[LinkedListPrimitiveSize ?x2] ] =>
			poseNew (Mark (x2) "unfolded LinkedListPrimitiveSize_equation");
			add_equation (LinkedListPrimitiveSize_equation_1 x2)
end.

Ltac rwrtTac4 := rwrtTac3; repeat rwrtTac_A4; repeat rwrtTac_B4.

Ltac t33 :=
  t_base ||
  LinkedList_tactic5 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t34 :=
  t33 ||
  rwrtTac4 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t34.

(***********************
  End of LinkedListPrimitiveSize
 ***********************)


(***********************
  Start of content
 ***********************)

Obligation Tactic := idtac.
Definition content_rt_type (thiss: LinkedList) : Type :=
set (Z).

Fail Next Obligation.

#[export] Hint Unfold content_rt_type: core.


Equations (noind) content (thiss: LinkedList) : content_rt_type thiss
  by wf ignore_termination lt :=
  content thiss := match thiss with
	| Nil_construct => @set_empty Z
	| Cons_construct h t35 =>
			set_union (set_union (@set_empty Z) (set_singleton h)) (content t35)
	end.

Solve Obligations with (repeat t34).
Fail Next Obligation.

Ltac rwrtTac_A5 := match goal with
	| [ H117: context[content ?thiss] |- _ ] =>
			poseNew (Mark (thiss) "unfolding content_equation")
	| [  |- context[content ?thiss] ] =>
			poseNew (Mark (thiss) "unfolding content_equation")
end.

Ltac rwrtTac_B5 := match goal with
	| [ H117: context[content ?thiss], H217: Marked (?thiss) "unfolding content_equation" |- _ ] =>
			poseNew (Mark (thiss) "unfolded content_equation");
			add_equation (content_equation_1 thiss)
	| [ H217: Marked (?thiss) "unfolding content_equation" |- context[content ?thiss] ] =>
			poseNew (Mark (thiss) "unfolded content_equation");
			add_equation (content_equation_1 thiss)
end.

Ltac rwrtTac5 := rwrtTac4; repeat rwrtTac_A5; repeat rwrtTac_B5.

Ltac t36 :=
  t_base ||
  LinkedList_tactic5 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t37 :=
  t36 ||
  rwrtTac5 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t37.

(***********************
  End of content
 ***********************)
