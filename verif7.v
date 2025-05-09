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

Ltac t38 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t39 :=
  t38 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t39.


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

Lemma Cons_exists: (forall self24: LinkedList, ((true = isCons self24)) <-> ((exists tmp13: LinkedList, exists tmp12: Z, (Cons_construct tmp12 tmp13 = self24)))).
Proof.
	repeat t39 || eauto.
Qed.

Lemma Nil_exists: (forall self25: LinkedList, ((true = isNil self25)) <-> (((Nil_construct = self25)))).
Proof.
	repeat t39 || eauto.
Qed.

Definition Cons_type : Type :=
{src: LinkedList | (isCons src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Cons_type: refinements.

Definition Nil_type : Type :=
{src: LinkedList | (isNil src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Nil_type: refinements.

Ltac LinkedList_tactic6 := match goal with
	| [ H12: (true = isCons ?self26) |- _ ] =>
			poseNew (Mark (self26) "Cons_exists");pose proof ((proj1 (Cons_exists _ _)) H12)
	| [ H12: (isCons ?self26 = true) |- _ ] =>
			poseNew (Mark (self26) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H12))
	| [ H13: (true = isNil ?self27) |- _ ] =>
			poseNew (Mark (self27) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H13)
	| [ H13: (isNil ?self27 = true) |- _ ] =>
			poseNew (Mark (self27) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H13))
	| _ => idtac
end.

Ltac t40 :=
  t_base ||
  LinkedList_tactic6 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t41 :=
  t40 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t41.

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
Definition IntAbsToBigInt_rt3_type (x1: Z) : Type :=
{res: Z | (Z.geb res (0)%Z = true)}.

Fail Next Obligation.

#[export] Hint Unfold IntAbsToBigInt_rt3_type: core.


Equations (noind) IntAbsToBigInt (x1: Z) : IntAbsToBigInt_rt3_type x1
  by wf ignore_termination lt :=
  IntAbsToBigInt x1 := ifthenelse (propInBool ((x1 = (0)%Z))) Z
		(fun _ => (0)%Z )
		(fun _ => ifthenelse (Z.gtb x1 (0)%Z) Z
			(fun _ => Z.add (1)%Z (proj1_sig (IntAbsToBigInt (Z.sub x1 (1)%Z))) )
			(fun _ => Z.add (1)%Z (proj1_sig (IntAbsToBigInt (Z.opp (Z.add x1 (1)%Z)))) ) ).

Admit Obligations.
Fail Next Obligation.

Ltac rwrtTac_A6 := match goal with
	| [ H120: context[IntAbsToBigInt ?x1] |- _ ] =>
			poseNew (Mark (x1) "unfolding IntAbsToBigInt_equation")
	| [  |- context[IntAbsToBigInt ?x1] ] =>
			poseNew (Mark (x1) "unfolding IntAbsToBigInt_equation")
end.

Ltac rwrtTac_B6 := match goal with
	| [ H120: context[IntAbsToBigInt ?x1], H220: Marked (?x1) "unfolding IntAbsToBigInt_equation" |- _ ] =>
			poseNew (Mark (x1) "unfolded IntAbsToBigInt_equation");
			add_equation (IntAbsToBigInt_equation_1 x1)
	| [ H220: Marked (?x1) "unfolding IntAbsToBigInt_equation" |- context[IntAbsToBigInt ?x1] ] =>
			poseNew (Mark (x1) "unfolded IntAbsToBigInt_equation");
			add_equation (IntAbsToBigInt_equation_1 x1)
end.

Ltac rwrtTac6 := idtac; repeat rwrtTac_A6; repeat rwrtTac_B6.

Ltac t42 :=
  t_base ||
  LinkedList_tactic6 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t43 :=
  t42 ||
  rwrtTac6 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t43.

(***********************
  End of IntAbsToBigInt
 ***********************)

(***********************
  Start of LinkedListPrimitiveSize
 ***********************)

Obligation Tactic := idtac.
Definition LinkedListPrimitiveSize_rt2_type (x2: LinkedList) : Type :=
{res1: Z | (Z.geb res1 (0)%Z = true)}.

Fail Next Obligation.

#[export] Hint Unfold LinkedListPrimitiveSize_rt2_type: core.


Equations (noind) LinkedListPrimitiveSize (x2: LinkedList) : LinkedListPrimitiveSize_rt2_type x2
  by wf ignore_termination lt :=
  LinkedListPrimitiveSize x2 := match x2 with
	| Cons_construct head1 tail1 =>
			Z.add (Z.add (1)%Z (proj1_sig (IntAbsToBigInt head1))) (proj1_sig (LinkedListPrimitiveSize tail1))
	| Nil_construct => (0)%Z
	end.

Admit Obligations.
Fail Next Obligation.

Ltac rwrtTac_A7 := match goal with
	| [ H121: context[LinkedListPrimitiveSize ?x2] |- _ ] =>
			poseNew (Mark (x2) "unfolding LinkedListPrimitiveSize_equation")
	| [  |- context[LinkedListPrimitiveSize ?x2] ] =>
			poseNew (Mark (x2) "unfolding LinkedListPrimitiveSize_equation")
end.

Ltac rwrtTac_B7 := match goal with
	| [ H121: context[LinkedListPrimitiveSize ?x2], H221: Marked (?x2) "unfolding LinkedListPrimitiveSize_equation" |- _ ] =>
			poseNew (Mark (x2) "unfolded LinkedListPrimitiveSize_equation");
			add_equation (LinkedListPrimitiveSize_equation_1 x2)
	| [ H221: Marked (?x2) "unfolding LinkedListPrimitiveSize_equation" |- context[LinkedListPrimitiveSize ?x2] ] =>
			poseNew (Mark (x2) "unfolded LinkedListPrimitiveSize_equation");
			add_equation (LinkedListPrimitiveSize_equation_1 x2)
end.

Ltac rwrtTac7 := rwrtTac6; repeat rwrtTac_A7; repeat rwrtTac_B7.

Ltac t44 :=
  t_base ||
  LinkedList_tactic6 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t45 :=
  t44 ||
  rwrtTac7 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t45.

(***********************
  End of LinkedListPrimitiveSize
 ***********************)

(***********************
  Start of content
 ***********************)

Obligation Tactic := idtac.
Definition content_rt1_type (thiss: LinkedList) : Type :=
set (Z).

Fail Next Obligation.

#[export] Hint Unfold content_rt1_type: core.


Equations (noind) content (thiss: LinkedList) : content_rt1_type thiss
  by wf ignore_termination lt :=
  content thiss := match thiss with
	| Nil_construct => @set_empty Z
	| Cons_construct h t35 =>
			set_union (set_union (@set_empty Z) (set_singleton h)) (content t35)
	end.

Admit Obligations.
Fail Next Obligation.

Ltac rwrtTac_A8 := match goal with
	| [ H122: context[content ?thiss] |- _ ] =>
			poseNew (Mark (thiss) "unfolding content_equation")
	| [  |- context[content ?thiss] ] =>
			poseNew (Mark (thiss) "unfolding content_equation")
end.

Ltac rwrtTac_B8 := match goal with
	| [ H122: context[content ?thiss], H222: Marked (?thiss) "unfolding content_equation" |- _ ] =>
			poseNew (Mark (thiss) "unfolded content_equation");
			add_equation (content_equation_1 thiss)
	| [ H222: Marked (?thiss) "unfolding content_equation" |- context[content ?thiss] ] =>
			poseNew (Mark (thiss) "unfolded content_equation");
			add_equation (content_equation_1 thiss)
end.

Ltac rwrtTac8 := rwrtTac7; repeat rwrtTac_A8; repeat rwrtTac_B8.

Ltac t46 :=
  t_base ||
  LinkedList_tactic6 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t47 :=
  t46 ||
  rwrtTac8 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t47.

(***********************
  End of content
 ***********************)


(***********************
  Start of append
 ***********************)

Obligation Tactic := idtac.
Definition append_rt_type (thiss1: LinkedList) (x4: Z) : Type :=
{res3: LinkedList | (let assumption := (magic ((isCons res3 = true))) in (set_equality (content res3) (set_union (content thiss1) (set_union (@set_empty Z) (set_singleton x4)))) = true)}.

Fail Next Obligation.

#[export] Hint Unfold append_rt_type: core.


Equations (noind) append (thiss1: LinkedList) (x4: Z) : append_rt_type thiss1 x4
  by wf ignore_termination lt :=
  append thiss1 x4 := match thiss1 with
	| Nil_construct => Cons_construct x4 Nil_construct
	| Cons_construct h1 t48 => Cons_construct h1 (proj1_sig (append t48 x4))
	end.

Solve Obligations with (repeat t47).
Fail Next Obligation.

Ltac rwrtTac_A9 := match goal with
	| [ H123: context[append ?thiss1 ?x4] |- _ ] =>
			poseNew (Mark (thiss1,x4) "unfolding append_equation")
	| [  |- context[append ?thiss1 ?x4] ] =>
			poseNew (Mark (thiss1,x4) "unfolding append_equation")
end.

Ltac rwrtTac_B9 := match goal with
	| [ H123: context[append ?thiss1 ?x4], H223: Marked (?thiss1,?x4) "unfolding append_equation" |- _ ] =>
			poseNew (Mark (thiss1,x4) "unfolded append_equation");
			add_equation (append_equation_1 thiss1 x4)
	| [ H223: Marked (?thiss1,?x4) "unfolding append_equation" |- context[append ?thiss1 ?x4] ] =>
			poseNew (Mark (thiss1,x4) "unfolded append_equation");
			add_equation (append_equation_1 thiss1 x4)
end.

Ltac rwrtTac9 := rwrtTac8; repeat rwrtTac_A9; repeat rwrtTac_B9.

Ltac t49 :=
  t_base ||
  LinkedList_tactic6 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t50 :=
  t49 ||
  rwrtTac9 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t50.

(***********************
  End of append
 ***********************)
