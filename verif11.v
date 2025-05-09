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

Ltac t72 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t73 :=
  t72 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t73.


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

Lemma Cons_exists: (forall self40: LinkedList, ((true = isCons self40)) <-> ((exists tmp21: LinkedList, exists tmp20: Z, (Cons_construct tmp20 tmp21 = self40)))).
Proof.
	repeat t73 || eauto.
Qed.

Lemma Nil_exists: (forall self41: LinkedList, ((true = isNil self41)) <-> (((Nil_construct = self41)))).
Proof.
	repeat t73 || eauto.
Qed.

Definition Cons_type : Type :=
{src: LinkedList | (isCons src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Cons_type: refinements.

Definition Nil_type : Type :=
{src: LinkedList | (isNil src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Nil_type: refinements.

Ltac LinkedList_tactic10 := match goal with
	| [ H20: (true = isCons ?self42) |- _ ] =>
			poseNew (Mark (self42) "Cons_exists");pose proof ((proj1 (Cons_exists _ _)) H20)
	| [ H20: (isCons ?self42 = true) |- _ ] =>
			poseNew (Mark (self42) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H20))
	| [ H21: (true = isNil ?self43) |- _ ] =>
			poseNew (Mark (self43) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H21)
	| [ H21: (isNil ?self43 = true) |- _ ] =>
			poseNew (Mark (self43) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H21))
	| _ => idtac
end.

Ltac t74 :=
  t_base ||
  LinkedList_tactic10 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t75 :=
  t74 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t75.

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
Definition IntAbsToBigInt_rt5_type (x1: Z) : Type :=
{res: Z | (Z.geb res (0)%Z = true)}.

Fail Next Obligation.

#[export] Hint Unfold IntAbsToBigInt_rt5_type: core.


Equations (noind) IntAbsToBigInt (x1: Z) : IntAbsToBigInt_rt5_type x1
  by wf ignore_termination lt :=
  IntAbsToBigInt x1 := ifthenelse (propInBool ((x1 = (0)%Z))) Z
		(fun _ => (0)%Z )
		(fun _ => ifthenelse (Z.gtb x1 (0)%Z) Z
			(fun _ => Z.add (1)%Z (proj1_sig (IntAbsToBigInt (Z.sub x1 (1)%Z))) )
			(fun _ => Z.add (1)%Z (proj1_sig (IntAbsToBigInt (Z.opp (Z.add x1 (1)%Z)))) ) ).

Admit Obligations.
Fail Next Obligation.

Ltac rwrtTac_A14 := match goal with
	| [ H136: context[IntAbsToBigInt ?x1] |- _ ] =>
			poseNew (Mark (x1) "unfolding IntAbsToBigInt_equation")
	| [  |- context[IntAbsToBigInt ?x1] ] =>
			poseNew (Mark (x1) "unfolding IntAbsToBigInt_equation")
end.

Ltac rwrtTac_B14 := match goal with
	| [ H136: context[IntAbsToBigInt ?x1], H236: Marked (?x1) "unfolding IntAbsToBigInt_equation" |- _ ] =>
			poseNew (Mark (x1) "unfolded IntAbsToBigInt_equation");
			add_equation (IntAbsToBigInt_equation_1 x1)
	| [ H236: Marked (?x1) "unfolding IntAbsToBigInt_equation" |- context[IntAbsToBigInt ?x1] ] =>
			poseNew (Mark (x1) "unfolded IntAbsToBigInt_equation");
			add_equation (IntAbsToBigInt_equation_1 x1)
end.

Ltac rwrtTac14 := idtac; repeat rwrtTac_A14; repeat rwrtTac_B14.

Ltac t76 :=
  t_base ||
  LinkedList_tactic10 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t77 :=
  t76 ||
  rwrtTac14 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t77.

(***********************
  End of IntAbsToBigInt
 ***********************)

(***********************
  Start of LinkedListPrimitiveSize
 ***********************)

Obligation Tactic := idtac.
Definition LinkedListPrimitiveSize_rt4_type (x2: LinkedList) : Type :=
{res1: Z | (Z.geb res1 (0)%Z = true)}.

Fail Next Obligation.

#[export] Hint Unfold LinkedListPrimitiveSize_rt4_type: core.


Equations (noind) LinkedListPrimitiveSize (x2: LinkedList) : LinkedListPrimitiveSize_rt4_type x2
  by wf ignore_termination lt :=
  LinkedListPrimitiveSize x2 := match x2 with
	| Cons_construct head1 tail1 =>
			Z.add (Z.add (1)%Z (proj1_sig (IntAbsToBigInt head1))) (proj1_sig (LinkedListPrimitiveSize tail1))
	| Nil_construct => (0)%Z
	end.

Admit Obligations.
Fail Next Obligation.

Ltac rwrtTac_A15 := match goal with
	| [ H137: context[LinkedListPrimitiveSize ?x2] |- _ ] =>
			poseNew (Mark (x2) "unfolding LinkedListPrimitiveSize_equation")
	| [  |- context[LinkedListPrimitiveSize ?x2] ] =>
			poseNew (Mark (x2) "unfolding LinkedListPrimitiveSize_equation")
end.

Ltac rwrtTac_B15 := match goal with
	| [ H137: context[LinkedListPrimitiveSize ?x2], H237: Marked (?x2) "unfolding LinkedListPrimitiveSize_equation" |- _ ] =>
			poseNew (Mark (x2) "unfolded LinkedListPrimitiveSize_equation");
			add_equation (LinkedListPrimitiveSize_equation_1 x2)
	| [ H237: Marked (?x2) "unfolding LinkedListPrimitiveSize_equation" |- context[LinkedListPrimitiveSize ?x2] ] =>
			poseNew (Mark (x2) "unfolded LinkedListPrimitiveSize_equation");
			add_equation (LinkedListPrimitiveSize_equation_1 x2)
end.

Ltac rwrtTac15 := rwrtTac14; repeat rwrtTac_A15; repeat rwrtTac_B15.

Ltac t78 :=
  t_base ||
  LinkedList_tactic10 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t79 :=
  t78 ||
  rwrtTac15 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t79.

(***********************
  End of LinkedListPrimitiveSize
 ***********************)

(***********************
  Start of content
 ***********************)

Obligation Tactic := idtac.
Definition content_rt3_type (thiss: LinkedList) : Type :=
set (Z).

Fail Next Obligation.

#[export] Hint Unfold content_rt3_type: core.


Equations (noind) content (thiss: LinkedList) : content_rt3_type thiss
  by wf ignore_termination lt :=
  content thiss := match thiss with
	| Nil_construct => @set_empty Z
	| Cons_construct h t35 =>
			set_union (set_union (@set_empty Z) (set_singleton h)) (content t35)
	end.

Admit Obligations.
Fail Next Obligation.

Ltac rwrtTac_A16 := match goal with
	| [ H138: context[content ?thiss] |- _ ] =>
			poseNew (Mark (thiss) "unfolding content_equation")
	| [  |- context[content ?thiss] ] =>
			poseNew (Mark (thiss) "unfolding content_equation")
end.

Ltac rwrtTac_B16 := match goal with
	| [ H138: context[content ?thiss], H238: Marked (?thiss) "unfolding content_equation" |- _ ] =>
			poseNew (Mark (thiss) "unfolded content_equation");
			add_equation (content_equation_1 thiss)
	| [ H238: Marked (?thiss) "unfolding content_equation" |- context[content ?thiss] ] =>
			poseNew (Mark (thiss) "unfolded content_equation");
			add_equation (content_equation_1 thiss)
end.

Ltac rwrtTac16 := rwrtTac15; repeat rwrtTac_A16; repeat rwrtTac_B16.

Ltac t80 :=
  t_base ||
  LinkedList_tactic10 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t81 :=
  t80 ||
  rwrtTac16 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t81.

(***********************
  End of content
 ***********************)


(***********************
  Start of prepend
 ***********************)

Definition prepend (thiss3: LinkedList) (x6: Z) : {res5: LinkedList | (let assumption1 := (magic ((isCons res5 = true))) in (set_equality (content res5) (set_union (set_union (@set_empty Z) (set_singleton x6)) (content thiss3))) = true)} :=
Cons_construct x6 thiss3.

Fail Next Obligation.

#[export] Hint Unfold prepend: definitions.

(***********************
  End of prepend
 ***********************)
