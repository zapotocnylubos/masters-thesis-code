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

Ltac t51 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t52 :=
  t51 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t52.


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

Lemma Cons_exists: (forall self28: LinkedList, ((true = isCons self28)) <-> ((exists tmp15: LinkedList, exists tmp14: Z, (Cons_construct tmp14 tmp15 = self28)))).
Proof.
	repeat t52 || eauto.
Qed.

Lemma Nil_exists: (forall self29: LinkedList, ((true = isNil self29)) <-> (((Nil_construct = self29)))).
Proof.
	repeat t52 || eauto.
Qed.

Definition Cons_type : Type :=
{src: LinkedList | (isCons src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Cons_type: refinements.

Definition Nil_type : Type :=
{src: LinkedList | (isNil src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Nil_type: refinements.

Ltac LinkedList_tactic7 := match goal with
	| [ H14: (true = isCons ?self30) |- _ ] =>
			poseNew (Mark (self30) "Cons_exists");pose proof ((proj1 (Cons_exists _ _)) H14)
	| [ H14: (isCons ?self30 = true) |- _ ] =>
			poseNew (Mark (self30) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H14))
	| [ H15: (true = isNil ?self31) |- _ ] =>
			poseNew (Mark (self31) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H15)
	| [ H15: (isNil ?self31 = true) |- _ ] =>
			poseNew (Mark (self31) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H15))
	| _ => idtac
end.

Ltac t53 :=
  t_base ||
  LinkedList_tactic7 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t54 :=
  t53 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t54.

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
Definition IntAbsToBigInt_rt4_type (x1: Z) : Type :=
{res: Z | (Z.geb res (0)%Z = true)}.

Fail Next Obligation.

#[export] Hint Unfold IntAbsToBigInt_rt4_type: core.


Equations (noind) IntAbsToBigInt (x1: Z) : IntAbsToBigInt_rt4_type x1
  by wf ignore_termination lt :=
  IntAbsToBigInt x1 := ifthenelse (propInBool ((x1 = (0)%Z))) Z
		(fun _ => (0)%Z )
		(fun _ => ifthenelse (Z.gtb x1 (0)%Z) Z
			(fun _ => Z.add (1)%Z (proj1_sig (IntAbsToBigInt (Z.sub x1 (1)%Z))) )
			(fun _ => Z.add (1)%Z (proj1_sig (IntAbsToBigInt (Z.opp (Z.add x1 (1)%Z)))) ) ).

Admit Obligations.
Fail Next Obligation.

Ltac rwrtTac_A10 := match goal with
	| [ H126: context[IntAbsToBigInt ?x1] |- _ ] =>
			poseNew (Mark (x1) "unfolding IntAbsToBigInt_equation")
	| [  |- context[IntAbsToBigInt ?x1] ] =>
			poseNew (Mark (x1) "unfolding IntAbsToBigInt_equation")
end.

Ltac rwrtTac_B10 := match goal with
	| [ H126: context[IntAbsToBigInt ?x1], H226: Marked (?x1) "unfolding IntAbsToBigInt_equation" |- _ ] =>
			poseNew (Mark (x1) "unfolded IntAbsToBigInt_equation");
			add_equation (IntAbsToBigInt_equation_1 x1)
	| [ H226: Marked (?x1) "unfolding IntAbsToBigInt_equation" |- context[IntAbsToBigInt ?x1] ] =>
			poseNew (Mark (x1) "unfolded IntAbsToBigInt_equation");
			add_equation (IntAbsToBigInt_equation_1 x1)
end.

Ltac rwrtTac10 := idtac; repeat rwrtTac_A10; repeat rwrtTac_B10.

Ltac t55 :=
  t_base ||
  LinkedList_tactic7 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t56 :=
  t55 ||
  rwrtTac10 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t56.

(***********************
  End of IntAbsToBigInt
 ***********************)

(***********************
  Start of LinkedListPrimitiveSize
 ***********************)

Obligation Tactic := idtac.
Definition LinkedListPrimitiveSize_rt3_type (x2: LinkedList) : Type :=
{res1: Z | (Z.geb res1 (0)%Z = true)}.

Fail Next Obligation.

#[export] Hint Unfold LinkedListPrimitiveSize_rt3_type: core.


Equations (noind) LinkedListPrimitiveSize (x2: LinkedList) : LinkedListPrimitiveSize_rt3_type x2
  by wf ignore_termination lt :=
  LinkedListPrimitiveSize x2 := match x2 with
	| Cons_construct head1 tail1 =>
			Z.add (Z.add (1)%Z (proj1_sig (IntAbsToBigInt head1))) (proj1_sig (LinkedListPrimitiveSize tail1))
	| Nil_construct => (0)%Z
	end.

Admit Obligations.
Fail Next Obligation.

Ltac rwrtTac_A11 := match goal with
	| [ H127: context[LinkedListPrimitiveSize ?x2] |- _ ] =>
			poseNew (Mark (x2) "unfolding LinkedListPrimitiveSize_equation")
	| [  |- context[LinkedListPrimitiveSize ?x2] ] =>
			poseNew (Mark (x2) "unfolding LinkedListPrimitiveSize_equation")
end.

Ltac rwrtTac_B11 := match goal with
	| [ H127: context[LinkedListPrimitiveSize ?x2], H227: Marked (?x2) "unfolding LinkedListPrimitiveSize_equation" |- _ ] =>
			poseNew (Mark (x2) "unfolded LinkedListPrimitiveSize_equation");
			add_equation (LinkedListPrimitiveSize_equation_1 x2)
	| [ H227: Marked (?x2) "unfolding LinkedListPrimitiveSize_equation" |- context[LinkedListPrimitiveSize ?x2] ] =>
			poseNew (Mark (x2) "unfolded LinkedListPrimitiveSize_equation");
			add_equation (LinkedListPrimitiveSize_equation_1 x2)
end.

Ltac rwrtTac11 := rwrtTac10; repeat rwrtTac_A11; repeat rwrtTac_B11.

Ltac t57 :=
  t_base ||
  LinkedList_tactic7 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t58 :=
  t57 ||
  rwrtTac11 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t58.

(***********************
  End of LinkedListPrimitiveSize
 ***********************)

(***********************
  Start of content
 ***********************)

Obligation Tactic := idtac.
Definition content_rt2_type (thiss: LinkedList) : Type :=
set (Z).

Fail Next Obligation.

#[export] Hint Unfold content_rt2_type: core.


Equations (noind) content (thiss: LinkedList) : content_rt2_type thiss
  by wf ignore_termination lt :=
  content thiss := match thiss with
	| Nil_construct => @set_empty Z
	| Cons_construct h t35 =>
			set_union (set_union (@set_empty Z) (set_singleton h)) (content t35)
	end.

Admit Obligations.
Fail Next Obligation.

Ltac rwrtTac_A12 := match goal with
	| [ H128: context[content ?thiss] |- _ ] =>
			poseNew (Mark (thiss) "unfolding content_equation")
	| [  |- context[content ?thiss] ] =>
			poseNew (Mark (thiss) "unfolding content_equation")
end.

Ltac rwrtTac_B12 := match goal with
	| [ H128: context[content ?thiss], H228: Marked (?thiss) "unfolding content_equation" |- _ ] =>
			poseNew (Mark (thiss) "unfolded content_equation");
			add_equation (content_equation_1 thiss)
	| [ H228: Marked (?thiss) "unfolding content_equation" |- context[content ?thiss] ] =>
			poseNew (Mark (thiss) "unfolded content_equation");
			add_equation (content_equation_1 thiss)
end.

Ltac rwrtTac12 := rwrtTac11; repeat rwrtTac_A12; repeat rwrtTac_B12.

Ltac t59 :=
  t_base ||
  LinkedList_tactic7 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t60 :=
  t59 ||
  rwrtTac12 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t60.

(***********************
  End of content
 ***********************)


(***********************
  Start of contains
 ***********************)

Obligation Tactic := idtac.
Definition contains_rt_type (thiss2: LinkedList) (x5: Z) : Type :=
{res4: bool | (Bool.eqb res4 (set_elem_of x5 (content thiss2)) = true)}.

Fail Next Obligation.

#[export] Hint Unfold contains_rt_type: core.


Equations (noind) contains (thiss2: LinkedList) (x5: Z) : contains_rt_type thiss2 x5
  by wf ignore_termination lt :=
  contains thiss2 x5 := match thiss2 with
	| Nil_construct => false
	| Cons_construct h2 t61 =>
			ifthenelse (propInBool ((h2 = x5))) bool
				(fun _ => true )
				(fun _ => proj1_sig (contains t61 x5) )
	end.

Solve Obligations with (repeat t60).
Fail Next Obligation.

Ltac rwrtTac_A13 := match goal with
	| [ H129: context[contains ?thiss2 ?x5] |- _ ] =>
			poseNew (Mark (thiss2,x5) "unfolding contains_equation")
	| [  |- context[contains ?thiss2 ?x5] ] =>
			poseNew (Mark (thiss2,x5) "unfolding contains_equation")
end.

Ltac rwrtTac_B13 := match goal with
	| [ H129: context[contains ?thiss2 ?x5], H229: Marked (?thiss2,?x5) "unfolding contains_equation" |- _ ] =>
			poseNew (Mark (thiss2,x5) "unfolded contains_equation");
			add_equation (contains_equation_1 thiss2 x5)
	| [ H229: Marked (?thiss2,?x5) "unfolding contains_equation" |- context[contains ?thiss2 ?x5] ] =>
			poseNew (Mark (thiss2,x5) "unfolded contains_equation");
			add_equation (contains_equation_1 thiss2 x5)
end.

Ltac rwrtTac13 := rwrtTac12; repeat rwrtTac_A13; repeat rwrtTac_B13.

Ltac t62 :=
  t_base ||
  LinkedList_tactic7 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t63 :=
  t62 ||
  rwrtTac13 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t63.

(***********************
  End of contains
 ***********************)
