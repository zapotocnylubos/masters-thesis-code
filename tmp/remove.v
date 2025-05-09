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

Ltac t82 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t83 :=
  t82 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t83.


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

Lemma Cons_exists: (forall self44: LinkedList, ((true = isCons self44)) <-> ((exists tmp23: LinkedList, exists tmp22: Z, (Cons_construct tmp22 tmp23 = self44)))).
Proof.
	repeat t83 || eauto.
Qed.

Lemma Nil_exists: (forall self45: LinkedList, ((true = isNil self45)) <-> (((Nil_construct = self45)))).
Proof.
	repeat t83 || eauto.
Qed.

Definition Cons_type : Type :=
{src: LinkedList | (isCons src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Cons_type: refinements.

Definition Nil_type : Type :=
{src: LinkedList | (isNil src = true)}.

Fail Next Obligation.

#[export] Hint Unfold  Nil_type: refinements.

Ltac LinkedList_tactic11 := match goal with
	| [ H22: (true = isCons ?self46) |- _ ] =>
			poseNew (Mark (self46) "Cons_exists");pose proof ((proj1 (Cons_exists _ _)) H22)
	| [ H22: (isCons ?self46 = true) |- _ ] =>
			poseNew (Mark (self46) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H22))
	| [ H23: (true = isNil ?self47) |- _ ] =>
			poseNew (Mark (self47) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H23)
	| [ H23: (isNil ?self47 = true) |- _ ] =>
			poseNew (Mark (self47) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H23))
	| _ => idtac
end.

Ltac t84 :=
  t_base ||
  LinkedList_tactic11 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t85 :=
  t84 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t85.

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
Definition IntAbsToBigInt_rt6_type (x1: Z) : Type :=
{res: Z | (Z.geb res (0)%Z = true)}.

Fail Next Obligation.

#[export] Hint Unfold IntAbsToBigInt_rt6_type: core.


Equations (noind) IntAbsToBigInt (x1: Z) : IntAbsToBigInt_rt6_type x1
  by wf ignore_termination lt :=
  IntAbsToBigInt x1 := ifthenelse (propInBool ((x1 = (0)%Z))) Z
		(fun _ => (0)%Z )
		(fun _ => ifthenelse (Z.gtb x1 (0)%Z) Z
			(fun _ => Z.add (1)%Z (proj1_sig (IntAbsToBigInt (Z.sub x1 (1)%Z))) )
			(fun _ => Z.add (1)%Z (proj1_sig (IntAbsToBigInt (Z.opp (Z.add x1 (1)%Z)))) ) ).

Admit Obligations.
Fail Next Obligation.

Ltac rwrtTac_A17 := match goal with
	| [ H141: context[IntAbsToBigInt ?x1] |- _ ] =>
			poseNew (Mark (x1) "unfolding IntAbsToBigInt_equation")
	| [  |- context[IntAbsToBigInt ?x1] ] =>
			poseNew (Mark (x1) "unfolding IntAbsToBigInt_equation")
end.

Ltac rwrtTac_B17 := match goal with
	| [ H141: context[IntAbsToBigInt ?x1], H241: Marked (?x1) "unfolding IntAbsToBigInt_equation" |- _ ] =>
			poseNew (Mark (x1) "unfolded IntAbsToBigInt_equation");
			add_equation (IntAbsToBigInt_equation_1 x1)
	| [ H241: Marked (?x1) "unfolding IntAbsToBigInt_equation" |- context[IntAbsToBigInt ?x1] ] =>
			poseNew (Mark (x1) "unfolded IntAbsToBigInt_equation");
			add_equation (IntAbsToBigInt_equation_1 x1)
end.

Ltac rwrtTac17 := idtac; repeat rwrtTac_A17; repeat rwrtTac_B17.

Ltac t86 :=
  t_base ||
  LinkedList_tactic11 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t87 :=
  t86 ||
  rwrtTac17 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t87.

(***********************
  End of IntAbsToBigInt
 ***********************)

(***********************
  Start of LinkedListPrimitiveSize
 ***********************)

Obligation Tactic := idtac.
Definition LinkedListPrimitiveSize_rt5_type (x2: LinkedList) : Type :=
{res1: Z | (Z.geb res1 (0)%Z = true)}.

Fail Next Obligation.

#[export] Hint Unfold LinkedListPrimitiveSize_rt5_type: core.


Equations (noind) LinkedListPrimitiveSize (x2: LinkedList) : LinkedListPrimitiveSize_rt5_type x2
  by wf ignore_termination lt :=
  LinkedListPrimitiveSize x2 := match x2 with
	| Cons_construct head1 tail1 =>
			Z.add (Z.add (1)%Z (proj1_sig (IntAbsToBigInt head1))) (proj1_sig (LinkedListPrimitiveSize tail1))
	| Nil_construct => (0)%Z
	end.

Admit Obligations.
Fail Next Obligation.

Ltac rwrtTac_A18 := match goal with
	| [ H142: context[LinkedListPrimitiveSize ?x2] |- _ ] =>
			poseNew (Mark (x2) "unfolding LinkedListPrimitiveSize_equation")
	| [  |- context[LinkedListPrimitiveSize ?x2] ] =>
			poseNew (Mark (x2) "unfolding LinkedListPrimitiveSize_equation")
end.

Ltac rwrtTac_B18 := match goal with
	| [ H142: context[LinkedListPrimitiveSize ?x2], H242: Marked (?x2) "unfolding LinkedListPrimitiveSize_equation" |- _ ] =>
			poseNew (Mark (x2) "unfolded LinkedListPrimitiveSize_equation");
			add_equation (LinkedListPrimitiveSize_equation_1 x2)
	| [ H242: Marked (?x2) "unfolding LinkedListPrimitiveSize_equation" |- context[LinkedListPrimitiveSize ?x2] ] =>
			poseNew (Mark (x2) "unfolded LinkedListPrimitiveSize_equation");
			add_equation (LinkedListPrimitiveSize_equation_1 x2)
end.

Ltac rwrtTac18 := rwrtTac17; repeat rwrtTac_A18; repeat rwrtTac_B18.

Ltac t88 :=
  t_base ||
  LinkedList_tactic11 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t89 :=
  t88 ||
  rwrtTac18 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t89.

(***********************
  End of LinkedListPrimitiveSize
 ***********************)

(***********************
  Start of content
 ***********************)

Obligation Tactic := idtac.
Definition content_rt4_type (thiss: LinkedList) : Type :=
set (Z).

Fail Next Obligation.

#[export] Hint Unfold content_rt4_type: core.


Equations (noind) content (thiss: LinkedList) : content_rt4_type thiss
  by wf ignore_termination lt :=
  content thiss := match thiss with
	| Nil_construct => @set_empty Z
	| Cons_construct h t35 =>
			set_union (set_union (@set_empty Z) (set_singleton h)) (content t35)
	end.

Admit Obligations.
Fail Next Obligation.

Ltac rwrtTac_A19 := match goal with
	| [ H143: context[content ?thiss] |- _ ] =>
			poseNew (Mark (thiss) "unfolding content_equation")
	| [  |- context[content ?thiss] ] =>
			poseNew (Mark (thiss) "unfolding content_equation")
end.

Ltac rwrtTac_B19 := match goal with
	| [ H143: context[content ?thiss], H243: Marked (?thiss) "unfolding content_equation" |- _ ] =>
			poseNew (Mark (thiss) "unfolded content_equation");
			add_equation (content_equation_1 thiss)
	| [ H243: Marked (?thiss) "unfolding content_equation" |- context[content ?thiss] ] =>
			poseNew (Mark (thiss) "unfolded content_equation");
			add_equation (content_equation_1 thiss)
end.

Ltac rwrtTac19 := rwrtTac18; repeat rwrtTac_A19; repeat rwrtTac_B19.

Ltac t90 :=
  t_base ||
  LinkedList_tactic11 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t91 :=
  t90 ||
  rwrtTac19 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t91.

(***********************
  End of content
 ***********************)

(***********************
  Start of contains
 ***********************)

Obligation Tactic := idtac.
Definition contains_rt1_type (thiss2: LinkedList) (x5: Z) : Type :=
{res4: bool | (Bool.eqb res4 (set_elem_of x5 (content thiss2)) = true)}.

Fail Next Obligation.

#[export] Hint Unfold contains_rt1_type: core.


Equations (noind) contains (thiss2: LinkedList) (x5: Z) : contains_rt1_type thiss2 x5
  by wf ignore_termination lt :=
  contains thiss2 x5 := match thiss2 with
	| Nil_construct => false
	| Cons_construct h2 t61 =>
			ifthenelse (propInBool ((h2 = x5))) bool
				(fun _ => true )
				(fun _ => proj1_sig (contains t61 x5) )
	end.

Admit Obligations.
Fail Next Obligation.

Ltac rwrtTac_A20 := match goal with
	| [ H144: context[contains ?thiss2 ?x5] |- _ ] =>
			poseNew (Mark (thiss2,x5) "unfolding contains_equation")
	| [  |- context[contains ?thiss2 ?x5] ] =>
			poseNew (Mark (thiss2,x5) "unfolding contains_equation")
end.

Ltac rwrtTac_B20 := match goal with
	| [ H144: context[contains ?thiss2 ?x5], H244: Marked (?thiss2,?x5) "unfolding contains_equation" |- _ ] =>
			poseNew (Mark (thiss2,x5) "unfolded contains_equation");
			add_equation (contains_equation_1 thiss2 x5)
	| [ H244: Marked (?thiss2,?x5) "unfolding contains_equation" |- context[contains ?thiss2 ?x5] ] =>
			poseNew (Mark (thiss2,x5) "unfolded contains_equation");
			add_equation (contains_equation_1 thiss2 x5)
end.

Ltac rwrtTac20 := rwrtTac19; repeat rwrtTac_A20; repeat rwrtTac_B20.

Ltac t92 :=
  t_base ||
  LinkedList_tactic11 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t93 :=
  t92 ||
  rwrtTac20 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t93.

(***********************
  End of contains
 ***********************)


(***********************
  Start of remove
 ***********************)

Obligation Tactic := idtac.
Definition remove_rt_type (thiss4: LinkedList) (x7: Z) : Type :=
{res6: LinkedList | (ifthenelse (implb (proj1_sig (contains thiss4 x7)) (set_equality (content res6) (set_difference (content thiss4) (set_union (@set_empty Z) (set_singleton x7))))) bool
	(fun _ => implb (negb (proj1_sig (contains thiss4 x7))) (set_equality (content res6) (content thiss4)) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

#[export] Hint Unfold remove_rt_type: core.


Equations (noind) remove (thiss4: LinkedList) (x7: Z) : remove_rt_type thiss4 x7
  by wf ignore_termination lt :=
  remove thiss4 x7 := match thiss4 with
	| Nil_construct => Nil_construct
	| Cons_construct h3 t94 =>
			let targetBound := (propInBool ((h3 = x7))) in (ifthenelse targetBound LinkedList
				(fun _ => proj1_sig (remove t94 x7) )
				(fun _ => Cons_construct h3 (proj1_sig (remove t94 x7)) ))
	end.

Solve Obligations with (repeat t93).
Fail Next Obligation.

Ltac rwrtTac_A21 := match goal with
	| [ H145: context[remove ?thiss4 ?x7] |- _ ] =>
			poseNew (Mark (thiss4,x7) "unfolding remove_equation")
	| [  |- context[remove ?thiss4 ?x7] ] =>
			poseNew (Mark (thiss4,x7) "unfolding remove_equation")
end.

Ltac rwrtTac_B21 := match goal with
	| [ H145: context[remove ?thiss4 ?x7], H245: Marked (?thiss4,?x7) "unfolding remove_equation" |- _ ] =>
			poseNew (Mark (thiss4,x7) "unfolded remove_equation");
			add_equation (remove_equation_1 thiss4 x7)
	| [ H245: Marked (?thiss4,?x7) "unfolding remove_equation" |- context[remove ?thiss4 ?x7] ] =>
			poseNew (Mark (thiss4,x7) "unfolded remove_equation");
			add_equation (remove_equation_1 thiss4 x7)
end.

Ltac rwrtTac21 := rwrtTac20; repeat rwrtTac_A21; repeat rwrtTac_B21.

Ltac t95 :=
  t_base ||
  LinkedList_tactic11 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t96 :=
  t95 ||
  rwrtTac21 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t96.

(***********************
  End of remove
 ***********************)
