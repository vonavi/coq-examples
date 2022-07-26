(*|
##########################
How to improve this proof?
##########################

:Link: https://stackoverflow.com/q/72635620
|*)

(*|
Question
********

I work on mereology and I wanted to prove that a given theorem
(Extensionality) follows from the four axioms I had.

This is my code:
|*)

Require Import Classical.
Parameter Entity: Set.
Parameter P : Entity -> Entity -> Prop.

Axiom P_refl : forall x, P x x.

Axiom P_trans : forall x y z,
    P x y -> P y z -> P x z.

Axiom P_antisym : forall x y,
    P x y -> P y x -> x = y.

Definition PP x y := P x y /\ x <> y.
Definition O x y := exists z, P z x /\ P z y.

Axiom strong_supp : forall x y,
    ~ P y x -> exists z, P z y /\ ~ O z x.

(*| And this is my proof: |*)

Theorem extension : forall x y,
    (exists z, PP z x) -> (forall z, PP z x <-> PP z y) -> x = y.
Proof.
  intros x y [w PPwx] H.
  apply Peirce.
  intros Hcontra.
  destruct (classic (P y x)) as [yesP|notP].
  - pose proof (H y) as [].
    destruct H0.
    split; auto.
    contradiction.
  - pose proof (strong_supp x y notP) as [z []].
    assert (y = z).
    apply Peirce.
    intros Hcontra'.
    pose proof (H z) as [].
    destruct H3.
    split; auto.
    destruct H1.
    exists z.
    split.
    apply P_refl.
    assumption.
    rewrite <- H2 in H1.
    pose proof (H w) as [].
    pose proof (H3 PPwx).
    destruct PPwx.
    destruct H5.
    destruct H1.
    exists w.
    split; assumption.
Qed.

(*|
I'm happy with the fact that I completed this proof. However, I find
it quite messy. And I don't know how to improve it. (The only thing I
think of is to use patterns instead of destruct.) It is possible to
improve this proof? If so, please do not use super complex tactics: I
would like to understand the upgrades you will propose.
|*)

(*|
Answer
******

Here is a refactoring of your proof:
|*)

Reset Initial. (* .none *)
Require Import Classical.
Parameter Entity: Set.
Parameter P : Entity -> Entity -> Prop.

Axiom P_refl : forall x, P x x.

Axiom P_trans : forall x y z,
    P x y -> P y z -> P x z.

Axiom P_antisym : forall x y,
    P x y -> P y x -> x = y.

Definition PP x y := P x y /\ x <> y.
Definition O x y := exists z, P z x /\ P z y.

Axiom strong_supp : forall x y,
    ~ P y x -> exists z, P z y /\ ~ O z x.

Theorem extension : forall x y,
    (exists z, PP z x) -> (forall z, PP z x <-> PP z y) -> x = y.
Proof.
  intros x y [w PPwx] x_equiv_y.
  apply NNPP. intros x_ne_y.
  assert (~ P y x) as NPyx.
  { intros Pxy.
    enough (PP y y) as [_ y_ne_y] by congruence.
    rewrite <- x_equiv_y. split; congruence. }
  destruct (strong_supp x y NPyx) as (z & Pzy & NOzx).
  assert (y <> z) as y_ne_z.
  { intros <-. (* Substitute z right away. *)
    assert (PP w y) as [Pwy NEwy] by (rewrite <- x_equiv_y; trivial).
    destruct PPwx as [Pwx NEwx].
    apply NOzx.
    now exists w. }
  assert (PP z x) as [Pzx _].
  { rewrite x_equiv_y. split; congruence. }
  apply NOzx. exists z. split; trivial.
  apply P_refl.
Qed.

(*|
The main changes are:

1. Give explicit and informative names to all the intermediate
   hypotheses (i.e., avoid doing ``destruct foo as [x []]``)
2. Use curly braces to separate the proofs of the intermediate
   assertions from the main proof.
3. Use the ``congruence`` tactic to automate some of the low-level
   equality reasoning. Roughly speaking, this tactic solves goals that
   can be established just by rewriting with equalities and pruning
   subgoals with contradictory statements like ``x <> x``.
4. Condense trivial proof steps using the ``assert ... by tactic``,
   which does not generate new subgoals.
5. Use the ``(a & b & c)`` destruct patterns rather than ``[a [b
   c]]``, which are harder to read.
6. Rewrite with ``x_equiv_y`` to avoid doing sequences such as
   ``specialize... destruct... apply H0 in H1``
7. Avoid some unnecessary uses of classical reasoning.

----

**Q:** Is ``destruct (strong_supp x y NPyx) as (z & Pzy & NOzx).``
equivalent to ``pose proof (strong_supp x y NPyx) as (z & Pzy &
NOzx).``? I tried and its the same result. Is there a difference?

**A:** In this particular case, yes, they are equivalent.

**A:** Classical reasoning can be replaced with an extra assumption
that equality of ``Entity`` is decidable.
|*)
