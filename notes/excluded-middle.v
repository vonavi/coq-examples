(*|
######################################
Proof based on the excluded-middle law
######################################

In `constructive logic
<https://en.wikipedia.org/wiki/Intuitionistic_logic>`__, two lemmas
looking almost the same can have rather different complexity to prove
them. Let us give such an example:
|*)

Lemma forall_not_exists : forall {T : Type} (P : T -> Prop),
    (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros T P H [x H0]. apply H0, (H x).
Qed.

(*|
The proof is really not hard; Coq can even solve it automatically:
|*)

Reset forall_not_exists.
Lemma forall_not_exists : forall {T : Type} (P : T -> Prop),
    (forall x, P x) -> ~ (exists x, ~ P x).
Proof. firstorder. Qed.

(*|
So, we may hope to get such a simple proof for a little-bit
reformulated lemma:
|*)

Lemma not_forall_exists : forall {T : Type} (P : T -> Prop),
    ~ (forall x, P x) -> (exists x, ~ P x).
Proof. firstorder. Fail Qed. (* .fails .unfold .in .messages *)
Abort. (* .none *)

(*|
Why are we unable to proof? The point is that, due to `Curry–Howard
correspondence
<https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence>`__,
deriving a proof in constructive logic is equivalent to computing
lambda terms. As well-known, the power of `lambda calculus
<https://en.wikipedia.org/wiki/Lambda_calculus>`__ is the same as that
of `Turing machine <https://en.wikipedia.org/wiki/Turing_machine>`__.
As a result, not every proposition ``P x`` returns true or false,
sometimes it may does not halt. After taking a look at this lemma
again, we see that we are also trying to prove that ``P x`` return the
result for every ``x``. In contrast, the previous lemma
``forall_not_exists`` includes the statement of ``P x`` halting as a
hypothesis.

In other words, `the excluded-middle law
<https://en.wikipedia.org/wiki/Law_of_excluded_middle>`__ (``P x \/ ~
P x``) is not always valid in constructive logic. However, it can be
introduced to provide the proof for our example:
|*)

Lemma not_forall_exists : forall {T : Type} (P : T -> Prop),
    ~ (forall x, P x) -> (exists x, ~ P x).
Proof.
  intros T P. (* .unfold .no-hyps *)
Abort. (* .none *)

(*|
There is a useful trick in order to deal with goals like ``~ P -> Q``,
which we formulate as a lemma and prove it in two different ways. Of
course, both of them are based on the excluded-middle law, which in
turn is provided by module ``Coq.Logic.Classical``.
|*)

Require Import Coq.Logic.Classical.

Lemma negate_impl : forall P Q : Prop, (~ P -> Q) -> (~ Q -> P).
Proof.
  intros P Q H H0. apply NNPP. intro H1. apply H0, (H H1).
Qed.

Reset negate_impl.
Lemma negate_impl : forall P Q : Prop, (~ P -> Q) -> (~ Q -> P).
Proof.
  intros P Q. case (classic P); auto. intros H H0 H1.
  exfalso. apply H1, (H0 H).
Qed.

(*| Now, we can make a step ahead: |*)

Lemma not_forall_exists : forall {T : Type} (P : T -> Prop),
    ~ (forall x, P x) -> (exists x, ~ P x).
Proof.
  intros T P. apply negate_impl. intros H x.

(*|
It should be noted that the use of the trick allows us to get value
``x``---a candidate for ``exists x, ~ P x``:
|*)

  assert (~ ~ P x) by (intro H0; apply H; now exists x). revert H0.

(*|
The goal is transformed to suit the form of lemma ``negate_impl``, in
order to demonstrate the generality of the lemma. Now, its application
finishes the proof:
|*)

  now apply negate_impl.
Qed.

(*|
----

1. `<../examples/can-any-one-help-me-how-to-prove-this-therom-in-coq.html>`__
2. `<../examples/how-to-enumerate-set-in-coq-ensemble.html>`__
3. `<../examples/proving-a-property-on-sets.html>`__
|*)
