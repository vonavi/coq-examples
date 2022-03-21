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
result for some ``x``. In contrast, the previous lemma
``forall_not_exists`` includes the statement of ``P x`` halting as a
hypothesis.

In other words, `the excluded-middle law
<https://en.wikipedia.org/wiki/Law_of_excluded_middle>`__ (``P x \/ ~
P x``) is not always valid in constructive logic; but is not in
contradiction with it. In fact, this law is provided by module
``Coq.Logic.Classical``, and is usually used in two equivalent forms:
|*)

Require Import Coq.Logic.Classical. (* .none *)
Check classic. (* .unfold .messages *)
Check NNPP. (* .unfold .messages *)

(*|
Taking a look again at lemma ``not_forall_exists``, one sees that its
statement has the form of ``~ P -> Q``. There is a useful trick in
order to deal with such goals called `proof by contradiction
<https://en.wikipedia.org/wiki/Proof_by_contradiction>`__. It is based
on the excluded-middle law, and we will proof it in two different
ways.
|*)

Reset Initial. (* .none *)
Require Import Coq.Logic.Classical.

Lemma assume_opposite : forall P Q : Prop, (~ P -> Q) -> (~ Q -> P).
Proof.
  intros P Q H H0. apply NNPP. intro H1. apply H0, (H H1).
Qed.

Reset assume_opposite.

Lemma assume_opposite : forall P Q : Prop, (~ P -> Q) -> (~ Q -> P).
Proof.
  intros P Q. case (classic P); auto. intros H H0 H1.
  exfalso. apply H1, (H0 H).
Qed.

(*|
It should be noticed that lemma ``assume_opposite`` changes the order
of computation (the result ``Q`` now precedes the assumption ``P``),
which is prohibited in a real computation. However, it does not relate
to propositions (``Prop``) which are excluded from computation in Coq.
The reason is to keep the ability to add the excluded-middle law for
``Prop``.

So, let us "change the order of computation" at lemma
``not_forall_exists``:
|*)

Lemma not_forall_exists : forall {T : Type} (P : T -> Prop),
    ~ (forall x, P x) -> (exists x, ~ P x).
Proof.
  intros T P. apply assume_opposite. intros H x.

(*|
As a result, we get value ``x``---a candidate for ``exists x, ~ P
x``---impossible in the direct computation:
|*)

  assert (~ ~ P x) by (intro H0; apply H; now exists x).

(*|
We will transform the goal to suit lemma ``assume_opposite``, in order
to demonstrate the generality of the lemma. Then, its application will
finish the proof:
|*)

  revert H0. now apply assume_opposite.
Qed.

(*|
----

Below are appropriate examples found on `Stack Overflow
<https://stackoverflow.com/>`__:

1. `<../examples/can-any-one-help-me-how-to-prove-this-therom-in-coq.html>`__
2. `<../examples/how-to-enumerate-set-in-coq-ensemble.html>`__
3. `<../examples/proving-a-property-on-sets.html>`__
|*)
