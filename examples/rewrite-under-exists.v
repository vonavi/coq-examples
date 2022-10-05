(*|
########################
Rewrite under ``exists``
########################

:Link: https://stackoverflow.com/q/47635697
|*)

(*|
Question
********

Say I have the following relation:
|*)

Inductive my_relation: nat -> Prop :=
  constr n : my_relation n.

(*| and I want to prove the following: |*)

Lemma example:
  (forall n, my_relation n -> my_relation (S n)) ->
  (exists n, my_relation n) -> exists n, my_relation (S n).
Proof.
  intros.

(*| After introducing, I have the following environment: |*)

  Show. (* .unfold .messages *)

(*|
My question is: is there a possibility to rewrite ``H`` under the
``exists`` quantifier? If not, is there a strategy to solve this kind
of problem (this particular one is not really relevant, but problems
where you have to prove an ``exists`` using another ``exists``, and
where, informally, you can "deduce" a way to rewrite the ``exists`` in
the hypothesis into the ``exists`` in the goal)?

For instance, if I try ``rewrite H in H0.`` I have, an error
|*)

  Fail rewrite H in H0. (* .unfold .messages *)

(*|
Answer (eponier)
****************

The standard way to manipulate an existential quantification in an
hypothesis is to get a witness of the property using ``inversion`` or,
better and simpler, ``destruct``.

You can give a name to the variable using one of the following
syntaxes:
|*)

  destruct H0 as (n, H0). Undo 1. (* .none *)

  destruct H0 as [n H0]. Undo 1. (* .none *)

  destruct H0 as (n & H0).

(*|
Note that you can also destruct an hypothesis using `intro-patterns
<https://coq.inria.fr/refman/tactics.html#sec364>`__.
|*)

  Restart. (* .none *)
  intros H (n & H0).

(*| And you can even directly apply ``H`` in ``H0``. |*)

  Restart. (* .none *)
  intros H (n & H0%H). exists n. assumption.

(*|
`Software Foundations
<https://softwarefoundations.cis.upenn.edu/lf-current/Logic.html#lab175>`__
explains this in a clear way.
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

I found a way, I post it here for any similar questions in the future.

It is possible to inverse the ``exists`` hypothesis, in order to
"instantiate" the quantified variable, for instance, here, the proof
can be finished by:
|*)

  Restart. (* .none *) intros. (* .none *)
  inversion H0. apply H in H1.
  exists x. apply H1.

(*| After ``inversion H0``, we have in the environment: |*)

  Restart. (* .none *) intros. (* .none *) inversion H0. (* .none *)
  Show. (* .unfold .messages *)

(*| and we can now work with ``x``. |*)
