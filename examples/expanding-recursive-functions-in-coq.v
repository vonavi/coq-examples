(*|
####################################
Expanding Recursive Functions In Coq
####################################

:Link: https://stackoverflow.com/q/29825609
|*)

(*|
Question
********

Background
==========

I understand that Iota reduction is used to reduce/expand recursive
functions. For instance, given the following application of a simple
recursive function (factorial over natural numbers):

.. code-block:: coq

    ((fix fact (n : nat) : nat :=
        match n with
        | O => 1
        | S m => n * fact m end) 2)

Iota reduction expands the recursive call, effectively iterating over
the recursive function once:
|*)

Eval lazy iota in ((fix fact (n : nat) : nat :=
                      match n with
                      | O => 1
                      | S m => n * fact m end) 2). (* .unfold *)

(*|
This behaviour generalizes nicely to mutually recursive functions. For
example, given the following mutually recursive function definitions:
|*)

Fixpoint even (n : nat) : Prop := match n with | O => True | S m => odd m end
with odd (n : nat) : Prop := match n with | O => False | S m => even m end.

(*|
Iota reduction will correctly expand over recursive calls to even or
odd respectively. To see this consider:
|*)

Theorem even_2 : even 2.
  lazy delta. (* .unfold *)
  lazy iota. (* .unfold *)
Abort. (* .none *)

(*|
Problem
=======

This is obviously the correct behaviour. **Unfortunately**, and
apparently inexplicably, Coq wont apply Iota reduction in cases where
a recursive function is either not applied to an argument or the
argument is universally quantified. For example the following does not
work:
|*)

Theorem even_n : forall n : nat, even n.
  intro n.
  lazy delta. (* .unfold *)
  lazy iota. (* FAILS TO REDUCE! *) (* .unfold *)
Abort. (* .none *)

(*|
I do not see any reason why Iota reduction should depend on the
surrounding context and have tried multiple variations to the above
trying to get Coq to Iota reduce recursive functions. Unfortunately
nothing worked.

How do I get Coq to apply Iota reduction to recursive functions that
are either not applied to any arguments or that are applied to
universally quantified arguments?
|*)

(*|
Answer
******

The problem here is that the iota rule is restricted for fixpoints:
the `Coq manual
<https://coq.inria.fr/distrib/current/refman/Reference-Manual006.html#sec217>`__
explicitly states that iota can only be applied to a fixpoint if the
decreasing argument starts with a constructor.

This is done to ensure that the calculus of inductive constructions is
strongly normalizing as a rewriting system: if we could always apply
iota, then it would be possible to expand the recursive occurrences of
the function being defined infinitely.

In practice, if you want to simplify such a fixpoint, there are two
things you can do:

1. Destruct the recursive argument (``n``, in your case) manually and
   then reduce. This is simpler to do in some cases, but requires you
   to consider many cases.

2. Prove a simplification lemma and do a rewrite instead of a
   reduction. For instance, you could have proved a lemma of the form
   ``odd n <-> ~ even n``, which might help you in some cases. You can
   also prove the unfolding explicitly as a lemma (this time, using
   your original definition of ``even``):
|*)

Goal forall n, even n = match n with | O => True | S m => odd m end.
  now destruct n.
Qed.
