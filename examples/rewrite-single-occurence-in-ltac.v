(*|
################################
Rewrite single occurence in Ltac
################################

:Link: https://stackoverflow.com/q/45427869
|*)

(*|
Question
********

How can I invoke ``rewrite`` in ltac to only rewrite one occurrence? I
think coq's documentation mentions something about ``rewrite at`` but
I haven't been able to actually use it in practice and there are no
examples.

This is an example of what I am trying to do:
|*)

Definition f (a b: nat): nat.
Admitted.

Theorem theorem1: forall a b: nat, f a b = 4.
Admitted.

Theorem theorem2: forall (a b: nat), (f a b) + (f a b) = 8.
Proof.
  intros a b.
  (*
    my goal here is f a b + f a b = 8 I want to only rewrite the first
    f a b The following tactic call doesn't work
   *)
  Fail rewrite -> theorem1 at 1. (* .fails *)

(*|
Answer (Yves)
*************

When I try ``rewrite -> theorem1 at 1.`` as you suggest, I get the
following error message:
|*)

  Fail rewrite -> theorem1 at 1. (* .unfold .messages *)
Abort. (* .none *)

(*|
So, as a reaction, I restarted your script, including the following
command at the very beginning.
|*)

Require Import Setoid.

(*|
And now, it works.

.. coq:: none
|*)

Theorem theorem2: forall (a b: nat), (f a b) + (f a b) = 8.
Proof.
  intros a b.
  rewrite -> theorem1 at 1.

(*|
Answer (Rob Blanco)
*******************

You are using the ``rewrite at`` variant of the tactic, which as the
manual specifies is always performed via setoid rewriting (see
https://coq.inria.fr/refman/Reference-Manual010.html#hevea_tactic121).

Another possibility to have finer control over your rewriting rules is
to assert the general shape of your desired rewrite (which here one
would prove via ``theorem1``), then perform a focused rewrite with the
new hypothesis.

This works without resort to any libraries:
|*)

  Restart. (* .none *)
  intros a b.
  assert (H: f a b + f a b = 4 + f a b) by (rewrite theorem1; reflexivity).
  rewrite H.

(*|
Answer (Anton Trunov)
*********************

There are several options, one of them was pointed out by @Yves.

Another option is to use the pattern tactic:
|*)

  Restart. (* .none *) intros a b. (* .none *)
  pattern (f a b) at 1.
  rewrite theorem1.

(*|
The trick here is in fact that ``pattern (f a b) at 1.`` turns the
goal
|*)

  Restart. (* .none *) intros a b. (* .none *)
  Show. (* .unfold .messages *)

(*| into |*)

  pattern (f a b) at 1. (* .none *) Show. (* .unfold .messages *)

(*|
Basically, it beta-expands your goal, abstracting on the first
occurrence of ``f a b``. Also, normally ``rewrite`` won't rewrite
under binders (e.g. lambdas), because if it did, you'd be able to go
from let's say ``fun x => x + 0`` to ``fun x => x``, which are not
equal in vanilla Coq.

Then ``rewrite theorem1.`` rewrites the argument ``(f a b)`` to ``4``
and simplifies a bit (it does beta-reduction), hence you obtain ``4 +
f a b = 8``.

Side note: you can also use the ``replace`` tactic like so:
|*)

  Restart. (* .none *) intros a b. (* .none *)
  replace (f a b + f a b) with (4 + f a b) by now rewrite theorem1.
Abort. (* .none *)
