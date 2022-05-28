(*|
###########################################################
How to use an unequality to simplify a if-then-else in Coq?
###########################################################

:Link: https://stackoverflow.com/q/34135724
|*)

(*|
Question
********

I am in the middle of a proof, where I generated two cases by

.. code-block:: coq

    destruct (eq_id_dec Y X)

(``eq_id_dec`` is similar in nature to ``eq_nat_dec``).

This gives two cases with added assumptions ``e: Y = X`` for equality
and ``n: Y <> X`` for unequality, respectively.

In the first case, I can easily use ``rewrite e`` or ``rewrite <- e``.

But how can I efficiently make use of the unequality in the second
case? Consider, e.g. a goal such as

.. code-block:: coq

    (if eq_id_dec X Y then AAA else BBB) = BBB

?

I tried ``unfold eq_id_dec`` and some ``rewrite``\ s but got stuck.

----

**A:** Is there a reason why you're not destructing ``eq_id_dec X Y``?
If you want functions to reduce, it's always a good strategy to
perform the precise case analysis they do.
|*)

(*|
Answer
******

Ideally, you would like to say something like
|*)

Goal forall (P : Prop)
            (b : {P} + {~ P})
            (H : ~ P), b = right H.
Abort. (* .none *)

(*|
Unfortunately, it is not possible to show this result without assuming
functional extensionality, because there is no useful principle that
allows you to show that two proofs of negation are equal.

You can prove a generic consequence of this lemma for your case, like
this:
|*)

Require Import Coq.Arith.Peano_dec.

Lemma sumboolF T P (b : {P} + {~ P}) x y : ~ P -> (if b then x else y) = y :> T.
Proof.
  intros. destruct b; tauto.
Qed.

Lemma test n m : n <> m -> (if eq_nat_dec n m then 1 else 0) = 0.
Proof.
  intros H. rewrite sumboolF; auto.
Qed.

(*|
This helps solving your case, but may require showing analogous
results for other uses of the ``sumbool`` type.

This is one of the issues that are making us consider removing
``sumbool`` from the Software Foundations book, and just using plain
booleans instead.
|*)
