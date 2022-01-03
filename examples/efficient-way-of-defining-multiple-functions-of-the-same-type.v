(*|
#############################################################
Efficient Way of Defining Multiple Functions of the Same Type
#############################################################

:Link: https://stackoverflow.com/q/49600938
|*)

(*|
Question
********

I would like to avoid copying and pasting the parameters and return
type of functions of the same type that I am trying to define. Since,
in my opinion, that would be bad programming practice.

For example, I am defining the following functions:
|*)

Definition R := nat. (* .none *)
Definition metric_non_negative {X : Type} (d : X -> X -> R) :=
  forall x y : X, (d x y) >= 0.

Definition metric_identical_arguments {X : Type} (d : X -> X -> R) :=
  forall x y : X, (d x y) = 0 <-> x = y.

(*|
I would like to be able to define both functions without repeatedly
typing the redundancy:

.. code-block:: coq

    {X : Type} (d : X -> X -> R)

I would also like to potentially define a third function, in which
case the solution should generalize to the case where more than two
functions of the same type are being defined. Is this possible, and
how so?

----

**A (Anton Trunov):** Does ``Section`` mechanism not solve your
problem?
|*)

(*|
Answer
******

As Anton Trunov mentioned in his comment, it sounds exactly like you
want to use a section:
|*)

Reset metric_non_negative. (* .none *)
Section Metric.

  Context {X : Type}.
  Variable (d : X -> X -> R).

  Definition metric_non_negative :=
    forall x y : X, (d x y) >= 0.

  Definition metric_identical_arguments :=
    forall x y : X, (d x y) = 0 <-> x = y.

End Metric.

(*|
Note that I've used ``Context`` to make ``X`` an implicit argument;
you can also use ``Set Implicit Arguments.`` and make it a
``Variable`` to let Coq set its implicitness automatically.
|*)
