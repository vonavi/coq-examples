(*|
###################################################################
Coq: How to refer to the types generated by a specific constructor?
###################################################################

:Link: https://stackoverflow.com/q/52621517
|*)

(*|
Question
********

For example, if I define a function from nat to nat, it would be
|*)

Definition plusfive (a : nat) : nat := a + 5.

(*|
However, I would like to define a function whose arguments are nats
constructed using the ``S`` constructor (i.e. nonzero) is that
possible to directly specify as a type? something like

.. code-block:: coq

    Definition plusfive (a : nat.S) : nat := a + 5.

(I know that for this case I could also add an argument with a proof
that ``a`` is nonzero, but I am wondering if it is possible to
directly name the type based on the ``S`` constructor).
|*)

(*|
Answer
******

Functions have to be complete, so you will have to use some subtype
instead of ``nat``, or add an argument that reduces input space, for
instance ``(H: a <> 0)``
|*)

Reset Initial. (* .none *)
Definition plusfive (a : nat) (H : a <> 0) :=
  match a as e return a = e -> _ with
  | S _ => fun _  => a + 5
  | _   => fun H0 => match (H H0) with end
  end eq_refl.

(*|
However, these kinds of tricks have been discovered to be very
cumbersome to work with in large developments, and often one instead
uses complete functions on the base type that return dummy values for
bad input values, and prove that the function is called with correct
arguments separately from the function definition. See for example how
division is defined in the standard library.
|*)

Require Import Nat.
Print div. (* .unfold *)

(*|
So ``Compute (div 1 0).`` gives you ``0``.

The nice thing is that you can use ``div`` in expressions directly,
without having to interleave proofs that the denominator is non-zero.
Proving that an expression is correct is then done *after* it has been
defined, not at the same time.
|*)
