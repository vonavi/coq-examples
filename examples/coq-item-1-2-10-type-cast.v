(*|
#########################
Coq item 1.2.10 Type cast
#########################

:Link: https://stackoverflow.com/q/47072904
|*)

(*|
Question
********

Not sure what the following means in the Coq manual v8.7.0 item
`1.2.10
<https://coq.inria.fr/distrib/V8.7.0/refman/gallina.html#typecast>`__:

- The expression ``term : type`` is a type cast expression. It
  enforces the type of term to be type.
- ``term <: type`` locally sets up the virtual machine for checking
  that term has type type.

My understanding is that the type check of the first one is done by
Coq (some default), whereas the second one is done by a chosen Coq's
VM (which might have different typing rules).

I try with the following example, and couldn't see any difference from
their error message
|*)

Fail Check (3 : bool). (* .fails .unfold *)
Fail Check (3 <: bool). (* .fails .unfold *)

(*|
My question is that: might be this is the case where the default and
VM behaves the same?

Moreover, it would be nice to have an example where the ``:`` and
``<:`` behaves differently, so people could be more careful of
choosing one from the other.
|*)

(*|
Answer
******

As far as I know, the default reduction machinery and the VM reduction
machinery are designed to enforce the same typing rules.

But they don't behave the same in the sense that, for some
computations, the verification time may be of a different order of
magnitude.

Here is an example
|*)
Require Import Arith.
Time Check (refl_equal 1 : (10 ^ 6 - 9 * 10 ^ 5) / 10 ^ 5 = 1). (* .unfold *)
Time Check (refl_equal 1 <: (10 ^ 6 - 9 * 10 ^ 5) / 10 ^ 5 = 1). (* .unfold *)

(*|
This matters because large computations can occur in the middle of
proofs.
|*)
