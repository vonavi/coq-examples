(*|
###########################################################
How to "extract" ``Z`` from subset type ``{z : Z | z > 0}``
###########################################################

:Link: https://stackoverflow.com/q/26493911
|*)

(*|
Question
********

If a function take ``Z`` as arguments, it should also be possible to
take any subset of ``Z``, right? For example, ``Zmod`` takes two ``Z``
and return ``Z``. Can I improve on this method with subset types
without reimplementing it?

I want this:
|*)

Require Import ZArith.
Open Scope Z_scope.

Definition Z_gt0 := {z | z > 0}.

Fail Definition mymod (n1 n2 : Z_gt0) := Zmod n1 n2. (* .fails *)

(*|
But Coq complains that ``n1 is expected to have type Z``, of course.
How can I make it work with ``Z_gt0``? Coerce?

This question is related to my other one here: `Random nat stream and
subset types in Coq
<https://stackoverflow.com/questions/26475258/random-nat-stream-and-subset-types-in-coq>`__

**Edit:** ``proj1_sig`` might do the trick, thanks Coq IRC channel!
|*)

(*|
Answer
******

``proj1_sig`` is the usual way to go. Another solution is to pattern
match:

.. code-block:: coq

    match z1 with
      exist _ z hz => ...
    end

``z`` will be your projection, and ``hz`` will be a proof that ``z >
0``. I usually leave the first parameter anonymous since I know that
``z : Z``.

I recent version of Coq, there is another way to do it, using ``let``
(because ``sig`` is an inductive with only one constructor):
|*)

Definition Zmod_gt0 (z1 z2 : Z_gt0) : Z :=
  let (a, _) := z1 in
  let (b, _) := z2 in
  Zmod a b.
