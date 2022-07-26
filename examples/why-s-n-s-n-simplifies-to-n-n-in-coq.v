(*|
#######################################################
Why ``S n' =? S n'`` simplifies to ``n' =? n'`` in Coq?
#######################################################

:Link: https://stackoverflow.com/q/73085923
|*)

(*|
Question
********

I'm a beginner in Coq, and I've seen other examples when, if you have
``S n'`` on both sides of an equality, using the tactics ``simpl``
removes the successor function of both sides and simplifies them to
``n'``.

Although it seems "obvious", I'm wondering why it happens with this
specific function (successor). Is this behavior stated by any axiom or
something like that?
|*)

(*|
Answer
******

That's because ``_ =? _`` is defined by structural recursion on both
arguments.
|*)

Require Import Arith.
Locate "_ =? _". (* .unfold *)
Print Nat.eqb. (* .unfold *)

(*|
When you use ``simpl``, you're computing ``_ =? _``, same as you're
computing every other function that simplifies.

Note that there are two equalities for natural numbers: ``_ = _``
lives in ``Prop`` and checks whether two terms are exactly the same,
"character for character", so to say. ``_ =? _`` is defined as above.
They behave exactly the same [*]_, as the following theorem states:
|*)

Check Nat.eqb_eq. (* .unfold .messages *)

(*|
However, they aren't defined in the same way (they don't even have the
same type signature).

.. [*] This wasn't predetermined. You can define equivalence relations
   on types that don't behave like ``_ = _``. For example, rational
   numbers can be represented as pairs of a natural number and a
   positive natural number. Thus, ``<1,2>`` can represent ``1/2`` and
   yet ``<2,4>`` also represents ``1/2``. So we can define a relation
   on these pairs where ``(1,2) =? (2,4) = true``, and yet ``(1,2) <>
   (2,4)``.
|*)
