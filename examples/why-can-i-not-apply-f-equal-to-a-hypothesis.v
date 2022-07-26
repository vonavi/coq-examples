(*|
################################################
Why can I not apply ``f_equal`` to a hypothesis?
################################################

:Link: https://stackoverflow.com/q/72091301
|*)

(*|
Question
********

In my list of hypothesis, I have:

.. coq:: none
|*)

Section Foo.
Variables (X : Type) (l' : list X) (n' : nat).
Hypothesis H :  S (length l') = S n'.

Goal length l' = n'.

(*||*)

  Show. (* .unfold .hyps *)

(*| My goal is |*)

  Show. (* .unfold .goals *)

(*|
So I tried ``f_equal in H``. But I get the following error:

.. code::

    Syntax error: [tactic:ltac_use_default] expected after
    [tactic:tactic] (in [vernac:tactic_command]).

Am I wrong in thinking I should be able to apply ``f_equal`` to ``H``
in order to remove the ``S`` on both sides?
|*)

(*|
Answer (Théo Winterhalter)
**************************

``f_equal`` is about congruence of equality. It can be used to prove
``f x = f y`` from ``x = y``. However, it cannot be used to deduce ``x
= y`` from ``f x = f y`` because that is not true in general, only
when ``f`` is injective.

Here it is a particular case as ``S`` is a constructor of an inductive
type, and constructors are indeed injective. You could for instance
use tactics like ``inversion H`` to obtain the desired equality.

Another solution involving ``f_equal`` would be to apply a function
that removes the ``S`` like
|*)

  Definition removeS n :=
    match n with
    | S m => m
    | 0 => 0
    end.

(*| and then use |*)

  apply (f_equal removeS) in H.

(*|
Answer (jbapple)
****************

``f_equal`` tells you that if ``x = y``, then ``f x = f y``. In other
words, when you *have* ``x = y`` and *need* ``f x = f y``, you can use
``f_equal``.

Your situation is the reverse. You *have* ``f x = f y`` and you *need*
``x = y``, so you can't use ``f_equal``.

If you think about your conclusion, it is only true when ``S`` is an
injection. You need a different tactic.

----

**A:** Since ``S`` is a constructor, the tactic ``injection H`` will
work.
|*)
