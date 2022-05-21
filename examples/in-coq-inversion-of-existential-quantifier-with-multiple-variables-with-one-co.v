(*|
######################################################################################
In Coq: inversion of existential quantifier with multiple variables, with one command?
######################################################################################

:Link: https://stackoverflow.com/q/38282636
|*)

(*|
Question
********

I am working through a proof in which there is a hypothesis
|*)

Section Foo. (* .none *)
Parameter P : nat -> nat -> nat -> Prop. (* .none *)
Hypothesis H : exists a b v, P a b v.

(*| If I use ``inversion H``, then I recover |*)

Goal False. (* .none *)
  inversion H. (* .unfold .hyps *)

(*|
which is fine, but then I need to use ``inversion`` twice more to
recover ``b`` and ``v``. Is there a single command to recover ``a``,
``b``, ``v`` all at once?
|*)

(*|
Answer (Anton Trunov)
*********************

You can use a list of patterns ``(p1 & ... & pn)`` for sequence of
right-associative binary inductive constructors such as ``conj`` or
``ex_intro``:
|*)

  Undo. (* .none *) destruct H as (a & b & v & H').

(*|
Another nice example from the reference manual: if we have a
hypothesis

.. code-block:: coq

    A /\ (exists x, B /\ C /\ D).

Then, we can destruct it with

.. code-block:: coq

    destruct H as (a & x & b & c & d).
|*)

(*|
Answer (pintoch)
****************

Yes, by specifying binders for the objects you want to introduce, like
this:
|*)

  Undo. (* .none *) inversion H as [a [b [v H']]].

(*|
Note that ``destruct`` also works here (with the same syntax), it
generates a slightly simpler proof (In general, the manual warns
against large proofs generated by ``inversion``).
|*)
