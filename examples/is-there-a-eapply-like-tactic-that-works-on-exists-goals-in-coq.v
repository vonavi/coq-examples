(*|
########################################################################
Is there a ``eapply``-like tactic that works on ``exists`` goals in Coq?
########################################################################

:Link: https://stackoverflow.com/q/34216180
|*)

(*|
Question
********

I have the following during a proof where the goal is an existential,
and the target property is one of the assumptions.

.. code-block::

    H : x ==> y
    ...
    ______________________________________(1/2)
    exists t : tm, x ==> t

I know I can do ``exists y. apply H.`` to prove the current goal, but
I am wondering if there is a more intelligent tactic that can use the
assumption directly to prove the existential goal here, like ``eapply
H``?

Since this is one unification away, it would be nice not having to
write the ``X`` part in ``exists X.``.

If such a tactic does not exist, how do I write one?
|*)

(*|
Answer
******

There exists such a tactic and it is called ``eexists``. It does
exactly what you seem to expect.

https://coq.inria.fr/distrib/current/refman/Reference-Manual010.html#hevea_tactic23

----

Example use:
|*)

Variable T : Type.
Variable R : T -> T -> Prop.

Theorem test : forall x y, R x y -> exists t, R x t.
Proof.
  intros. eexists. apply H.
Qed.

(*|
----

**Q:** Thanks. An extra question. Is there a way to avoid the ``apply
H`` part? I can imagine something like ``eassumption`` that tries
``apply`` on every assumption. I tried ``assumption`` and got ``Error:
No such assumption.``

**A:** ``eexists. eassumption.`` works perfectly for the above
example. ``eauto.`` works too, btw.
|*)
