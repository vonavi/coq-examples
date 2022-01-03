(*|
###########################################
How to specialize nested hypotheses in Coq?
###########################################

:Link: https://stackoverflow.com/q/65747150
|*)

(*|
Question
********

I've already got the idea of ``specialize`` in Coq.

It works okay with ``specialize (H1 trm_int)``.

.. code-block:: coq

    H1 : forall x, value x -> term x.

But what about this case

.. code-block:: coq

    H1 : forall x, value x -> forall y, value y -> sub x y.

It doesn't work with ``specialize (H1 trm_int _trm_int)``.

Edit:

``specialize (H1 trm_int _trm_int)`` works fine with

.. code-block:: coq

    H1 : forall x y, value x -> value y -> sub x y.

Notice the ``forall y`` appears in the second premise.
|*)

(*|
Answer
******

I am not sure I understand your problem. ``specialize`` will apply
your hypothesis to the arguments you give it. It is not limited to
``forall`` quantifiers.

Say you have

.. code-block:: coq

    h : nat -> bool

you can also use ``specialize (h 0)`` and you will get

.. code-block:: coq

    h : bool

So when you have

.. code-block:: coq

    H1 : forall x, value x -> forall y, value y -> sub x y.

and you specialise, you have to use ``specialize (H1 some_x
some_value_x some_y)`` where ``some_x`` is an instance for ``x``,
``some_value_x`` is a proof of ``value some_x`` and ``some_y`` is an
instance for ``y``.

Note that there is an alternative using ``with`` that allows you to
specialise using names. Please consider the following example
|*)

Lemma foo :
  forall (h : forall x, x = 0 -> forall y, y = x -> x = y),
    True.
Proof.
  intro h.
  specialize h with (x := 0) (y := 0).

(*| Here you will end up with |*)

  Show 1. (* .unfold .messages *)

(*| But you could also give the proof directly with |*)

  Undo. (* .none *)
  specialize (h 0 eq_refl 0).
