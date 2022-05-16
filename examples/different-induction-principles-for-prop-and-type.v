(*|
########################################################
Different induction principles for ``Prop`` and ``Type``
########################################################

:Link: https://stackoverflow.com/q/39683390
|*)

(*|
Question
********

I noticed that Coq synthesizes different induction principles on
equality for ``Prop`` and ``Type``. Does anybody have an explanation
for that?

Equality is defined as
|*)

Print eq. (* .unfold .messages *)

(*| And the associated induction principle has the following type: |*)

Check eq_ind. (* .unfold .messages *)

(*| Now let's define a ``Type`` pendant of ``eq``: |*)

Inductive eqT {A : Type} (x : A) : A -> Type := eqT_refl : eqT x x.

(*| The automatically generated induction principle is |*)

Check eqT_ind. (* .unfold .messages *)

(*|
Answer
******

*Note*: I'm going to use ``_rect`` principles everywhere instead of
``_ind``, since ``_ind`` principles are usually implemented via the
``_rect`` ones.

Type of ``eqT_rect``
====================

Let's take a look at the predicate ``P``. When dealing with inductive
families, the number of arguments of ``P`` is equal to the number of
*non-parametric* arguments ``(indices) + 1``.

Let me give some examples (they can be easily skipped).

- Natural numbers don't have parameters at all:

  .. coq::
|*)

Print nat. (* .unfold .messages *)

(*|
  So, the predicate ``P`` will be of type ``nat -> Type``.

- Lists have one parametric argument (``A``):

  .. coq::
|*)

Print list. (* .unfold .messages *)

(*|
  Again, ``P`` has only one argument: ``P : list A -> Type``.

- Vectors are a different:

  .. coq::
|*)

Require Coq.Vectors.VectorDef. (* .none *)
Print VectorDef.t. (* .unfold .messages *)

(*|
  ``P`` has 2 arguments, because ``n`` in ``vec A n`` is a
  non-parameteric argument:

  .. code-block:: coq

      P : forall n : nat, vec A n -> Type

The above explains ``eqT_rect`` (and, of course, ``eqT_ind`` as a
consequence), since the argument after ``(x : A)`` is non-parametric,
``P`` has 2 arguments:

.. code-block:: coq

    P : forall a : A, eqT x a -> Type

which justifies the overall type for ``eqT_rect``:
|*)

Check eqT_rect. (* .unfold .messages *)

(*|
The induction principle obtained in this way is called a *maximal
induction principle*.

Type of ``eq_rect``
===================

The generated induction principles for inductive predicates (such as
``eq``) are simplified to express proof irrelevance (the term for this
is *simplified induction principle*\ ).

When defining a predicate ``P``, Coq simply drops the last argument of
the predicate (which is the type being defined, and it lives in
``Prop``). That's why the predicate used in ``eq_rect`` is unary. This
fact shapes the type of ``eq_rect``:
|*)

Check eq_rect. (* .unfold .messages *)

(*|
How to generate maximal induction principle
===========================================

We can also make Coq generate non-simplified induction principle for
``eq``:
|*)

Scheme eq_rect_max := Induction for eq Sort Type.

(*| The resulting type is |*)

Check eq_rect_max. (* .unfold .messages *)

(*|
and it has the same structure as ``eqT_rect``.

References
==========

For more detailed explanation see sect. 14.1.3 ... 14.1.6 of the book
"Interactive Theorem Proving and Program Development (Coq'Art: The
Calculus of Inductive Constructions)" by Bertot and Castéran (2004).

----

**A:** Updated link:
https://coq.inria.fr/refman/user-extensions/proof-schemes.html#generation-of-induction-principles-with-scheme
|*)
