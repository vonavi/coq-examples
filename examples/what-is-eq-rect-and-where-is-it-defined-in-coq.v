(*|
###################################################
What is ``eq_rect`` and where is it defined in Coq?
###################################################

:Link: https://stackoverflow.com/questions/48352966/what-is-eq-rect-and-where-is-it-defined-in-coq
|*)

(*|
Question
********

From what I have read, ``eq_rect`` and equality seem deeply
interlinked. Weirdly, I'm not able to find a definition on the manual
for it.

Where does it come from, and what does it state?
|*)

(*|
Answer
******

If you use ``Locate eq_rect`` you will find that ``eq_rect`` is
located in ``Coq.Init.Logic``, but if you look in that file there is
no ``eq_rect`` in it. So, what's going on?

When you define an inductive type, Coq in many cases *automatically
generates* 3 induction principles for you, appending ``_rect``,
``_rec``, ``_ind`` to the name of the type.

To understand what ``eq_rect`` means you need its type,
|*)

Check eq_rect. (* .unfold *)

(*|
and you need to understand the notion of `Leibniz's equality
<https://en.wikipedia.org/wiki/Equality_(mathematics)#Logical_formulations>`__:

    Leibniz characterized the notion of equality as follows: Given any
    ``x`` and ``y``, ``x = y`` if and only if, given any predicate
    ``P``, ``P(x)`` if and only if ``P(y)``.

    In this law, "``P(x)`` if and only if ``P(y)``" can be weakened to
    "``P(x)`` if ``P(y)``"; the modified law is equivalent to the
    original, since a statement that applies to "any ``x`` and ``y``"
    applies just as well to "any ``y`` and ``x``".

Speaking less formally, the above quotation says that if ``x`` and
``y`` are equal, their "behavior" for every predicate is the same.

To see more clearly that Leibniz's equality directly corresponds to
``eq_rect`` we can rearrange the order of parameters of ``eq_rect``
into the following equivalent formulation:

.. code-block:: coq

    eq_rect_reorder
      : forall (A : Type) (P : A -> Type) (x y : A),
        x = y -> P x -> P y

----

**Q:** What about the other two terms that are generated? I assume
``_ind`` is the induction principle. What is ``_rec``?

**A:** Those principles have the same form, the difference between
them lies in the type of predicate ``P``: for ``eq_rect`` it's ``A ->
Type``, for ``eq_ind`` it's ``A -> Prop``, and for ``eq_rec`` -- ``A
-> Set``. In fact, ``eq_rec`` is just a special case of ``eq_rect``,
which you can check with ``Print eq_rec``.

**A:** Note that you can also generate such principles with things
like ``Scheme eq_rect := Minimality for eq Sort Type``, ``Scheme
eq_rec := Minimality for eq Sort Set``, ``Scheme eq_ind := Minimality
for eq Sort Prop``, and there are also dependent versions where you
replace ``Minimality`` with ``Induction`` and get schemes like
``forall (A : Type) (x : A) (P : forall a : A, x = a -> Type), P x
eq_refl -> forall (y : A) (e : x = y), P y e``. I believe Coq
automatically chooses ``Minimality`` for inductives in ``Prop``, and
``Induction`` for inductives landing in ``Set`` and ``Type``.
|*)
