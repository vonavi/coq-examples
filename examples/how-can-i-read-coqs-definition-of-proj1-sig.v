(*|
#################################################
How can I read Coq's definition of ``proj1_sig``?
#################################################

:Link: https://stackoverflow.com/q/41461247
|*)

(*|
Question
********

In Coq, ``sig`` is defined as
|*)

Print sig. (* .unfold .messages *)

(*|
Which I read as

    ``A sig P`` is a type, where ``P`` is a function taking an ``A``
    and returning a ``Prop``. The type is defined such that an element
    ``x`` of type ``A`` is of type ``sig P`` if ``P x`` holds.

``proj1_sig`` is defined as
|*)

Print proj1_sig. (* .unfold .messages *)

(*|
I'm not sure what to make of that. Could somebody provide a more
intuitive understanding?

----

**A:** This `question
<http://stackoverflow.com/questions/38777736/how-do-i-read-the-definition-of-ex-intro>`__
is somewhat related. And `this
<http://stackoverflow.com/questions/11593270/coq-extract-witness-from-proposition>`__
one and `this
<http://stackoverflow.com/questions/26493911/how-to-extract-z-from-subset-type-z-z-z-0>`__.
Also, `this
<http://stackoverflow.com/questions/27079513/prove-equality-on-sigma-types>`__
question on equality of sigma types can be of some interest too. I've
added these links because the automatic ones were not too close.
|*)

(*|
Answer
******

Non-dependent pairs vs. ``sig``
===============================

    The type is defined such that an element ``x`` of type ``A`` is of
    type ``sig P`` if ``P x`` holds.

That is not entirely correct: we can't say ``x : sig A P``. An
inhabitant ``e`` of type ``sig A P`` is essentially a *pair* of an
element ``x : A`` and a proof that ``P x`` holds (this is called a
`dependent pair
<https://en.wikipedia.org/wiki/Dependent_type#Dependent_pair_type>`__).
``x`` and ``P x`` are "wrapped" together using the data constructor
``exist``.

To see this let us first consider the non-dependent pair type
``prod``, which is defined as follows:
|*)

Print prod. (* .unfold .messages *)

(*|
``prod``'s inhabitants are pairs, like ``pair 1 true`` (or, using
notations, ``(1, true)``), where the *types* of both components are
*independent* of each other.

Since ``A -> B`` in Coq is just syntactic sugar for ``forall _ : A,
B`` (defined `here
<https://coq.inria.fr/library/Coq.Init.Logic.html>`__), the definition
of ``prod`` can be desugared into
|*)

Inductive prod (A B : Type) : Type :=  pair : forall _ : A, B -> prod A B.

(*|
The above definition, perhaps, can help to see that elements of ``sig
A P`` are (dependent) pairs.

What we can derive from implementation and type of ``proj1_sig``
================================================================

From the implementation we can see that ``proj1_sig e`` unpacks the
pair and returns the *first* component, viz. ``x``, throwing away the
proof of ``P x``.

The `Coq.Init.Specif
<https://coq.inria.fr/library/Coq.Init.Specif.html>`__ module contains
the following comment:

    ``(sig A P)``, or more suggestively ``{x:A | P x}``, denotes the
    subset of elements of the type ``A`` which satisfy the predicate
    ``P``.

If we look at the type of ``proj1_sig``
|*)

Check proj1_sig. (* .unfold *)

(*|
we will see that ``proj1_sig`` gives us a way of recovering an element
of a superset ``A`` from its subset ``{x : A | P x}``.

Analogue between ``fst`` and ``proj1_sig``
==========================================

Also, we can say that in some sense ``proj1_sig`` is analogous to the
`fst <https://coq.inria.fr/library/Coq.Init.Datatypes.html#fst>`__
function, which returns the first component of a pair:
|*)

Check @fst. (* .unfold *)

(*| There is a trivial property of ``fst``: |*)

Goal forall A B (a : A) (b : B),
    fst (a, b) = a.
Proof. reflexivity. Qed.

(*| We can formulate a similar statement for ``proj1_sig``: |*)

Goal forall A (P : A -> Prop) (x : A) (prf : P x),
    proj1_sig (exist P x prf) = x.
Proof. reflexivity. Qed.

(*|
----

**Q:** Okay, so suppose I have an element ``x`` of ``sig P``. Is
``proj1_sig x`` just ``x``?

**A:** No, it's not. ``x`` is a "pair". You probably meant something
like this ``proj1_sig (exist P x prf) = x``, which is an analogue of
``fst (a, b) = a``.
|*)
