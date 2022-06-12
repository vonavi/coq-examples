(*|
#############################
Definition by property in Coq
#############################

:Link: https://stackoverflow.com/q/30171995
|*)

(*|
Question
********

I am having trouble with formalizing definitions of the following
form: define an integer such that some property holds.

Let's say that I formalized the definition of the property:

.. code-block:: coq

    Definition IsGood (x : Z) : Prop := ...

Now I need a definition of the form:

.. code-block:: coq

    Definition Good : Z := ...

assuming that I proved that an integer with the property exists and is
unique:

.. code-block:: coq

    Lemma Lemma_GoodExistsUnique : exists! (x : Z), IsGood x.

Is there an easy way of defining ``Good`` using ``IsGood`` and
``Lemma_GoodExistsUnique``?

Since, the property is defined on integer numbers, it seems that no
additional axioms should be necessary. In any event, I don't see how
adding something like the axiom of choice can help with the
definition.

Also, I am having trouble with formalizing definitions of the
following form (I suspect this is related to the problem I described
above, but please indicate if that is not the case): for every ``x``,
there exists ``y``, and these ``y`` are different for different ``x``.
Like, for example, how to define that there are ``N`` distinct good
integer numbers using ``IsGood``:

.. code-block:: coq

    Definition ThereAreNGoodIntegers (N : Z) (IsGood : Z -> Prop) := ...?

In real-world mathematics, definitions like that occur every now and
again, so this should not be difficult to formalize if Coq is intended
to be suitable for practical mathematics.
|*)

(*|
Answer
******

The short answer to your first question is: in general, it is not
possible, but in your particular case, yes.

In Coq's theory, propositions (i.e., ``Prop``\ s) and their proofs
have a very special status. In particular, it is in general not
possible to write a choice operator that extracts the witness of an
existence proof. This is done to make the theory compatible with
certain axioms and principles, such as proof irrelevance, which says
that all proofs of a given proposition are equal to each other. If you
want to be able to do this, you need to add this choice operator as an
additional axiom to your theory, as in the `standard library
<https://coq.inria.fr/distrib/current/stdlib/Coq.Logic.Epsilon.html>`__.

However, in certain particular cases, it *is* possible to extract a
witness out of an abstract existence proof without recurring to any
additional axioms. In particular, it is possible to do this for
countable types (such as ``Z``) when the property in question is
decidable. You can for instance use the ``choiceType`` interface in
the `Ssreflect
<http://ssr.msr-inria.inria.fr/~jenkins/current/mathcomp.ssreflect.choice.html>`__
library to get exactly what you want (look for the ``xchoose``
function).

That being said, I would usually advice *against* doing things in this
style, because it leads to unnecessary complexity. It is probably
easier to define ``Good`` directly, without resorting to the existence
proof, and then prove separately that ``Good`` has the sought
property.
|*)

Require Import ZArith. (* .none *)
Definition Good : Z. (* ... *) Admitted.
Definition IsGood (z : Z) : Prop. (* ... *) Admitted.

Lemma GoodIsGood : IsGood Good.
Proof. (* ... *) Admitted.

Lemma GoodUnique : forall z : Z, IsGood z -> z = Good.
Proof. (* ... *) Admitted.

(*|
If you absolutely want to define ``Good`` with an existence proof, you
can also change the proof of ``Lemma_GoodExistsUnique`` to use a
connective in ``Type`` instead of ``Prop``, since it allows you to
extract the witness directly using the ``proj1_sig`` function:
|*)

Lemma Lemma_GoodExistsUnique :
  {z : Z | IsGood z /\ forall z', IsGood z' -> z' = z}.
Proof. (* ... *) Admitted.

(*|
As for your second question, yes, it is a bit related to the first
point. Once again, I would recommend that you write down a function
``y_from_x`` with type ``Z -> Z`` that will compute ``y`` given ``x``,
and then prove separately that this function relates inputs and
outputs in a particular way. Then, you can say that the ``y``\ s are
different for different ``x``\ s by proving that ``y_from_x`` is
injective.

On the other hand, I'm not sure how your last example relates to this
second question. If I understand what you want to do correctly, you
can write something like
|*)

Require Import List. (* .none *)
Definition ThereAreNGoodIntegers (N : Z) (IsGood : Z -> Prop) :=
  exists zs : list Z,
    Z.of_nat (length zs) = N
    /\ NoDup zs
    /\ Forall IsGood zs.

(*|
Here, ``Z.of_nat : nat -> Z`` is the canonical injection from naturals
to integers, ``NoDup`` is a predicate asserting that a list doesn't
contain repeated elements, and ``Forall`` is a higher-order predicate
asserting that a given predicate (in this case, ``IsGood``) holds of
all elements of a list.

As a final note, I would advice against using ``Z`` for things that
can only involve natural numbers. In your example, your using an
integer to talk about the cardinality of a set, and this number is
always a natural number.
|*)
