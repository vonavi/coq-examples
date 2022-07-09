(*|
#############################################################
Is it possible to declare type-dependent ``Notation`` in Coq?
#############################################################

:Link: https://stackoverflow.com/q/69944163
|*)

(*|
Question
********

As Coq has a powerful type inference algorithm, I am wondering whether
we can "overload" notations for different rewriting based on the
``Notation``'s variables.

As an example, I will borrow a piece of my work on formalizing a typed
language's semantics in Coq. In this formalization, I have both pairs
of types and pairs of expressions, and I would like to use the same
symbol for their respective constructor: ``{ _ , _ }``.

.. code-block:: coq

    Inductive type : Type := ... | tpair: type -> type -> type | ...
    Inductive expr : Type := ... | epair: expr -> expr -> expr | ...

    Notation "{ t1 , t2 }" := tpair t1 t2
    Notation "{ e1 , e2 }" := epair e1 e2

I know the last statement will raise an error because of the notation
being already defined; I would appreciate if somebody has thought
about trickery around it, or if there is another "official" way of
doing this.
|*)

(*|
Answer
******

One easy way to overload notations is by using scopes. In fact you
should use scopes most of the time so that your notations don't mix
with notations from other work that you might include or that might
include yours.

Using scope delimiters, you could have ``{ t1 , t2 }%ty`` and ``{ e1 ,
e2 }%exp`` for instance (with the delimiters ``ty`` and ``exp`` to
disambiguate).

That said, in order to leverage typing information, there is one trick
involving typeclasses which is to have a generic notion of pairs which
comes with its own notation, and then declaring instances of that. See
example below:
|*)

Class PairNotation (A : Type) := __pair : A -> A -> A.

Notation "{ x , y }" := (__pair x y).

Instance PairNotationNat : PairNotation nat := {
    __pair n m := n + m
  }.

Axiom term : Type.
Axiom tpair : term -> term -> term.

Instance PairNotationTerm : PairNotation term := {
    __pair := tpair
  }.

Definition foo (n m : nat) : nat := { n , m }.
Definition bar (u v : term) := { u , v }.

(*|
----

**A:** For instance, `the stdpp library
<https://gitlab.mpi-sws.org/iris/stdpp>`__ makes pervasive use of
for-notation-only typeclasses to provide overloaded notations like `≡
(Equiv)
<https://gitlab.mpi-sws.org/iris/stdpp/-/blob/0939f35/theories/base.v#L245-268>`__,
``∅`` (``Empty``), ``_ !! _`` (``Lookup``), etc. A minor naming issue
(this answer does it better than stdpp) is that with a typeclass named
``Equiv`` you might think you have the mathematical properties of an
equivalence relation, whereas all you get is a notation
(well-formedness properties are stated by another typeclass,
``Equivalence``).
|*)
