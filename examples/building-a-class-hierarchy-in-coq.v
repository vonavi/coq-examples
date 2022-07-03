(*|
##################################
Building a class hierarchy in Coq?
##################################

:Link: https://stackoverflow.com/q/7990301
|*)

(*|
Question
********

I can naively construct a hierarchy of algebraic structures in Coq
using type classes. I'm having some trouble finding resources on Coq's
syntax and semantics for type classes. However, I believe the
following is a correct implementation of semigroups, monoids and
commutative monoids:
|*)

Class Semigroup {A : Type} (op : A -> A -> A) : Type := {
    op_associative : forall x y z : A, op x (op y z) = op (op x y) z
  }.

Class Monoid `(M : Semigroup) (id : A) : Type := {
    id_ident_left  : forall x : A, op id x = x;
    id_ident_right : forall x : A, op x id = x
  }.

Class AbelianMonoid `(M : Monoid) : Type := {
    op_commutative : forall x y : A, op x y = op y x
  }.

(*|
If I understand correctly, additional parameters (e.g., the identity
element of a monoid) can be added by first declaring ``Monoid`` an
instance of ``Semigroup``, then parameterizing on ``id : A``. However,
something odd is occurring in the record constructed for
``AbelianMonoid``.
|*)

Print Monoid. (* .unfold *)
Print AbelianMonoid. (* .unfold *)

(*|
This occurred when I was trying to build a class for semigroups. I
thought that the following syntax was correct:

.. code-block:: coq

    Class Semiring `(P : AbelianMonoid) `(M : Monoid) := {
        ...
      }.

However, I couldn't disambigutate the correct operators and identity
elements. Printing the records revealed the problems outlined above.
So I have two questions: first, how do I correctly declare the class
``Monoid``; second, how do I disambiguate functions in superclasses?

What I'd really like is a good resources that clearly explains Coq's
type classes without antiquated syntax. For example, I thought
Hutton's book explained type classes in Haskell clearly.
|*)

(*|
Answer
******

References:
===========

The canonical references for type classes in Coq - beyond `the manual
<http://coq.inria.fr/refman/Reference-Manual024.html>`__ - are `this
paper
<http://mattam.org/research/publications/First-Class_Type_Classes.pdf>`__,
and `the thesis <http://mattam.org/research/PhD.en.html>`__ (in
french) of `Matthieu Sozeau <http://mattam.org/>`__. There are less
canonical references (with different points of view) at the research
level in `a recent paper <http://arxiv.org/abs/1102.1323>`__, and in
`my thesis <http://pastel.archives-ouvertes.fr/pastel-00649586>`__.
You should also spend some time on the #coq channel on Freenode, and
subscribe to `the mailing list
<https://sympa-roc.inria.fr/wws/arc/coq-club>`__.

Your problem:
=============

The syntax issue is not with ``Classes`` per se, but with `maximally
inserted implicit arguments
<http://coq.inria.fr/refman/Reference-Manual004.html#htoc53>`__. The
``Monoid`` and ``AbelianMonoid`` *types* have in your definition
(implicit) parametric arguments that are, in this order, the domain
type, the operation, and the identity - as indexed by the dependent
product that you see fully expanded when you print those record types.
They are filled automatically when you mention the dependent product
without its arguments in a position where it would need them.

Indeed, implicit argument resolution will automatically insert the
required parametric arguments to be identical (for both products that
depend on them: ``P`` and ``M``'s types) if left to its own devices.
You just need to specify constraints between those identifiers by
specifying variables for the various identifiers, distinct when
appropriate:
|*)

Class Semiring A mul add `(P : AbelianMonoid A mul) `(M : Monoid A add) := {
  }.

(*| The result: |*)

Print Semiring. (* .unfold *)

(*|
Note the identities for the abelian monoid and monoid are this time
distinct. It's a good exercise (even if it makes little mathematical
sense) to train yourself to write the record type (aka the ``Class``)
you would want if you had the same identity element for the additive
and multiplicative structures.
|*)
