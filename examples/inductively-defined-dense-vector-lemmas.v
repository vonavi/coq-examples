(*|
#######################################
Inductively defined dense vector lemmas
#######################################

:Link: https://stackoverflow.com/q/31111114
|*)

(*|
Question
********

Inspired by another question on StackOverflow, I defined a *dense
vector* to be a vector with ``option A`` type elements that only
contains ``Some _`` elements, and no ``None`` elements.
|*)

Require Import Vector.

Section Dense.
  Variable A : Type.

  Inductive Is_dense : forall n, t (option A) n -> Prop :=
  | snil : Is_dense 0 (nil _)
  | scons: forall n s, Is_dense n s ->
                       forall a, Is_dense (S n) (cons _ (Some a) _ s).

(*| How can I prove the following two lemmas? |*)

  Lemma Is_dense_tl : forall n (s : t (option A) (S n)),
      Is_dense (S n) s -> Is_dense n (tl s).
  Abort. (* .none *)

(*| and |*)

  Lemma dense_hd : forall n (s : t (option A) (S n)), Is_dense (S n) s -> A.
  Abort. (* .none *)

(*|
And also, in the first lemma, when I do ``inversion s.`` I get the
elements ``h n' X`` that were used by ``s``'s constructor, but how can
I get an equality stating ``s = cons (option A) h n' X``?
|*)

(*|
Answer
******

Because of type dependency, ``inversion`` can't directly generate what
you expect, because it is not true in general. However, it is true for
a large family of types, whose equality is *decidable*. In your case,
you can apply ``Eqdep_dec.inj_pair2_eq_dec`` to get the equality you
want, if you provide the fact that equality upon ``nat`` is decidable
(and it is).

Here is the proof for the first lemma:
|*)
  Lemma Is_dense_tl : forall n (s : t (option A) (S n)),
      Is_dense (S n) s -> Is_dense n (tl s).
  Proof.
    intros n s hs.
    inversion hs. subst. clear hs.
    apply Eqdep_dec.inj_pair2_eq_dec in H0.
    - now rewrite <- H0.
    - (* insert proof of decidablity *) admit.
  Admitted.

(*|
EDIT: About your comment about the second lemma.

The main difference between your two lemmas is that the first one
tries to prove the property ``Is_dense n (tl s)`` which lives in
``Prop``, whereas the second one tries to exhibit a term of type
``A``. In short, the former creates a term of sort ``Prop``, the
latter a term of sort ``Type``.

To avoid inconsistency in Coq's logic, there is a *hierarchy* to
organize the sorts, which is (not exactly, but to give you the rough
idea) ``Prop : Set`` ``Set : Type_0`` and ``Type_n : Type_n+1``. On
top of this hierarchy is built a type system where the dependent pair
(e.g. the type ``{n : nat | even n}`` is the type of even natural
numbers) is restricted. You can build a ``Prop`` from other ``Prop``
(e.g. ``forall p : Prop, p -> p`` lives in ``Prop``). However you need
to be careful when ``Type`` is involved. For example, (again, please
refer to Coq's documentation for the exact statement) ``forall n :
Type_i, Type_j`` is of type ``Type_max(i, j)``.

This restriction is here to avoid inconsistency (like Russel's
paradox) in Coq's type system.

In your case, you are trying to inspect (using ``inversion``) a term
of sort ``Prop`` (``Is_dense (S n) s``) to build a term of type ``A``,
of sort ``Type``. This is forbidden by the type system. To build a
term of sort ``Type``, you need to inspect terms of at least the sort
``Set``. In your example, all you have to do is change the definition
of ``Is_dense`` to land in ``Type`` instead of ``Prop``, and you're
good to go.

----

**Q:** It needed a decidability proof for ``nat``, rather than for
``A``, so that was easy, using ``Arith.Peano_dec.eq_nat_dec``.
However, when I try to use ``inversion hs.`` for the second lemma, I
get the error ``Error: Inversion would require case analysis on sort
Type which is not allowed for inductive definition Is_dense.`` Why is
it possible to use inversion in the first lemma but not in the second?

**Q:** After changing ``A`` from ``Type`` to ``Set``, and chaning
``Is_dense ...`` from ``Prop`` to ``Set`` I was able to do ``inversion
hs.`` in the second lemma. What happened? Is there a less drastic
solution (than changing the definitions)?
|*)
