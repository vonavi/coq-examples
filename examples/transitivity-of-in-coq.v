(*|
#############################
Transitivity of ``->`` in Coq
#############################

:Link: https://stackoverflow.com/questions/55295029/transitivity-of-in-coq
|*)

(*|
Question
********

I'm trying to prove the transitivity of ``->`` in Coq's propositions:
|*)

Theorem implies_trans : forall P Q R : Prop,
    (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
Abort. (* .none *)

(*|
I wanted to destruct all propositions and simply handle **all 8
possibilities** with reflexivity. Apparently it's not that simple.
Here's what I tried:
|*)

Theorem implies_trans : forall P Q R : Prop,
    (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R H1 H2.
  Fail destruct P. (* .unfold .fails *) (** Hmmm ... this doesn't work *)
Admitted.

(*| Any help is very much appreciated, thanks! |*)

(*|
Answer
******

Coq's logic is not classical logic where propositions are true or
false. Instead, it's based in type theory and has an intuitionistic
flavor by default [1]_. In type theory, you should think of ``P -> Q``
being a function from "things of type ``P``" to "things of type ``Q``"
[2]_.

The usual way to prove a goal of type ``P -> Q`` is to use ``intro``
or ``intros`` to introduce a hypothesis of type ``P``, then use that
hypothesis to somehow produce an element of type ``Q``.

For example, we can prove that ``(P -> Q -> R) -> (Q -> P -> R)``. In
the "implication is a function" interpretation, this could be read as
saying that if we have a function that takes ``P`` and ``Q`` and
produces ``R``, then we can define a function that takes ``Q`` and
``P`` and produces ``R``. This is the same function, but with the
arguments swapped.
|*)

Definition ArgSwap_1 {P Q R: Prop}: (P -> Q -> R) -> (Q -> P -> R) :=
  fun f q p => f p q.

(*|
Using tactics, we can see the types of the individual elements.
|*)

Lemma ArgSwap_2 {P Q R: Prop}: (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intro f. intros q p. exact (f p q).
Qed.

(*|
After the ``intro``, we see that ``f: P -> Q -> R``, so ``f`` is our
function that takes ``P``'s and ``Q``'s and produces ``R``'s. After
the ``intros`` (which introduces multiple terms), we see that ``q: Q``
and ``p: P``. The last line (before the ``Qed.``) simply applies the
function ``f`` to ``p`` and ``q`` to get something in ``R``.

For your problem, the ``intros`` introduces the propositions ``P``,
``Q`` and ``R``, as well as ``H1: P -> Q`` and ``H2: Q -> R``. We can
still introduce one more term of type ``P`` though, since the goal is
``P -> R``. Can you see how to use ``H1`` and ``H2`` and an element of
``P`` to produce an element of ``R``? Hint: you'll go through ``Q``.
Also, remember that ``H1`` and ``H2`` are functions.

----

.. [1] You could add the law of excluded middle as an axiom, which
       would allow the kind of case analysis you want, but I think it
       misses the point of Coq.
.. [2] If you're wondering, the elements of ``Prop`` are still types
       and have very similar behavior to elements of ``Set`` or
       ``Type``. The only difference is that ``Prop`` is
       "impredicative", which allows propositions to quantify over all
       propositions. For example ``forall P: Prop, P -> P`` is an
       element of ``Prop``, but ``forall A: Type, A -> A`` is an
       element of the next level up of ``Type`` (``Type`` is actually
       an infinite hierarchy).
|*)
