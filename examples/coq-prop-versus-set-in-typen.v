(*|
###########################################
Coq: ``Prop`` versus ``Set`` in ``Type(n)``
###########################################

:Link: https://stackoverflow.com/q/29322534
|*)

(*|
Question
********

I want to consider the following three (related?) Coq definitions.
|*)

Inductive nat1 : Prop :=
| z1 : nat1
| s1 : nat1 -> nat1.

Inductive nat2 : Set :=
| z2 : nat2
| s2 : nat2 -> nat2.

Inductive nat3 : Type :=
| z3 : nat3
| s3 : nat3 -> nat3.

(*|
All three types give induction principles to prove a proposition holds.
|*)

Check nat1_ind. (* .unfold .messages *)
Check nat2_ind. (* .unfold .messages *)
Check nat3_ind. (* .unfold .messages *)

(*|
The set and type versions also contain induction principles for
definitions over set and type (``rec`` and ``rect`` respectively).
This is the extent of my knowledge about the difference between
``Prop`` and ``Set``; ``Prop`` has a weaker induction.

I have also read that ``Prop`` is impredicative while ``Set`` is
predicative, but this seems like a property rather than a defining
quality.

While some practical (moral?) differences between ``Set`` and ``Prop``
are clear, the exact, defining differences between ``Set`` and
``Prop``, as well as where they fit into the universe of types is
unclear (running check on ``Prop`` and ``Set`` gives ``Type (* (Set) +
1 *)``), and I'm not exactly sure how to interpret this...

----

**A:** A minor observation: ``nat1`` does not define natural numbers
in ``Prop`` -- this is discussed `here
<https://stackoverflow.com/q/41568683/2747511>`__.
|*)

(*|
Answer (gen)
************

``Type : Type`` is inconsistent.

Impredicative ``Set`` with excluded middle implies proof irrelevance,
so impredicative ``Set`` with proof relevance, e.g. ``true <> false``,
refutes excluded middle, which intuitionism isn't supposed to do.

Therefore we leave impredicativity in ``Prop`` and the rest of the
type hierarchy gives us predicativity.

By the way,

.. code-block:: coq

    forall P : nat1 -> Prop,
      P z1 -> (forall n : nat1, P n -> P (s1 n)) -> forall n : nat1, P n

is provable. Don't ask me what's the benefit of Coq only automatically
proving that other weaker induction principle...

Also, have you read `this chapter of CPDT
<http://adam.chlipala.net/cpdt/html/Universes.html>`__?
|*)

(*|
Answer (Hexadecimal Hyuga)
**************************

Just read about this in an hour. This is because Coq will assume
equality of two proof object of a same ``Prop``. This is an axiom and
is called proof irrelevance.

https://coq.inria.fr/library/Coq.Logic.ProofIrrelevance.html

It just thinks a predicate over ``Prop`` (here ``P``) doesn't really
need to have some proof passed as its argument (or hypothesis) and
removed it.

Consider this. Because of every ``nat1`` are the same, whenever we try
to proof some property ``P``, we can just abstract over some ``nat1``,
while use the axiom to rewrite it to required ones. Thus Coq generated
the "simplified" version of induction principle.

To generate the "full" version, you can use
|*)

Scheme nat1_ind_full := Induction for nat1 Sort Prop.

(*|
ref. `Different induction principles for Prop and Type
<https://stackoverflow.com/questions/39683390/different-induction-principles-for-prop-and-type>`__
|*)
