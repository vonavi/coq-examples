(*|
##############################################################
Pigeonhole proof without decidable equality or excluded middle
##############################################################

:Link: https://stackoverflow.com/q/42585024
|*)

(*|
Question
********

In Software Foundations `IndProp.v
<https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html#lab244>`__
one is asked to prove the **pigeonhole principle**, and one may use
*excluded middle*, but it is mentioned that it is not strictly
necessary. I've been trying to prove it without EM, but my brain seems
to be wired classically.

Q: How would one prove the theorem *without* using excluded middle?
How should one generally approach proofs for types without decidable
equality, where one can't easily reason by cases?

I'd be very happy for a complete proof to look at, but please avoid
posting it "in the clear", so as to not spoil the exercise in the
Software Foundations course.

The definition uses two inductive predicates, ``In`` and ``repeats``.
|*)

Require Import Lists.List.
Import ListNotations.

Section Pigeon.

  Variable (X : Type).
  Implicit Type (x : X).

  Fixpoint In x l : Prop :=
    match l with
    | nil => False
    | x' :: l' => x' = x \/ In x l'
    end.

  Hypothesis in_split : forall x l, In x l ->  exists l1 l2, l = l1 ++ x :: l2.
  Hypothesis in_app : forall x l1 l2, In x (l1 ++ l2) <-> In x l1 \/ In x l2.

  Inductive repeats : list X -> Prop :=
    repeats_hd l x : In x l    -> repeats (x :: l)
  | repeats_tl l x : repeats l -> repeats (x :: l).

  Theorem pigeonhole_principle_NO_EM :  (***   pigeonhole   ***)
    forall l1 l2,
      length l2 < length l1 ->          (* There are more pigeons than nests *)
      (forall x, In x l1 -> In x l2) -> (* All pigeons are in some nest *)
      repeats l1.                       (* Thus, some pigeons share nest *)
  Proof.
    (* ??? *)
  Abort. (* .none *)

(*|
----

**Q:** Thanks, could you give an example?

**A (gallais):** Cf. `this proof in Agda
<https://github.com/gallais/potpourri/blob/master/agda/poc/PigeonHole.agda>`__
for instance.
|*)

(*|
Answer (stewbasic)
******************

I'll describe the thought process that led me to a solution, in case
it helps. We may apply induction and it is straightforward to reduce
to the case ``l1 = a :: l1'``, ``l2 = a :: l2'``. Now ``l1'`` is a
subset of ``a :: l2'``. My EM-trained intuition is that one of the
following holds:

- ``a`` is in ``l1'``.
- ``a`` is not in ``l1'``.

In the latter case, each element of ``l1'`` is in ``a :: l2'`` but
differs from ``a``, and therefore must be in ``l2'``. Thus ``l1'`` is
a subset of ``l2'``, and we can apply the inductive hypothesis.

Unfortunately if ``In`` is not decidable, the above can't be directly
formalized. In particular if equality is not decidable for the given
type, it's difficult to prove elements are unequal, and therefore
difficult to prove a negative statement like ``~(In a l1')``. However,
we wanted to use that negative statement to prove a positive one,
namely

.. code-block:: coq

    forall x, In x l1' -> In x l2'

By analogy, suppose we wanted to prove

.. coq:: none
|*)

  Section Foo.

    Variables P Q R : Prop.
    Hypotheses (H : P \/ Q) (H0 : Q -> R).

    Goal P \/ R.
      clear X in_split in_app.

(*||*)

      Show. (* .unfold .messages *)
    Abort. (* .none *)
  End Foo. (* .none *)

(*|
The above intuitive argument is like starting from ``P \/ ~P``, and
using ``~P -> Q -> R`` in the second case. We can use a direct proof
to avoid EM.

Quantifying over the list ``l1'`` makes this a bit more complicated,
but still we can construct a direct proof using the following lemma,
which can be proven by induction.
|*)

  Lemma split_or (l : list X) (P Q : X -> Prop) :
    (forall x, In x l -> (P x \/ Q x)) ->
    (exists x, In x l /\ P x) \/ (forall x, In x l -> Q x).
  Admitted. (* .none *)

(*|
----

Finally note that the intuitive pigeonhole principle could also be
formalized as the following way, which cannot be proven when the type
has undecidable equality (note that it has a negative statement in the
conclusion):
|*)

  Definition pigeon2 : Prop := forall (l1 l2 : list X),
      length l2 < length l1 ->
      (exists x, In x l1 /\ ~(In x l2)) \/ repeats l1.

(*|
Answer (András Kovács)
**********************

A possible constructive proof goes like this:

We prove ``pigeonhole_principle_NO_EM`` by induction on ``l1``. Only
the non-empty case is possible because of the length constraint. So,
assume ``l1 = x :: l1'``. Now, check whether there is some element of
``l1'`` which is mapped by ``f : (forall x, In x l1 -> In x l2)`` to
the same membership proof as ``x``. If there is such an ``x'``
element, then it follows that ``x = x'``, therefore ``l1`` repeats. If
there is no such element, then we can get ``l2'`` by removing the
element that ``x`` is mapped to from ``l2``, and apply the induction
hypothesis to ``l2'`` and the appropriate ``f' : forall x, In x l1' ->
In x l2'`` function.

That's it, but I note that actually formalizing this proof is not easy
with the definitions given, because we need to prove heterogeneous or
dependent equalities, since we have to compare membership proofs for
possibly different elements.

As to the question of getting the hang of constructive proofs in
general, an important skill or habit is always examining what kind of
data we have, not just what kind of logical facts we know. In this
case, membership proofs are actually indices pointing into lists,
bundled together with proofs that the pointed-to elements equal
certain values. If membership proofs didn't tell where exactly
elements are located then this proof would not be possible
constructively.

----

**Q:** I follow what you mean (it is quite similar to the EM proof's
structure), except for how to "check whether there is some element of
``l1'`` which is mapped by ``f : (forall x, In x l1 -> In x l2)`` to
the same membership proof as ``x``". Sorry for being so slow...

**Q:** Perhaps a stupid question, but won't membership proofs of ``In
x L`` and ``In x' L`` be different if the first one contains "``x`` is
at index 3 in the list" and the other one contains "``x'`` is at index
8", even if ``x = x'``?

**A:** To the first question: iterate through the list and decide for
each element whether it's mapped to the same index as ``x``. You first
have to implement dec. equality of membership proofs by induction on
them, then implement this check by induction on lists. To the second:
if ``In x L`` and ``In y L`` point to the same index, then ``x = y``.
We don't decide anything about equalities of elements, we decide
equality of indices, which implies equality of elements.

**Q:** "You first have to implement dec. equality of membership proofs
by induction on them" -- Do you mean I should prove i.e.
|*)

  Lemma in_proof_dec : forall l x (p q : In x l), {p = q} + {p <> q}.
  Abort. (* .none *)
(*|
Could you show how to do this, please? (Here ``In`` is unfortunately a
function and not an inductive predicate, so I need to compare
functions, which I can't, without assuming functional extensionality)

**A:** We'd like to decide `heterogeneous
<https://coq.inria.fr/library/Coq.Logic.JMeq.html>`__ equality of ``In
x l`` and ``In y l``. That's done by induction on ``l`` if ``In`` is
recursively defined on ``l``. Unfortunately I don't have immediately
deployable Coq skills, so I can't write example code. You can look at
the link in gallais' comment. He does a great job doing a simple proof
in Agda, and he also avoids heterogeneous ``In`` equalities. You can
certainly understand the types of the lemmas there even if you don't
know Agda.
|*)
