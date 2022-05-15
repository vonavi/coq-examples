(*|
#############################################
Adding complete disjunctive assumption in Coq
#############################################

:Link: https://stackoverflow.com/q/42342015
|*)

(*|
Question
********

In mathematics, we often proceed as follows: "Now let us consider two
cases, the number ``k`` can be ``even`` or ``odd``. For the ``even``
case, we can say ``exists k', 2k' = k``..."

Which expands to the general idea of reasoning about an entire set of
objects by disassembling it into several disjunct subsets that can be
used to reconstruct the original set.

How is this reasoning principle captured in Coq considering we do not
always have an assumption that is one of the subsets we want to
deconstruct into?

Consider the follow example for demonstration:

.. code-block:: coq

    forall n, Nat.Even n => P n.

Here we can naturally do ``inversion`` on ``Nat.Even n`` to get ``n =
2*x`` (and an automatically-false eliminated assumption that ``n = 2*x
+ 1``). However, suppose we have the following:

.. code-block:: coq

    forall n, P n

How can I state: "let us consider ``even n``\ s and ``odd n``\ s". Do
I need to first show that we have decidable ``forall n : nat, even n
\/ odd n``? That is, introduce a new (local or global) lemma listing
all the required subsets? What are the best practices?
|*)

(*|
Answer
******

Indeed, to reason about a splitting of a class of objects in Coq you
need to show an algorithm splitting them, unless you want to reason
classically (there is nothing wrong with that).

IMO, a key point is getting such decidability hypotheses "for free".
For instance, you could implement ``odd : nat -> bool`` as a boolean
function, as it is done in some libraries, then you get the splitting
for free.

[edit] You can use some slightly more convenient techniques for
pattern matching, by encoding the pertinent cases as inductives:
|*)

Require Import PeanoNat Nat Bool.

Inductive parity_spec (n : nat) : Type :=
| parity_spec_odd : odd  n = true -> parity_spec n
| parity_spec_even: even n = true -> parity_spec n.

Lemma parityP n : parity_spec n.
Proof.
  case (even n) eqn:H; [now right|left].
  now rewrite <- Nat.negb_even, H.
Qed.

Lemma test n : even n = true \/ odd n = true.
Proof. now case (parityP n); auto. Qed.

(*|
----

**A:** Yes, so with the standard library's ``Nat.odd`` for this, just
do ``destruct (Nat.odd n) eqn:Hodd.`` That puts ``Hodd: Nat.odd n =
true`` in one goal context and ``Hodd : Nat.odd n = false`` in
another. (If you don't put the ``eqn:Hname``, Coq forgets the
association between ``odd n`` and the case its considering.)
|*)
