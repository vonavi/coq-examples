(*|
###################################
Every proof deserves its own "view"
###################################

It is obvious that the validity of statement strongly depends on the
number sets appearing in its formulation. That leads to an illusion
that the proof itself should rely on particular properties of these
numbers. For instance, the definition of natural numbers in Coq
follows `Peano's encoding
<https://en.wikipedia.org/wiki/Peano_axioms>`__:
|*)

Print nat. (* .unfold .messages *)

(*|
Here, a natural number is created either from the constant ``O`` or by
applying the function ``S`` to another natural number. ``S`` is the
successor function which represents adding 1 to a number. Thus, ``O``
is zero, ``S O`` is one, ``S (S O)`` is two, ``S (S (S O))`` is three,
and so on.

In turn, this encoding of natural numbers brings us the ``nat_ind``
induction principle playing a vital role in proving properties of
natural numbers:
|*)

Check nat_ind. (* .unfold .messages *)

(*|
The induction principle, usually called `mathematical induction
<https://en.wikipedia.org/wiki/Mathematical_induction>`__, reads the
following. Proposition :math:`P(n)` holds for every natural number
:math:`n = 0, 1, 2, \dots` if the following two statements are
satisfied:

1. The **initial** or **base state**: the proposition holds for
   :math:`n = 0`.
2. The **induction step**: if the proposition holds for :math:`n`,
   then it holds for :math:`n + 1`.

Below is our illustrating example the consideration of which we start
from applying the induction principle (tactic ``induction``):
|*)

Require Import PeanoNat.

Lemma triangle_num : forall n : nat, Nat.even (n * S n) = true.
Proof.
  intro n. rewrite Nat.even_mul, Bool.orb_true_iff.
  induction n; tauto.
Qed.

(*|
Here, despite the use of the induction principle, our major
observation relates to the fact that ``n`` or ``S n`` is even. The
role of the induction principle is to use this fact in order to
conclude the evenness of ``S n`` or ``S (S n)``.
|*)

Inductive parity n :=
| parity_even : Nat.even n = true -> parity n
| parity_even_S : Nat.even (S n) = true -> parity n.

Lemma parity_spec : forall n : nat, parity n.
Proof.
  intro n. induction n as [| ? [? | ?]]; now constructor.
Qed.

Lemma triangle_num' : forall n : nat, Nat.even (n * S n) = true.
Proof.
  intro n. rewrite Nat.even_mul, Bool.orb_true_iff.
  destruct (parity_spec n); tauto.
Qed.

(*| ---- |*)

Lemma mod_sym : forall a b : nat,
    a <> 0 -> b <> 0 -> a mod b = b mod a <-> a = b.
Abort. (* .none *)

(*|
After some failed tries, I recommend you to take a coffee break and,
then, make a try with pen and paper. It should stimulate you to turn
into a case analysis and find out three distinct cases: ``a < b``, ``a
= b``, and ``a > b``. However, in comparison with mathematical
induction, reasoning about cases in Coq seems not so convenient. The
point is that every case is a proposition (``Prop``), not inductive
type; hence, our case analysis is non-constructive.

The good news is that Coq provides an appropriate inductive type for
case analysis:
|*)

Print sumbool. (* .unfold .messages *)

(*|
In turn, our case analysis is expressed by decidable equality:
|*)

Require Import Compare_dec. (* .none *)
Check lt_eq_lt_dec. (* .unfold .messages *)

(*|
Returning to our example, one can now split the set of natural numbers
into the desired cases:
|*)

Require Import Compare_dec.

Lemma mod_sym : forall a b : nat,
    a <> 0 -> b <> 0 -> a mod b = b mod a <-> a = b.
Proof.
  intros a b Ha Hb. pose proof (lt_eq_lt_dec a b) as H.
  destruct H as [H | H]. 1: destruct H as [H | H].
  Show 1. (* .unfold .messages *)
  Show 2. (* .unfold .messages *)
  Show 3. (* .unfold .messages *)

(*|
The rest of proof is straightforward:
|*)

  all: split; auto.
  - apply Nat.mod_small in H. intro H0. rewrite H in H0.
    pose proof (Nat.mod_upper_bound b a Ha) as H1. rewrite <- H0 in H1.
    contradict H1. apply Nat.lt_irrefl.
  - apply Nat.mod_small in H. intro H0. rewrite H in H0.
    pose proof (Nat.mod_upper_bound a b Hb) as H1. rewrite H0 in H1.
    contradict H1. apply Nat.lt_irrefl.
Qed.

(*|
In conclusion, we have emphasized the importance of inductive types to
enumerate all elements of a set (for instance, natural numbers).
However, we are not restricted to the standard encoding of the set and
are able to introduce own principles for the enumeration. But we need
always keep in mind that such a procedure should be decidable. In
contrast, non-decidable procedures are propositions (``Prop``) and not
the subject for case analysis (due to the lack of `excluded-middle law
<https://en.wikipedia.org/wiki/Law_of_excluded_middle>`__ in
constructive logic).

----

Below are appropriate examples found on `Stack Overflow
<https://stackoverflow.com/>`__:

1. `<../examples/contradiction-on-natural-numbers-zero-test.html>`__
2. `<../examples/coq-how-to-prove-if-statements-involving-strings.html>`__
3. `<../examples/coq-how-to-prove-max-a-b-ab.html>`__
4. `<../examples/coq-leb-does-not-give-me-an-hypothesis-after-case-or-induction.html>`__
5. `<../examples/finding-a-well-founded-relation-to-prove-termination-of-a-function-that-stops-de.html>`__
6. `<../examples/how-does-decidable-equality-works-with-list-remove.html>`__
7. `<../examples/pattern-matching-with-even-and-odd-cases.html>`__
8. `<../examples/prove-that-the-only-zero-length-vector-is-nil.html>`__
|*)
