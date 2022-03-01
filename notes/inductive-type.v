(*|
#######################################################
Inductive type not restricted to mathematical induction
#######################################################

Many properties of natural numbers are proven using `mathematical
induction <https://en.wikipedia.org/wiki/Mathematical_induction>`__.
This principle gives a proof that statement :math:`P(n)` holds for
every natural number :math:`n = 0, 1, 2, \ldots`, and consists of two
steps:

1. The **initial** or **base case**: prove that the statement holds
   for :math:`0`.
2. The **induction step**: prove that for every :math:`n`, if the
   statement holds for :math:`n`, then it holds for :math:`n + 1`.

In Coq, natural numbers encoded using `Peano's encoding
<https://en.wikipedia.org/wiki/Peano_axioms>`__ are given by the
following `inductive type
<https://en.wikipedia.org/wiki/Inductive_type>`__:
|*)

Print nat. (* .unfold .messages *)

(*|
Here, a natural number is created either from the constant ``O`` or by
applying the function ``S`` to another natural number. ``S`` is the
successor function which represents adding 1 to a number. Thus, ``O``
is zero, ``S O`` is one, ``S (S O)`` is two, ``S (S (S O))`` is three,
and so on.

As most inductive types, ``nat`` comes with a function to prove its
properties:
|*)

Check nat_ind. (* .unfold .messages *)

(*|
Not surprising that that is mathematical induction. Example of proof
by induction using ``induction`` tactic:
|*)

Require Import PeanoNat Lia.

Lemma pow_2_bound : forall n : nat, S n <= 2 ^ n.
Proof.
  intro n. induction n.
  - easy.
  - rewrite Nat.pow_succ_r; [| apply Nat.le_0_l].
    apply Nat.mul_le_mono_l with (p:=2) in IHn.
    apply (Nat.le_trans _ (2 * S n)); auto. lia.
Qed.

(*|
Albeit mathematical induction is a very natural way of proving
properties about natural numbers, its applicability to most cases is
overemphasized. Just try to prove by induction the following lemma:
|*)

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
