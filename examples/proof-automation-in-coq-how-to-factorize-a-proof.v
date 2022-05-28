(*|
################################################
Proof automation in Coq how to factorize a proof
################################################

:Link: https://stackoverflow.com/q/34581945
|*)

(*|
Question
********

I'm following the book Software Foundation and I'm on the chapter
named "Imp".

The authors expose a small language that is the following:
|*)

Inductive aexp : Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

(*| Here is the function to evaluate these expressions: |*)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => aeval a1 + aeval a2
  | AMinus a1 a2 => aeval a1 - aeval a2
  | AMult a1 a2 => aeval a1 * aeval a2
  end.

(*|
The exercise is to create a function that optimize the evaluation. For
example:

.. code-block:: coq

    APlus a (ANum 0) --> a

Here there is my optimize function:
|*)

Fixpoint optimizer_a (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimizer_a e2
  | APlus e1 (ANum 0) => optimizer_a e1
  | APlus e1 e2 => APlus (optimizer_a e1) (optimizer_a e2)
  | AMinus e1 (ANum 0) => optimizer_a e1
  | AMinus e1 e2 => AMinus (optimizer_a e1) (optimizer_a e2)
  | AMult (ANum 1) e2 => optimizer_a e2
  | AMult e1 (ANum 1) => optimizer_a e1
  | AMult e1 e2 => AMult (optimizer_a e1) (optimizer_a e2)
  end.

(*|
And now, I would prove that the optimization function is sound:
|*)

Theorem optimizer_a_sound : forall a, aeval (optimizer_a a) = aeval a.
Abort. (* .none *)

(*|
This proof is quite difficult. So I tried to decompose the proof using
some lemmas.

Here is one lemma:
|*)

Lemma optimizer_a_plus_sound : forall a b,
    aeval (optimizer_a (APlus a b)) =
      aeval (APlus (optimizer_a a) (optimizer_a b)).
Abort. (* .none *)

(*|
I have the proof, but it is boring. I do an induction on ``a`` and
then, for every case, I destruct ``b`` and destruct the ``aexp`` to
handle the case when ``b`` is ``0``.

I need to do that because

.. code-block::

    n + 0 = n

doesn't reduce automatically, we need a theorem which is ``plus_0_r``.

Now, I wonder, how can I build a better proof with Coq in order to
avoid some boring repetitions during the proof.

Here is my proof for this lemma:

http://pastebin.com/pB76JFGv

I think I should use ``Hint Rewrite plus_0_r`` but I don't know how.

By the way, I'm also interested to know some tips in order to show the
initial theorem (the soudness of my optimization function).
|*)

(*|
Answer (larsr)
**************

When you are working with induction on data structures and need to
consider cases, here is one method I found useful to consider the
cases of a variable ``X``, get rid of the impossible cases, and solve
the trivial ones.

.. code-block:: coq

    destruct X; try congruence; auto.

In your case, we can use it to prove useful rewrite lemmas about the
``optimization_a`` function.
|*)

Lemma opt1 : forall a b, a = ANum 0 -> optimizer_a (APlus a b) = optimizer_a b.
  intros.
  destruct a; try congruence; auto;
    destruct n; try congruence; auto.
Qed.

Lemma opt2 : forall a b, b = ANum 0 -> optimizer_a (APlus a b) = optimizer_a a.
  intros.
  destruct a; try congruence; auto;
    destruct b; try congruence; auto;
    destruct n; try congruence; auto;
    destruct n0; try congruence; auto.
Qed.

Lemma opt3 : forall a b,
    a <> ANum 0 -> b <> ANum 0 ->
    optimizer_a (APlus a b) = APlus (optimizer_a a) (optimizer_a b).
Proof.
  intros.
  destruct a; try congruence; auto;
    destruct b; try congruence; auto;
    destruct n; try congruence; auto;
    destruct n0; try congruence; auto.
Qed.

(*|
Actually, these proofs can also be written more compactly as
one-liners with some insight and Ltac-fu, but my point here is to show
that it can also be used almost mechanically.

Also note the use of semicolon instead of point to string together the
tactics so that they work on all the remaining goals after each step.

Anyway, now that we have these lemmas, we can consider the different
cases (Is ``a = ANum 0`` or not? Is ``b``?), and just rewrite. To
consider the cases, we need one more lemma that states that ``a`` is
either ``ANum 0`` or it isn't.
|*)

Lemma ANum0_dec : forall a, {a = ANum 0} + {a <> ANum 0}.
  destruct a; try destruct n; try (right; discriminate); left; auto.
Qed.

(*|
We can destruct ``ANum0_dec a`` and get either ``a = ANum 0`` in the
context, or ``a <> ANum 0`` in the context.
|*)

Require Import Arith. (* for "auto with arith" to handle n = n + 0 *)

Lemma optimizer_a_plus_sound : forall a b,
    aeval (optimizer_a (APlus a b)) =
      aeval (APlus (optimizer_a a) (optimizer_a b)).
Proof.
  intros a b.
  destruct (ANum0_dec a);  destruct (ANum0_dec b).
  - rewrite opt1; subst; auto.
  - rewrite opt1; subst; auto.
  - rewrite opt2; subst; simpl; auto with arith.
  - rewrite opt3; subst; auto.
Qed.

(*|
Answer (larsr)
**************

If you use the technique above, you can define your own tactical, so
you don't have to type as much. And since the proofs are very short,
you could do without the lemmas. (I called the tactical ``dca`` for
``destruct``-``congruence``-``auto``.)

The shorter proof is not that readable, but it is essentially:
consider the cases of the variables.
|*)

Reset ANum0_dec. (* .none *)
Lemma ANum0_dec : forall a, {a = ANum 0} + {a <> ANum 0}.
  destruct a; try destruct n; try (right; discriminate); left; auto.
Qed.

Require Import Arith.

Ltac dca v := destruct v; try congruence; auto.

Lemma optimizer_a_plus_sound : forall a b,
    aeval (optimizer_a (APlus a b)) =
      aeval (APlus (optimizer_a a) (optimizer_a b)).
Proof.
  intros a b.
  destruct (ANum0_dec a), (ANum0_dec b).
  - dca a; dca n.
  - dca a; dca n0.
  - dca b; dca n0; dca a; simpl; auto with arith; dca n0.
  - dca a; dca b; dca n1; dca n2.
Qed.

(*| Then use it |*)

Theorem optimizer_a_sound : forall a, aeval (optimizer_a a) = aeval a.
  induction a.
  - auto.
  - rewrite optimizer_a_plus_sound; simpl; auto.
  - (* ... and so on for Minus and Mult *)

(*|
You could probably also do the full proof in this compact form.
|*)
