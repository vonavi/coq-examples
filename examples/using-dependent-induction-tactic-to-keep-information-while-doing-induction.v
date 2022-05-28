(*|
##############################################################################
Using ``dependent induction`` tactic to keep information while doing induction
##############################################################################

:Link: https://stackoverflow.com/q/34088140
|*)

(*|
Question
********

I have just run into the issue of the Coq ``induction`` discarding
information about constructed terms while reading a proof from `here
<https://www.cis.upenn.edu/~bcpierce/sf/current/Equiv.html>`__.

The authors used something like:

.. code-block:: coq

    remember (WHILE b DO c END) as cw eqn:Heqcw.

to rewrite a hypothesis ``H`` before the actual induction ``induction
H``. I really don't like the idea of having to introduce a trivial
equality as it looks like black magic.

Some search here in SO shows that actually the ``remember`` trick is
necessary. One answer `here
<https://stackoverflow.com/a/4899467/683218>`__, however, points out
that the new ``dependent induction`` can be used to avoid the
``remember`` trick. This is nice, but the ``dependent induction``
itself now seems a bit magical.

I have a hard time trying to understand how ``dependent induction``
works. The `documentation
<https://coq.inria.fr/refman/Reference-Manual010.html#hevea_tactic78>`__
gives an example where ``dependent induction`` is required:
|*)

Lemma le_minus : forall n : nat, n < 1 -> n = 0.

(*|
I can verify how ``induction`` fails and ``dependent induction`` works
in this case. But I can't use the ``remember`` trick to replicate the
``dependent induction`` result.

What I tried so far to mimic the ``remember`` trick is:
|*)

Reset Initial. (* .none *)
Require Import Coq.Program.Equality.

Lemma le_minus : forall n : nat, n < 1 -> n = 0.
Proof.
  intros n H. (* dependent induction H works*)
  remember (n < 1) as H0. Fail induction H. (* .fails *)

(*|
But this doesn't work. Anyone can explain how ``dependent induction``
works here in terms of the ``remember``-ing?

----

**A:** As indicated in the documentation, dependent induction is
defined in ``Coq.Program.Equality``. You can `dig through its guts
<https://coq.inria.fr/distrib/current/stdlib/Coq.Program.Equality.html>`__
to see how it works.
|*)

(*|
Answer
******

You can do
|*)

Reset Initial. (* .none *)
Require Import Coq.Program.Equality.

Lemma le_minus : forall n : nat, n < 1 -> n = 0.
Proof.
  intros n H.
  remember 1 as m in H. induction H.
  - inversion Heqm. reflexivity.
  - inversion Heqm. subst m.
    inversion H.
Qed.

(*|
As stated `here <https://stackoverflow.com/a/4522477/1633770>`__, the
problem is that Coq cannot keep track of the shape of terms that
appear in the type of the thing you are doing induction on. In other
words, doing induction over the "less than" relation instructs Coq to
try to prove something about a generic upper bound, as opposed to the
specific one you're considering (1).

Notice that it is always possible to prove such goals without
``remember`` or ``dependent induction``, by generalizing your result a
little bit:
|*)

Reset Initial. (* .none *)
Lemma le_minus_aux :
  forall n m, n < m ->
              match m with
              | 1 => n = 0
              | _ => True
              end.
Proof.
  intros n m H. destruct H.
  - destruct n; trivial.
  - destruct H; trivial.
Qed.

Lemma le_minus : forall n, n < 1 -> n = 0.
Proof.
  intros n H.
  apply (le_minus_aux n 1 H).
Qed.
