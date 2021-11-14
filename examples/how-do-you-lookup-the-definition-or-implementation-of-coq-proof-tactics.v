(*|
How do you lookup the definition or implementation of Coq proof tactics?
========================================================================

https://stackoverflow.com/questions/63823528/how-do-you-lookup-the-definition-or-implementation-of-coq-proof-tactics
|*)

(*|
Question
--------

I am looking at `this
<https://github.com/coq/coq/blob/cdfe69d6da6b32338ba74c9f599c74389089c9dd/theories/Numbers/Natural/Abstract/NAdd.v#L49-L57>`_:

.. coq:: none
|*)

Require Export NBase.

Module NAddProp (Import N : NAxiomsMiniSig').
Include NBaseProp N.

Theorem eq_add_0 : forall n m, n + m == 0 <-> n == 0 /\ m == 0.
Proof.
  intros n m; induct n.
  nzsimpl; intuition.
  intros n IH. nzsimpl.
  setoid_replace (S (n + m) == 0) with False by
      (apply neg_false; apply neq_succ_0).
  setoid_replace (S n == 0) with False by
      (apply neg_false; apply neq_succ_0). tauto.
Qed.

Theorem eq_add_succ :
  forall n m, (exists p, n + m == S p) <->
              (exists n', n == S n') \/ (exists m', m == S m').
Proof.
  intros n m; cases n.
  split; intro H.
  destruct H as [p H]. rewrite add_0_l in H; right; now (exists p).
  destruct H as [[n' H] | [m' H]].
  symmetry in H; false_hyp H neq_succ_0.
  exists m'; now rewrite add_0_l.
  intro n; split; intro H.
  left; now (exists n).
  exists (n + m); now rewrite add_succ_l.
Qed.

(*||*)

Theorem eq_add_1 : forall n m,
    n + m == 1 -> n == 1 /\ m == 0 \/ n == 0 /\ m == 1.
Proof.
  intros n m. rewrite one_succ. intro H.
  assert (H1 : exists p, n + m == S p) by now (exists 0).
  apply eq_add_succ in H1. destruct H1 as [[n' H1] | [m' H1]].
  left. rewrite H1 in H; rewrite add_succ_l in H; apply succ_inj in H.
  apply eq_add_0 in H. destruct H as [H2 H3]; rewrite H2 in H1; now split.
  right. rewrite H1 in H; rewrite add_succ_r in H; apply succ_inj in H.
  apply eq_add_0 in H. destruct H as [H2 H3]; rewrite H3 in H1; now split.
Qed.

(*| .. coq:: none |*)
End NAddProp.

(*|
How do I find what the thing like `intros` or `destruct` mean
*exactly*, like looking up an implementation (or if not possible, a
definition)? What is the way to do this efficiently?
|*)

(*|
Answer (Blaisorblade)
---------------------

The answer differs for primitive and user-defined tactics. However,
the proof script you show uses almost no user-defined tactics, except
`now`, which is a notation for the `easy` tactic.

For user-defined tactics.
~~~~~~~~~~~~~~~~~~~~~~~~~

For tactics defined as `Ltac foo args := body.` you can use `Print
Ltac foo` (e.g. `Print Ltac easy.`). AFAIK, that does not work for
tactics defined by `Tactic Notation`. In both cases, I prefer to look
at the sources (which I find via `grep`).

For primitive tactics
~~~~~~~~~~~~~~~~~~~~~

- There is the Coq reference manual
  (https://coq.inria.fr/distrib/current/refman/coq-tacindex.html),
  which does not have complete specification but is usually the
  closest approximation. It’s not very accessible, so you should first
  refer to one of the many Coq tutorials or introductions, like
  Software Foundations.
- There is the actual Coq implementation, but that’s not very helpful
  unless you’re a Coq implementer.
|*)

(*|
Answer (Arthur Azevedo De Amorim)
---------------------------------

As Blaisorblade mentioned, it can be difficult to understand exactly
what tactics are doing, and it is easier to look at the reference
manual to find out how to use them. However, at a conceptual level,
tactics are not that complicated. Via the `Curry-Howard correspondence
<https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence>`_,
Coq proofs are represented using the same functional language you use
to write regular programs. Tactics like `intros` or `destruct` are
just metaprograms that write programs in this language.

For instance, suppose that you need to prove `A -> B`. This means that
you need to write a program with a function type `A -> B`. When you
write `intros H.`, Coq builds a partial proof `fun (H : A) => ?`,
where the `?` denotes a hole that should have type `B`. Similarly,
`destruct` adds a `match` expression to your proof to do case
analysis, and asks you to produce proofs for each `match` branch. As
you add more tactics, you keep filling in these holes until you have a
complete proof.

The language of Coq is quite minimal, so there is only so much that
tactics can do to build a proof: function application and abstraction,
constructors, pattern matching, etc. In principle, it would be
possible to have only a handful of tactics, one for each syntactic
construct in Coq, and this would allow you to build *any* proof! The
reason we don't do this is that using these core constructs directly
is too low level, and tactics use automated proof search, unification
and other features to simplify the process of writing a proof.
|*)
