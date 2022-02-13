(*|
##########################################################
Why would the tactic ``exact`` be complete for Coq proofs?
##########################################################

:Link: https://stackoverflow.com/q/46386249
|*)

(*|
Question
********

In the question `Is there a minimal complete set of tactics in Coq?
<https://stackoverflow.com/questions/32682544/is-there-a-minimal-complete-set-of-tactics-in-coq>`__,
the answers mentioned that ``exact`` would be enough to prove all
goals. Could someone explain and give an example? For example, how
would the goal ``A \/ B -> B \/ A`` with ``A``, ``B`` being ``Prop``
be proven by merely a bunch of ``exact``? If you have other better
examples, please don't hesitate to answer as well. The point is to
give some explanation on this issue and give a non-trivial example.
|*)

(*|
Answer (ejgallego)
******************

Recall that proofs in Coq are just terms in the (lambda) Calculus of
Inductive Constructions. Thus, your lemma is proven as:
|*)

Lemma test A B : A \/ B -> B \/ A.
Proof.
  exact (fun x => match x with
                  | or_introl p => or_intror p
                  | or_intror p => or_introl p
                  end).
Qed.

(*| which is almost the same as: |*)

Definition test' A B : A \/ B -> B \/ A :=
  fun x => match x with
           | or_introl p => or_intror p
           | or_intror p => or_introl p
           end.

(*|
[they differ in "opacity", don't worry about that, but Coq 8.8 will
likely support the ``Lemma foo := term`` syntax, closer to ``exact
term``.]

A more convenient tactic to build proofs is ``refine``, which allows
you to specify partial terms:
|*)

Lemma test'' A B : A \/ B -> B \/ A.
Proof.
  refine (fun x => _).
  refine (match x with | or_introl _ => _ | or_intror _ => _ end).
  - refine (or_intror a).
  - refine (or_introl b).
Qed.

(*|
In fact, ``refine`` is the basic tactic of the Coq proof engine;
``exact T`` basically executes ``refine T`` and checks that no goals
remain open.
|*)

(*|
Answer (Yves)
*************

Because of its theoretical foundations, the logic of Coq does not rely
on tactics as a primitive way to construct proofs. In fact, you could
use Coq and construct what would be considered as legitimate proofs
without ever using any tactic by using the idiom.
|*)

Lemma test3 A B : A \/ B -> B \/ A.
Proof.
  exact (fun x => match x with
                  | or_introl p => or_intror p
                  | or_intror p => or_introl p
                  end).
Qed.

(*|
So the question of "complete set of tactics" is not completely
meaningful.

On the other hand, tactics have been introduced to make the work
easier. So it is useful to know a *reasonably complete set of tactics*
that makes it possible to perform proofs without having a thorough
knowledge of Coq's theoretical foundations. My favorite set of tactics
is:

- ``intros``, ``apply`` (to deal with universal quantification and
  implication);
- ``destruct`` (to deal with logical connectives ``and``, also written
  ``/\`` and ``or``, also written ``\/``, and existential
  quantification, when in hypotheses);
- ``split`` to deal with ``and`` when in a goal's conclusion;
- ``left``, ``right`` to deal with ``or`` when in a goal's conclusion;
- ``exists`` to deal with an existential quantification when in the
  conclusion;
- ``assert`` to establish intermediate facts (not needed for
  completeness, but it really helps you write more readable proofs);
- ``exact`` and ``assumption`` when what you want to prove is really
  obvious from the context.

When reasoning about natural numbers, you will undoubtedly define
functions by pattern-matching and recursively and reason about their
behavior, so it is important to also know the tactics ``change``,
``simpl``, ``case``, ``case_eq``, ``injection``, and ``discriminate``.
Last, when you start making proofs that are advanced enough you need
tools for automated proofs like ``ring`` and ``lia``.
|*)
