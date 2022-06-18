(*|
###########################
Equality on inductive types
###########################

:Link: https://stackoverflow.com/q/26246441
|*)

(*|
Question
********

How do I prove the following trivial lemma:
|*)

Require Import Vector.

Lemma t0_nil : forall A (x : t A 0), x = nil A.
Proof.
Abort.

(*|
FAQ recommends ``decide equality`` and ``discriminate`` tactics but I
could not find a way to apply either of them. For the reference, here
is inductive definition:
|*)

Print t. (* .unfold .messages *)

(*|
Answer
******

What you want to do is to invert on ``x``. Unfortunately, it turns out
that general inversion of dependently typed hypotheses is undecidable,
see Adam Chlipala's CPDT. You can pattern match on the structure
manually though, e.g. with:
|*)

Lemma t0_nil : forall A (x : t A 0), x = nil A.
Proof.
  intros.
  refine (match x with
          | nil _ => _
          | cons _ _ _ _ => _
          end).
  - reflexivity.
  - exact @id.
Qed.

(*|
In many cases you can also use `the tactic dep_destruct provided by
CPDT
<http://adam.chlipala.net/cpdt/repo/file/977b425331c3/src/CpdtTactics.v>`__.
In that case your proof simply becomes:

.. code-block:: coq

    Require Import CpdtTactics.

    Lemma t0_nil : forall A (x : t A 0), x = nil A.
      intros. dep_destruct x. reflexivity.
    Qed.

----

**A:** An elegant solution by Pierre Boutillier, taken from this
`Coq-club post
<http://coq-club.inria.narkive.com/wrDwvaNY/how-to-prove-that-all-vectors-of-0-length-are-equal-to-vector-nil#post2>`__:
|*)

Reset t0_nil. (* .none *)
Definition t0_nil A (x : t A 0) : x = nil A := match x with nil _ => eq_refl end.
