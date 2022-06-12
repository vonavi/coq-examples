(*|
###############################################################################
Why does use of Coq's ``setoid_replace ... by`` clause need an extra ``idtac``?
###############################################################################

:Link: https://stackoverflow.com/q/31279517
|*)

(*|
Question
********

I encountered a strange situation using ``setoid_replace`` where a
proof step of the form:

.. coq:: none
|*)

Require Import QArith.
Open Scope Q.

Lemma rearrange_eq_r a b c d :
  a == b -> b + d == a + c -> c == d.
Proof.
  intro a_eq_b. rewrite a_eq_b. symmetry. now apply Qplus_inj_l with (z := b).
Qed.

Ltac rearrange :=
  match goal with
  | [ H : _ == _ |- _ == _ ] => apply rearrange_eq_r with (1 := H); ring
  end.

Lemma test_rearrange a b c d e (H0 : e < b) (H1 : b + c == a + d) :
  e < a - c + d.
Proof.

(*||*)

  Fail setoid_replace (a - c + d) with b by rearrange. (* .unfold .in .messages *)

(*| but after appending an extra ``idtac`` to the tactic: |*)

  setoid_replace (a - c + d) with b by (rearrange; idtac).

(*|
the proof succeeds. My understanding of ``idtac`` was that it was
essentially a no-op. Why does the presence of ``idtac`` make a
difference here?

Here's the full code. I'm using Coq 8.4pl6 through Proof General.
|*)

Reset Initial. (* .none *)
Require Import QArith.
Open Scope Q.

Lemma rearrange_eq_r a b c d :
  a == b -> b + d == a + c -> c == d.
Proof.
  intro a_eq_b. rewrite a_eq_b. symmetry. now apply Qplus_inj_l with (z := b).
Qed.

Ltac rearrange :=
  match goal with
  | [ H : _ == _ |- _ == _ ] => apply rearrange_eq_r with (1 := H); ring
  end.

Lemma test_rearrange a b c d e (H0 : e < b) (H1 : b + c == a + d) :
  e < a - c + d.
Proof.
  (* Why is the extra 'idtac' required in the line below? *)
  setoid_replace (a - c + d) with b by (rearrange; idtac).
  assumption.
Qed.

(*|
Note: as Matt observes, ``idtac`` doesn't seem to be special here: it
seems that any tactic (including ``fail``!) can be used in place of
``idtac`` to make the proof succeed.

----

**A (Matt):** Strangely enough sequencing ``rearrange`` with anything
seems to work. For example, I get the same result when I do
``setoid_replace (a - c + d) with b by (rearrange; fail).`` or
``setoid_replace (a - c + d) with b by (rearrange; exfalso).`` or
``setoid_replace (a - c + d) with b by (rearrange; auto).`` Very
odd...
|*)

(*|
Answer
******

Thanks to Jason Gross on the Coq bug tracker for explaining this. This
has to do with order of evaluation in the Ltac tactic language. In the
failing case, the match in ``rearrange`` is being applied to the
inequality in the immediate goal rather than to the equality generated
by ``setoid_replace``. Here's Jason's response on the bug report:

    This is because the ``match`` is evaluated before the
    ``setoid_replace`` is run. It is one of the unfortunate trip-ups
    of Ltac that things like ``match`` and ``let ... in ...`` are
    evaluated eagerly until a statement with semicolons, or other
    non-match non-let-in statement is reached. If you add ``idtac;``
    before the ``match`` in ``rearrange``, your problem will go away.
|*)
