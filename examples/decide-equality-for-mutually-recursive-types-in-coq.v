(*|
########################################################
``decide equality`` for Mutually Recursive Types in Coq?
########################################################

:Link: https://stackoverflow.com/questions/48268929/decide-equality-for-mutually-recursive-types-in-coq
|*)

(*|
Question
********

Is there any way to use the ``decide equality`` tactic with mutually
recursive types in Coq?

For example, if I've got something like this:
|*)

Inductive LTree : Set :=
| LNil
| LNode (x: LTree) (y: RTree)
with RTree : Set :=
| RNil
| RNode (x: LTree) (y: RTree).

Lemma eq_LTree : forall (x y : LTree), {x = y} + {x <> y}.
Proof.
  decide equality; auto.

(*| This leaves me with the goal: |*)

  Show 1. (* .unfold .goals *)
Abort. (* .none *)

(*|
But I can't solve that until I've derived equality for ``RTree``,
which will have the same problem.
|*)

(*|
Answer
******

You can use ``decide equality`` in this case if you prove the two
lemmas for ``LTrees`` and ``RTrees`` simultaneously:
|*)

Lemma eq_LTree : forall (x y : LTree), {x = y} + {x <> y}
with  eq_RTree : forall (x y : RTree), {x = y} + {x <> y}.
Proof.
  - decide equality.
  - decide equality.
Qed.

(*|
----

**Q:** This is strange, ``Guarded`` complains after the first ``decide
equality``, but then ``Qed`` is not rejected.

**A:** Never mind, I found a `thread
<https://sympa.inria.fr/sympa/arc/coq-club/2011-11/msg00297.html>`__
on coq-club discussing this particular problem.
|*)
