(*|
Vector : t A n = t A (n+0)?
===========================

:Link: https://stackoverflow.com/questions/64225642/vector-t-a-n-t-a-n0
|*)

(*|
Question
--------

I want trivial lemma below.
|*)

Require Import Coq.Vectors.Vector.

Lemma one (A:Type) (n:nat): t A n = t A (n+0).
Proof.
  induction n. reflexivity.
Abort.

(*| How do I simplify ``(n+0)`` to ``n``? |*)

(*|
Answer
------

When you want to prove an equality between complex structures it can
often be useful to use the ``f_equal`` tactic which will ask to prove
that the subterms are equal. For instance here it turns ``t A n = t A
(n+0)`` into ``n = n + 0``. Once you have this, you can use the very
useful ``lia`` tactic to deal with equalities on natural numbers.
|*)

Require Import Coq.Vectors.Vector.
From Coq Require Import Lia.

Lemma one (A:Type) (n:nat): t A n = t A (n+0).
Proof.
  f_equal. lia.
Qed.

(*|
(Notice that you have to require the ``Lia`` module to use ``lia``.)

In some cases you will not be proving an equality directly so it might
be useful to replace ``n+0`` with ``n``:
|*)

Reset one. (* .none *)
Lemma one (A:Type) (n:nat): t A n = t A (n+0).
Proof.
  (* f_equal. lia. *)
  replace (n + 0) with n by lia.
  reflexivity.
Qed.
