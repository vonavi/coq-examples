(*|
####################################
Split conjunction goal into subgoals
####################################

:Link: https://stackoverflow.com/q/43945888
|*)

(*|
Question
********

Consider the following toy exercise:
|*)

Theorem swap_id : forall (m n : nat), m = n -> (m, n) = (n, m).
Proof.
  intros m n H.

(*| At this point I have the following: |*)

  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
I would like to split the goal into two subgoals, ``m = n`` and ``n =
m``. Is there a tactic which does that?
|*)

(*|
Answer
******

Solve using the `f_equal
<https://coq.inria.fr/refman/Reference-Manual010.html#hevea_tactic169>`__
tactic:
|*)

Theorem test : forall (m n : nat), m = n -> (m, n) = (n, m).
Proof.
  intros m n H. f_equal.

(*| With state: |*)

  Show. (* .unfold .messages *)

(*|
----

**A:** A comment about the reason ``f_equal`` works: if we unfold some
notations, we'll get from the goal ``(m, n) = (n, m)`` to ``pair m n =
pair n m``, where ``pair`` is the only constructor of the ``prod``
datatype. At this point it should be obvious why ``f_equal`` splits
the goal into two subgoals.
|*)
