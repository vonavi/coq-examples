(*|
###################################
Step by step simplification in Coq?
###################################

:Link: https://stackoverflow.com/q/39355817
|*)

(*|
Question
********

Is there a way to simplify one step at a time?

Say you have ``f1 (f2 x)`` both of which can be simplified in turn via
a single ``simpl``, is it possible to simplify ``f2 x`` as a first
step, examine the intermediate result and then simplify ``f1``?

Take for example the theorem:
|*)

Theorem pred_length : forall n : nat, forall l : list nat,
    pred (length (n :: l)) = length l.
Proof.
  intros. simpl. reflexivity.
Qed.

(*|
The ``simpl`` tactic simplifies ``Nat.pred (length (n :: l))`` to
``length l``. Is there a way to break that into a two step
simplification i.e:

.. code-block:: coq

    Nat.pred (length (n :: l)) --> Nat.pred (S (length l)) --> length l
|*)

(*|
Answer (ichistmeinname)
***********************

You can also use ``simpl`` for a specific pattern.
|*)

Reset pred_length. (* .none *)
Theorem pred_length : forall n : nat, forall l : list nat,
    pred (length (n :: l)) = length l.
Proof.
 intros. simpl length. simpl pred. reflexivity.
Qed.

(*|
In case you have several occurrences of a pattern like ``length`` that
could be simplified, you can further restrict the outcome of the
simplification by giving a position of that occurrence (from left to
right), e.g. ``simpl length at 1`` or ``simpl length at 2`` for the
first or second occurrence.

----

**Q:** That's very useful! But I see that this simplifies all what it
is within the pattern. For example ``f (g x)`` with ``simpl f.`` will
also simplify using ``g`` definition. Is is possible to instruct coq,
in this example case, to just use ``f`` definition to simplify, and
let ``g x`` as it is?
|*)

(*|
Answer (Anton Trunov)
*********************

We can turn simplification for ``pred`` off, simplify its argument and
turn it back on:
|*)

Reset pred_length. (* .none *)
Theorem pred_length : forall n : nat, forall l : list nat,
    pred (length (n :: l)) = length l.
Proof.
  intros.
  Arguments pred : simpl never. (* do not unfold pred *)
  simpl.
  Arguments pred : simpl nomatch. (* unfold if extra simplification is possible *)
  simpl.
  reflexivity.
Qed.

(*|
See `§8.7.4
<https://coq.inria.fr/distrib/current/refman/Reference-Manual010.html#Conversion-tactics>`__
of the Reference Manual for more details.
|*)
