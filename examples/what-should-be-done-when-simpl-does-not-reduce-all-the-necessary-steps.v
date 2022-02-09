(*|
###########################################################################
What should be done when ``simpl`` does not reduce all the necessary steps?
###########################################################################

:Link: https://stackoverflow.com/q/55879360
|*)

(*|
Question
********

The following example is from chapter Poly of the Software Foundations
book.

.. coq:: none
|*)

Require Import List.
Import ListNotations.
Definition fold {A B} := @fold_left A B.

(*||*)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun n _ => S n) l 0.

Theorem fold_length_correct : forall X (l : list X),
    fold_length l = length l.
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - simpl. (* .unfold *)
Abort. (* .none *)

(*|
I expected it to simplify a step here on the left side. It certainly
should be able to.
|*)

Theorem fold_length_correct : forall X (l : list X),
    fold_length l = length l.
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - simpl. rewrite <- IHl. simpl. (* .unfold *)
Abort. (* .none *)

(*|
During the running of the tests I had an issue where ``simpl`` would
refuse to dive in, but ``reflexivity`` did the trick, so I tried the
same thing here and the proof succeeded.

Note that one would not expect ``reflexivity`` to pass given the state
of the goal, but it does. In this example it worked, but it did force
me to do the rewrite in the opposite direction of what I intended
originally.

Is it possible to have more control over ``simpl`` so that it does the
desired reductions?
|*)

(*|
Answer
******

For the purposes of this answer, I'll assume the definition of
``fold`` is something along the lines of

.. coq:: none
|*)

Reset Initial.
Require Import List.
Import ListNotations.

(*||*)

Fixpoint fold {A B: Type} (f: A -> B -> B) (u: list A) (b: B): B :=
  match u with
  | [] => b
  | x :: v => f x (fold f v b)
  end.

(*|
(basically ``fold_right`` from the standard library). If your
definition is substantially different, the tactics I recommend might
not work.

----

The issue here is the behavior of ``simpl`` with constants that have
to be unfolded before they can be simplified. From `the documentation
<https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.simpl>`__:

    Notice that only transparent constants whose name can be reused in
    the recursive calls are possibly unfolded by ``simpl``. For
    instance a constant defined by ``plus' := plus`` is possibly
    unfolded and reused in the recursive calls, but a constant such as
    ``succ := plus (S O)`` is never unfolded.

This is a bit hard to understand, so let's use an example.
|*)

Definition add_5 (n: nat) := n + 5.

Goal forall n: nat, add_5 (S n) = S (add_5 n).
Proof.
  intro n. simpl. unfold add_5. simpl. exact eq_refl.
Qed.

(*|
You'll see that the first call to ``simpl`` didn't do anything, even
though ``add_5 (S n)`` could be simplified to ``S (n + 5)``. However,
if I ``unfold add_5`` first, it works perfectly. I think the issue is
that ``plus_5`` is not directly a ``Fixpoint``. While ``plus_5 (S n)``
is equivalent to ``S (plus_5 n)``, that isn't actually the definition
of it. So Coq doesn't recognize that its "name can be reused in the
recursive calls". ``Nat.add`` (that is, "``+``") is defined directly
as a recursive ``Fixpoint``, so ``simpl`` does simplify it.

The behavior of ``simpl`` can be changed a little bit (see the
documentation again). As Anton mentions in the comments, you can use
the ``Arguments`` vernacular command to change when ``simpl`` tries to
simplify. ``Arguments fold_length _ _ /.`` tells Coq that
``fold_length`` should be unfolded if at least two arguments are
provided (the slash separates between the required arguments on the
left and the unnecessary arguments on the right) [1]_.

A simpler tactic to use if you don't want to deal with that is ``cbn``
which works here by default and works better in general. Quoting from
`the documentation
<https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.cbn>`__:

    The ``cbn`` tactic is claimed to be a more principled, faster and
    more predictable replacement for ``simpl``.

Neither ``simpl`` with ``Arguments`` and a slash nor ``cbn`` reduce
the goal to quite what you want in your case, since it'll unfold
``fold_length`` but not refold it. You could recognize that the call
to ``fold`` is just ``fold_length l`` and refold it with ``fold
(fold_length l)``.

Another possibility in your case is to use the ``change`` tactic. It
seemed like you knew already that ``fold_length (a :: l)`` was
supposed to simplify to ``S (fold_length l)``. If that's the case, you
could use ``change (fold_length (a :: l)) with (S (fold_length l)).``
and Coq will try to convert one into the other (using only the basic
conversion rules, not equalities like ``rewrite`` does).

After you've gotten the goal to ``S (fold_length l) = S (length l)``
using either of the above tactics, you can use ``rewrite -> IHl.``
like you wanted to.

----

.. [1] I thought the slashes only made ``simpl`` unfold things *less*,
   which is why I didn't mention it before. I'm not sure what the
   default actually is, since putting the slash anywhere seems to make
   ``simpl`` unfold ``fold_length``.
|*)
