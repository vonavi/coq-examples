(*|
###################################################
How to unfold a recursive function just once in Coq
###################################################

:Link: https://stackoverflow.com/q/24304345
|*)

(*|
Question
********

Here is a recursive function ``all_zero`` that checks whether all
members of a list of natural numbers are zero:
|*)

Require Import Lists.List.
Require Import Arith.

Fixpoint all_zero (l : list nat) : bool :=
  match l with
  | nil => true
  | n :: l' => andb (beq_nat n 0) (all_zero l')
  end.

(*| Now, suppose I had the following goal |*)

Goal forall n l', true = all_zero (n :: l').

(*|
And I wanted to use the ``unfold`` tactic to transform it to

.. coq:: none
|*)

  intros. unfold all_zero. fold all_zero.

(*||*)

  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
Unfortunately, I can't do it with a simple ``unfold all_zero`` because
the tactic will eagerly find and replace all instances of
``all_zero``, including the one in the once-unfolded form, and it
turns into a mess. Is there a way to avoid this and unfold a recursive
function just once?

I know I can achieve the same results by proving an ad hoc equivalence
with ``assert (...) as X``, but it is inefficient. I'd like to know if
there's an easy way to do it similar to ``unfold``.

----

**A:** You could also prove
|*)

Goal forall n l, all_zero (n :: l) = andb (beq_nat n 0) (all_zero l).
Admitted. (* .none *)

(*| and rewrite with that. |*)

(*|
Answer (Volker Stolz)
*********************

Try
|*)

Goal forall n l', true = all_zero (n :: l'). (* .none *)
  unfold all_zero. fold all_zero.

(*| At least here for me that yields: |*)

  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
----

**Q:** ``unfold`` followed by ``fold`` indeed works for ``all_zero``,
but not for polymorphic recursive functions. Here's one example:
|*)

Fixpoint none {X : Type} (t : X -> bool) (l : list X) : bool :=
  match l with
  | nil => true
  | h :: l' => andb (negb (t h)) (none t l')
  end.

(*|
``unfold none`` followed by ``fold none`` results in the following
error message:

.. coq:: none
|*)

Goal forall (X : Type) (t : X -> bool) h l',
    true = none t l' -> false = t h -> true = none t (h :: l').
  intros.

(*||*)

  unfold none. (* .none *) Fail fold none. (* .unfold .messages *)

(*|
So I think a generic solution for unfolding a recursive function once
will have to avoid using ``unfold`` in the first place, unless there
is some way to supply parametric information to ``fold``.

**A:** You can make the implicit parameter ``X`` of ``none`` explicit
by writing ``@none``. If you write ``fold @none.``, then Coq is able
to give the argument explictly and searches for a suitable ``X`` in
the current context, just as it does for the other all-quantified
variables ``t`` and ``l``. If there is ambiguity you can also specify
the corresponding variables explicitly, i.e. ``fold (@none X)``.
|*)

(*|
Answer (Virgile)
****************

It seems to me that ``simpl`` will do what you want. If you have a
more complicated goal, with functions that you want to apply and
functions that you want to keep as they are, you might need to use the
various options of the ``cbv`` tactic (see
http://coq.inria.fr/distrib/current/refman/Reference-Manual010.html#hevea_tactic127).
|*)
