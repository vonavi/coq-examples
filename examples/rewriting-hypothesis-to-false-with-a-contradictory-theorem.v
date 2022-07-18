(*|
##########################################################
Rewriting hypothesis to false with a contradictory theorem
##########################################################

:Link: https://stackoverflow.com/q/71834647
|*)

(*|
Question
********

I want to show that

.. code-block:: coq

    [seq q x t | x <- iota 0 (t + 1)] != [::]

I decided to destruct ``iota 0 (t + 1)`` because I have a lemma that
says:

.. code-block:: coq

    iota 0 (t + 1) != [::]

So the first case of destruct should have ``iota 0 (t + 1) = [::]``
which by the theorem mentioned is false, and I can discriminate. How
can I rewrite the equation in the first destruct case using the lemma?
I cannot figure it out.
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

You do not need to destruct. Note that ``iota`` is defined by
recursion on its second variable. Your current goal cannot be
simplified because ``t + 1`` does not start with a constructor.
However, you can do ``by rewrite addn1`` to put it in a form where it
can be solved.
|*)

(*|
Answer (Pierre Jouvelot)
************************

In addition to computation, as Arthur suggests, you can sometimes use
contraposition to deal with non-equalities (do ``Search "contra"`` for
variant versions).

For instance, in your case, you can show, if you add some injectivity
constraint:
|*)

From mathcomp Require Import all_ssreflect. (* .none *)
Lemma foo (q : nat -> nat -> nat) t (injq : injective (q ^~ t)) :
  iota 0 (t + 1) != [::] -> [seq q x t | x <- iota 0 (t + 1)] != [::].
Proof.
  apply: contra_neq.
  rewrite [RHS](_ : [::] = [seq q x t | x <- [::]]) //.
  exact: inj_map.
Qed.
