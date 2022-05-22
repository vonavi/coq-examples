(*|
##############################################
How to add to both sides of an equality in Coq
##############################################

:Link: https://stackoverflow.com/q/36996408
|*)

(*|
Question
********

This seems like a really simple question, but I wasn't able to find
anything useful.

.. coq:: none
|*)

Goal forall n x : nat, n - x = n -> (n - x) + x = n + x.
Proof.
  intros.

(*| I have the statement |*)

  Show. (* .unfold .hyps *)

(*| and would like to prove |*)

  Show. (* .unfold .goals .no-hyps *)

(*| I haven't been able to find what theorem allows for this. |*)

(*|
Answer (Vinz)
*************

You should have a look at the ``rewrite`` tactic (and then maybe
``reflexivity``).

EDIT: more info about rewrite:

- You can ``rewrite H`` (``rewrite -> H``) to rewrite from left to
  right
- You can ``rewrite <- H`` to rewrite from right to left
- You can use the ``pattern`` tactic to only select specific instances
  of the goal to rewrite. For example, to only rewrite the second
  ``n``, you can perform the following steps

  .. code-block:: coq

      pattern n at 2. rewrite <- H.

In your case, the solution is much simpler.

----

**Q:** In that case, how do I rewrite onto only one side of an
equation?

**A:** One can also combine ``pattern n at 2. rewrite <- H.`` into
``rewrite <- H at 2.``
|*)

(*|
Answer (Anton Trunov)
*********************

Building on @gallais' suggestion on using f_equal. We start in the
following state:
|*)

  Show. (* .unfold .messages *)

(*|
1. First variant via "forward" reasoning (where one applies theorems
   to hypotheses) using the ``f_equal`` lemma.
|*)

  Check f_equal. (* .unfold .no-hyps .no-goals *)

(*|
   It needs the function ``f``, so
|*)

  apply f_equal with (f := fun t => t + x) in H.

(*|
   This will give you:
|*)

  Show. (* .unfold .hyps *)

(*|
   This can be solved via ``apply H.`` or ``exact H.`` or
   ``assumption.`` or ``auto.`` ... or some other way which suits you
   the most.

2. Or you can use "backward" reasoning (where one applies theorems to
   the goal). There is also the ``f_equal2`` lemma:
|*)

  Check f_equal2. (* .unfold .no-hyps .no-goals *)

(*|
   We just apply it to the goal, which results in two trivial
   subgoals.
|*)

  Undo. (* .none *)
  apply f_equal2; [assumption | reflexivity].

(*|
   or just
|*)

  Undo. (* .none *)
  apply f_equal2; trivial.

(*|
3. There is also the more specialized lemma ``f_equal2_plus``:

   .. coq::
|*)

  Check f_equal2_plus. (* .unfold .no-hyps .no-goals *)

(*|
   Using this lemma we are able to solve the goal with the following
   one-liner:
|*)

  Undo. (* .none *)
  apply (f_equal2_plus _ _ _ _ H eq_refl).

(*|
----

**A:** Remark that ``apply f_equal with (f := fun t => t + x).`` can
also be used on the goal.

**Q:** Is there a version of ``f_equal`` that works for Setoids?

**A:** To be able to prove the analogous lemma, we must have ``f``
proper, but to prove ``f`` is ``Proper`` we need the lemma. Vicious
circle :) BTW, there is a tactic called ``f_equiv``, which is a setoid
analogue of the ``f_equal`` tactic -- can be useful to do "backward
reasoning".
|*)
