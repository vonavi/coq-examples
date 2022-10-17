(*|
###########################################
How to repeat proof tactics in case in Coq?
###########################################

:Link: https://stackoverflow.com/q/43823343
|*)

(*|
Question
********

I would like to extend the exercise 6.10 in Coq'Art by adding a
theorem that for all months which are not January, ``is_January`` will
equal false.

My definition of months looks like this:
|*)

Inductive month : Set :=
| January : month
| February : month
| March : month
| April : month
| May : month
| June : month
| July : month
| August : month
| September : month
| October : month
| November : month
| December : month.

(*| My definition of ``is_January`` looks like this: |*)

Definition is_January (m : month) : Prop :=
  match m with
  | January => True
  | _       => False
  end.

(*| I am doing the following to test that it is correct. |*)

Eval compute in (is_January January).
Eval compute in (is_January December).

Theorem is_January_eq_January :
  forall m : month, m = January -> is_January m = True.
Proof.
  intros m H. rewrite H. compute. reflexivity.
Qed.

(*| I am not very happy with this theorem's proof. |*)

Theorem is_January_neq_not_January :
  forall m : month, m <> January -> is_January m = False.
Proof.
  induction m.
  - contradiction.
  - intro H. simpl. reflexivity.
  - intro H. simpl. reflexivity.
  - intro H. simpl. reflexivity.
  - intro H. simpl. reflexivity.
  - intro H. simpl. reflexivity.
  - intro H. simpl. reflexivity.
  - intro H. simpl. reflexivity.
  - intro H. simpl. reflexivity.
  - intro H. simpl. reflexivity.
  - intro H. simpl. reflexivity.
  - intro H. simpl. reflexivity.
Qed.

(*|
Is there anyway in Coq to repeat the ``- intro H. simpl.
reflexivity.`` case proof for non-January months (so I would only have
two - or something similar so I do not have to repeat myself)? Or am I
just completely going about this proof the wrong way?

----

**A:** You probably want your ``is_January`` function to return
``bool``, not ``Prop``. ``Prop`` is a type of logical propositions
(there are plenty of them), so it's not supposed to be used as a usual
boolean-like type with only two values (``true`` and ``false``).
|*)

(*|
Answer
******

One way to do this is to
|*)

Reset is_January_neq_not_January. (* .none *)
Theorem is_January_neq_not_January :
  forall m : month, m <> January -> is_January m = False.
Proof.
  induction m; try reflexivity. contradiction.
Qed.

(*|
- ``simpl`` is implicit in ``reflexivity`` and hence unnecessary.
- ``t1 ; t2`` applies tactic ``t2`` to all branches created by the
  application of tactic ``t1``.
- ``try t`` tries to apply tactic ``t`` (as the name implies) or does
  nothing if ``t`` fails.

What this does is run ``induction`` as before and then immediately run
``reflexivity`` on all branches (which works on & solves all but the
January branch). After that, you're left with that single branch,
which can be solved by ``contradiction`` as before.

Other potentially useful constructions for more complex situations are

- ``(t1 ; t2)`` which groups tactics ``t1`` and ``t2``,

- ``t1 | t2``, ``t1 || t2``, ``t1 + t2`` which are variations on "try
  ``t1`` and if that fails / doesn't do anything useful / ..., do
  ``t2`` instead",

- ``fail`` which explicitly fails (this is useful if you want to
  un-do/reset what happened in a branch)

  (As a complex example from one of my proofs, consider ``try (split;
  unfold not; intro H'; inversion H'; fail)``. This attempts to create
  several sub-branches (``split``) hoping that they're all
  contradictory and can be solved by ``inversion H'``. If that doesn't
  work, the ``inversion``\ s would just create a big mess, so it
  explicitly ``fail``\ s in order to un-do the effects of the tactic
  chain. End result is that many boring cases get solved automatically
  and the interesting ones remain unchanged for manual solving.)

- and many more – look at `Chapter 9 of the Coq Reference Manual ("The
  tactic language")
  <https://coq.inria.fr/refman/Reference-Manual011.html>`__ for longer
  descriptions of these and many other useful constructions.

----

**A:** ``now destruct m.`` will do the trick as well -- it's
equivalent to ``destruct m; easy.`` and the `easy
<https://coq.inria.fr/library/Coq.Init.Tactics.html>`__ tactic is
clever enough to use ``contradiction`` and ``reflexivity``.
|*)
