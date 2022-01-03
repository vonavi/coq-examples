(*|
################################
Coq: automate repeated rewriting
################################

:Link: https://stackoverflow.com/questions/48139738/coq-automate-repeated-rewriting
|*)

(*|
Question
********
|*)

Example test : forall f (n : nat), f n = n -> f (f n) = n.
Proof.
  intros f n H. repeat rewrite H. reflexivity.
Qed.

(*|
What would be a good way to further automate this? In particular, I
would like to not have to mention the name of the hypothesis anywhere.

----

**A:** ``repeat rewrite H.`` can be replaced with ``rewrite ?H.``
(rewrite zero or more times) or ``rewrite !H.`` (rewrite one or more
times)

**A:** There is also ``autorewrite`` tactics.

**Q:** Is there a way to make ``autorewrite`` consider local
hypotheses?

**A:** You can use this new `strat_rewrite tactic
<https://github.com/coq/coq/blob/2d6e395dead61a49ede6208bc40e16b4b8e68ce4/CHANGES#L1028>`__:
``Require Import Setoid. Hint Rewrite my_hint : my_db. <...>
rewrite_strat topdown <local_term>; topdown (hints my_db).``
|*)

(*|
Answer
******

If the goal can be solved with some sequence of rewrites, then the
`congruence <https://coq.inria.fr/refman/tactics.html#congruence>`__
tactic can handle it.

    The tactic ``congruence``, by Pierre Corbineau, implements the
    standard Nelson and Oppen congruence closure algorithm, which is a
    decision procedure for ground equalities with uninterpreted
    symbols. It also include the constructor theory (see 8.5.7 and
    8.5.6). If the goal is a non-quantified equality, ``congruence``
    tries to prove it with non-quantified equalities in the context.
    Otherwise it tries to infer a discriminable equality from those in
    the context. Alternatively, ``congruence`` tries to prove that a
    hypothesis is equal to the goal or to the negation of another
    hypothesis.

    ``congruence`` is also able to take advantage of hypotheses
    stating quantified equalities, you have to provide a bound for the
    number of extra equalities generated that way. Please note that
    one of the members of the equality must contain all the quantified
    variables in order for ``congruence`` to match against it.

The above basically means that ``congruence`` can solve your goal if
it can be solved using ``rewrite`` and ``discriminate`` tactics. But
sometimes ``congruence`` can't help you because it does not unfold
definitions for you -- in that case you'll have to help it.
|*)

Reset Initial. (* .none *)
Example test : forall f (n : nat), f n = n -> f (f n) = n.
Proof. congruence. Qed.
