(*|
####################################
Transfering proof from Z to N in Coq
####################################

:Link: https://stackoverflow.com/questions/54752598/transfering-proof-from-z-to-n-in-coq
|*)

(*|
Question
********

Is there a way in Coq in to prove a statement for integer numbers and
the transfer statement in a semi-automatic way to naturals?

For a concret example, take the following lemma:
|*)

Lemma cancellation:
  forall a b c : nat, a > 0 -> a * b = a * c -> b = c.
Abort. (* .none *)

(*|
The statement is actually true in Z. In this case, it is easier to
prove, because one can use subtraction to get ``a * (b - c) = 0`` and
then simplify ``a``. But subtraction for naturals is capped, hence
this would not work.

Assume I can prove this for integers. Is there some tactic that one
could use to derive the statement for naturals as well?
|*)

(*|
Answer
******

One solution is a tactic called ``zify`` that automatically turns a
goal manipulating naturals into a goal manipulating integers (e.g., by
inserting appropriate calls to ``Z.of_nat``). This tactic is
internally called by ``lia``, but does not seem to be well documented.
It is at least mentioned `here
<https://coq.inria.fr/refman/addendum/micromega.html#id7>`__.

In your case, this would give the following.
|*)

Require Import ZArith.

(* The lemma stated in Z. *)
Lemma cancellation:
  (forall a b c, a > 0 -> a * b = a * c -> b = c)%Z.
Proof.
  (* your favorite proof of this result *)
Admitted.

(* The lemma stated in nat. *)
Lemma cancellation_nat:
  forall a b c : nat, a > 0 -> a * b = a * c -> b = c.
Proof.
  intros. zify. eauto using cancellation.
Qed.
