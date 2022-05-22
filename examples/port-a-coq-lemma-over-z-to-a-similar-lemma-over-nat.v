(*|
###########################################################
Port a Coq lemma over ``Z`` to a similar lemma over ``nat``
###########################################################

:Link: https://stackoverflow.com/q/37293710
|*)

(*|
Question
********

I have a lemma that is proved for ``Z``. All the variables are bounded
to be greater that or equal to zero.

Q: How can one as easily and generally as possible "port" that lemma
to ``nat``, i.e. use that lemma to prove a similar lemma for ``nat``
by using the lemma for ``Z``?

Example:
|*)

Require Import ZArith.
Open Scope Z.

Lemma Z_lemma :
  forall n n0 n1 n2 n3 n4 n5 n6 : Z,
    n >= 0 -> n0 >= 0 -> n1 >= 0 ->
    n2 >= 0 -> n3 >= 0 -> n4 >= 0 ->
    n5 >= 0 -> n6 >= 0 ->
    n5 + n4 = n6 + n3 ->
    n1 + n0 = n2 + n ->
    n5 * n1 + n6 * n2 + n3 * n0 + n * n4 =
      n5 * n2 + n1 * n6 + n3 * n + n0 * n4.
Admitted.

Close Scope Z.

Lemma nat_lemma :
  forall n n0 n1 n2 n3 n4 n5 n6 : nat,
    n5 + n4 = n6 + n3 ->
    n1 + n0 = n2 + n ->
    n5 * n1 + n6 * n2 + n3 * n0 + n * n4 =
      n5 * n2 + n1 * n6 + n3 * n + n0 * n4.
  (* prove this using `Z_lemma` *)
Abort. (* .none *)

(*|
Answer
******

You can do it rather generically for all the lemmas which have this
shape by defining a tactic exploiting the fact that ``Z.of_nat`` is
injective and distributes over ``( + )`` and ``( * )``:
|*)

Ltac solve_using_Z_and lemma :=
  (* Apply Z.of_nat to both sides of the equation *)
  apply Nat2Z.inj;
  (* Push Z.of_nat through multiplications and additions *)
  repeat (rewrite Nat2Z.inj_mul || rewrite Nat2Z.inj_add);
  (* Apply the lemma passed as an argument*)
  apply lemma;
  (* Discharge all the goals with the shape Z.of_nat m >= 0 *)
  try (apply Z.le_ge, Nat2Z.is_nonneg);
  (* Push the multiplications and additions back through Z.of_nat *)
  repeat (rewrite <- Nat2Z.inj_mul || rewrite <- Nat2Z.inj_add);
  (* Peal off Z.of_nat on each side of the equation *)
  f_equal;
  (* Look up the assumption in the environment*)
  assumption.

(*| The proof of ``nat_lemma`` now simply becomes: |*)

Lemma nat_lemma :
  forall n n0 n1 n2 n3 n4 n5 n6 : nat,
    n5 + n4 = n6 + n3 ->
    n1 + n0 = n2 + n ->
    n5 * n1 + n6 * n2 + n3 * n0 + n * n4 =
      n5 * n2 + n1 * n6 + n3 * n + n0 * n4.
Proof.
  intros. solve_using_Z_and Z_lemma.
Qed.
