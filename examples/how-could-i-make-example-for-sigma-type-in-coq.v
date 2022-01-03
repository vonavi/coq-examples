(*|
###############################################
How could I make example for sigma type in Coq?
###############################################

:Link: https://stackoverflow.com/q/56365504
|*)

(*|
Question
********

For that type:
|*)

Record Version :=
  mkVersion {
      major  : nat;
      minor  : nat;
      branch : {b : nat | b > 0 /\ b <= 9};
      hotfix : {h : nat | h > 0 /\ h < 8}
    }.

(*| I'm trying to make an example, and it failed with: |*)

Fail Example ex1 := mkVersion 3 2 (exist _ 5) (exist _ 5). (* .unfold .fails *)

(*| What am I missing? |*)

(*|
Answer
******

The reason it fails is that you need not only provide a witness (``b``
and ``h`` in this case) but also a proof that the corresponding
condition holds for the provided witness.

I would switch to booleans to make my life easier, because this allows
proof by computation, which is basically what ``eq_refl`` does in the
snippet below:
|*)

Reset Version. (* .none *)
From Coq Require Import Bool Arith.

Coercion is_true : bool >-> Sortclass.

Record Version :=
  mkVersion {
      major  : nat;
      minor  : nat;
      branch : {b : nat | (0 <? b) && (b <=? 9)};
      hotfix : {h : nat | (0 <? h) && (h <? 8)}
    }.

Example ex1 := mkVersion 3 2 (exist _ 5 eq_refl) (exist _ 5 eq_refl).

(*|
We could introduce a notation allowing a nicer representation of literals:
|*)

Notation "<| M ',' m ',' b '~' h |>" :=
  (mkVersion M m (exist _ b eq_refl) (exist _ h eq_refl)).

Example ex2 := <| 3,2,5~5 |>.

(*|
If there is a need to add manual proofs then I'd suggest to use
``Program`` mechanism:
|*)

From Coq Require Import Program.

Program Definition ex3 b h (condb : b =? 5) (condh : h =? 1) :=
  mkVersion 3 2 (exist _ b _) (exist _ h _).
Next Obligation.
  now unfold is_true in * |-; rewrite Nat.eqb_eq in * |-; subst. Qed.
Next Obligation.
  now unfold is_true in * |-; rewrite Nat.eqb_eq in * |-; subst. Qed.

(*| or ``refine`` tactic: |*)

Definition ex3' b h (condb : b =? 5) (condh : h =? 1) : Version.
Proof.
  now refine (mkVersion 3 2 (exist _ b _) (exist _ h _));
    unfold is_true in * |-; rewrite Nat.eqb_eq in * |-; subst.
Qed.
