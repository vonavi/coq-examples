(*|
####################################################
How does ``auto`` interract with biconditional (iff)
####################################################

:Link: https://stackoverflow.com/q/47435258
|*)

(*|
Question
********

I noticed, that ``auto`` is ignoring biconditionals. Here is a
simplified example:
|*)

Parameter A B : Prop.
Parameter A_iff_B : A <-> B.

Theorem foo1: A -> B.
Proof.
  intros H. apply A_iff_B. assumption.
Qed.

Theorem bar1: B -> A.
Proof.
  intros H. apply A_iff_B. assumption.
Qed.

Theorem foo2_failing: A -> B.
Proof.
  intros H. auto using A_iff_B.
Abort.

Theorem bar2_failing: B -> A.
Proof.
  intros H. auto using A_iff_B.
Abort.

(*|
Now, I know that ``A <-> B`` is a syntactic sugar for ``A -> B /\ B ->
A`` so I wrote two theorems to extract one or the other:
|*)

Theorem iff_forward : forall {P Q : Prop},
    (P <-> Q) -> P -> Q.
Proof.
  intros P Q H. apply H.
Qed.

Theorem iff_backward : forall {P Q : Prop},
    (P <-> Q) -> Q -> P.
Proof.
  intros P Q H. apply H.
Qed.

Theorem foo3 : A -> B.
Proof.
  intros H.
  auto using (iff_forward A_iff_B).
Qed.

Theorem bar3 : B -> A.
Proof.
  intros H.
  auto using (iff_backward A_iff_B).
Qed.

(*|
1. How come ``apply A_iff_B`` works and ``auto using A_iff_B`` does
   not? I thought that ``auto n`` is performing an exhaustive search
   of all possible sequences of ``apply`` of length <= n using the
   hypotheses and all theorems in a given database.

2. Is there a standard trick for working with biconditionals or are
   those two projection functions the usual solution?

3. Are such projection functions somewhere in the standard library? I
   could not found them.
|*)

(*|
Answer
******

    1. How come ``apply A_iff_B`` works and ``auto using A_iff_B``
       does not?

``auto`` generally uses ``simple apply`` instead of ``apply`` and this
restricted version of ``apply`` does not handle biconditionals.

    2. Is there a standard trick for working with biconditionals or
       are those two projection functions the usual solution?

You can use ``Hint Resolve -> (<-)`` feature for that:
|*)

Reset foo3. (* .none *)
(* if you remove this one, then `auto` won't be able to prove the
   `bar3` theorem *)
Hint Resolve -> A_iff_B.
Hint Resolve <- A_iff_B.

Theorem foo3 : A -> B.
Proof. info_auto. Qed. (* look at the output *)

(*|
\
    3. Are such projection functions somewhere in the standard
       library?

Yes, they are called: ``proj1`` and ``proj2``. Here is how you can
find them:
|*)

Search (?A /\ ?B -> ?A).

(*|
Or a bit easier to type, but finds a tad more stuff than we need:
|*)

Search (_ /\ _ -> _).
