(*|
#####################################
Explanation transitivity of equal coq
#####################################

:Link: https://stackoverflow.com/q/54731299
|*)

(*|
Question
********

I have a proof which is already proved.
|*)

Definition Equal {T : Type} (x y : T) := @eq T x y. (* .none *)
Lemma Equal_Trans : forall T : Type, forall y x z : T,
      Equal x y -> Equal y z -> Equal x z.
Admitted. (* .none *)

(*|
And secondly, I have the correction of the addition commutativity
proof.

.. coq:: none
|*)

Definition Nat := nat.
Definition Add := Nat.add.

Lemma Add_zero : forall n : Nat, Equal n (Add n 0).
Proof. exact plus_n_O. Qed.

Lemma Equal_Morph : forall n m : Nat, Equal n m -> Equal (S n) (S m).
Proof. exact eq_S. Qed.

Lemma Add_S : forall n m : nat, S (Add n m) = Add n (S m).
Proof. exact plus_n_Sm. Qed.

(*||*)

Lemma Add_com : forall x x' : Nat, Equal (Add x x') (Add x' x).
Proof.
  intros. induction x.
  - simpl. apply Add_zero.
  - simpl.
    apply (Equal_Trans Nat (S (Add x' x))). (* var y *)
    + apply Equal_Morph. assumption.
    + apply Add_S.
Qed.

(*|
However, I don't understand the use of ``Equal_Trans`` (line 6). If I
understand, ``Equal_Trans`` takes 3 arguments: y x z? But why there is
only 1 argument using ``Equal_Trans`` in ``Add_com`` lemma?

Thank you in advance for your help.
|*)

(*|
Answer
******

The tactic ``apply`` tries to fill in the blanks to match the type of
the provided term with the goal. In this case, the goal (when the
tactic is used) is probably something along the lines of ``a = b``
(based on your followup, it's actually ``Equal a b``). The type of
``Equal_Trans`` (when all the arguments are used) is ``x = z``
(``Equal x z``), so to unify these two types, we should have ``x :=
a`` and ``z := b``. That only leaves ``y`` as ambiguous, so we have to
provide it.

To address your followup, no, ``Equal_Trans`` does not take *just* one
argument. It takes a type (``Nat`` in your case) three elements of
that type (``y``, ``x`` and ``z``) and two equality proofs. However,
remember that functions in Coq are curried, which means that you can
call them with fewer arguments, but the result will be a function of
the remaining arguments.

So really, when we say ``apply (Equal_Trans Nat (S (Add x' x)).``,
we're saying "take this thing that has type ``forall (x z: Nat), Equal
x (S (Add x' x)) -> Equal (S (Add x' x)) z -> Equal x z`` and try to
fill in some of the arguments to match it with my goal".

Coq looks at that type and realizes that the goal already looks like
``Equal x z``, so it's able to deduce what ``x`` and ``z`` have to be.
``Equal_Trans`` still takes two more arguments that Coq can't figure
out on its own (the proofs of ``Equal x y`` and ``Equal y z``), so
that's what the rest of the proof is doing.

----

We use transitivity with ``y := S (Add x' x)`` because we can prove
``Equal (S (Add x x')) (S (Add x' x))`` using the inductive hypothesis
(``IHx``). We can also prove ``Equal (S (Add x' x)) (Add x' (S x))``
by using the definition of ``Add``. Hence, it's natural to route the
proof of equality through ``S (Add x' x)``.

Now, we don't have to use transitivity with ``y := S (Add x' x)``. We
could prove that ``(S (Add x x'))`` and ``(Add x' (S x))`` are both
equal to some other element of ``Nat``. But the easiest and most
direct route is through ``S (Add x' x)``.
|*)
