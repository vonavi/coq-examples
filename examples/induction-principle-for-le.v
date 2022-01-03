(*|
##############################
Induction principle for ``le``
##############################

:Link: https://stackoverflow.com/q/55196816
|*)

(*|
Question
********

For the inductive type ``nat``, the generated induction principle uses
the constructors ``O`` and ``S`` in its statement:
|*)

Print nat. (* .unfold .no-in *)
Check nat_ind. (* .unfold .no-in *)

(*|
But for ``le``, the generated statement does not uses the constructors
``le_n`` and ``le_S``:
|*)

Print le. (* .unfold .no-in *)
Check le_ind. (* .unfold .no-in *)

(*|
However it is possible to state and prove an induction principle
following the same shape as the one for ``nat``:
|*)

Lemma le_ind' : forall n (P : forall m, le n m -> Prop),
    P n (le_n n) ->
    (forall m (p : le n m), P m p -> P (S m) (le_S n m p)) ->
    forall m (p : le n m), P m p.
Proof.
  fix H 6. intros. destruct p.
  - apply H0.
  - apply H1, H. apply H0. apply H1.
Qed.

(*|
I guess the generated one is more convenient. But how does Coq chooses
the shape for its generated induction principle? If there is any rule,
I cannot find them in the reference manual. What about other proof
assistants such as Agda?
|*)

(*|
Answer
******

You can manually generate an induction principle for an inductive type
by using the command ``Scheme`` (see the `documentation
<https://coq.inria.fr/distrib/current/refman/user-extensions/proof-schemes.html#generation-of-induction-principles-with-scheme>`__).

The command comes in two flavours:

- ``Scheme scheme := Induction for Sort Prop`` generates the standard
  induction scheme.
- ``Scheme scheme := Minimality for Sort Prop`` generates a simplified
  induction scheme more suited to inductive predicates.

If you define an inductive type in ``Type``, the generated induction
principle is of the first kind. If you define an inductive type in
``Prop`` (i.e. an inductive predicate), the generated induction
principle is of the second kind.

To obtain the induction principle that you want in the case of ``le``,
you can define it in ``Type``:
|*)

Inductive le (n : nat) : nat -> Type :=
| le_n : le n n
| le_S : forall m : nat, le n m -> le n (S m).

Check le_ind. (* .unfold *)

(*|
or you can manually ask Coq to generate the expected induction principle:
|*)

Reset le. (* .none *)
Inductive le (n : nat) : nat -> Prop :=
| le_n : le n n
| le_S : forall m : nat, le n m -> le n (S m).

Check le_ind. (* .unfold *)

Scheme le_ind2 := Induction for le Sort Prop.
Check le_ind2. (* .unfold *)
