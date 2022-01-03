(*|
##############################################
Coq: Proving relation between ``<`` and ``<=``
##############################################

:Link: https://stackoverflow.com/q/57719818
|*)

(*|
Question
********

I am learning Coq right now and in a larger proof I have become
stumped by the following sub-proof:
|*)

Theorem sub : forall n m : nat, n <= m -> n <> m -> n < m.
Abort. (* .none *)

(*| Or, once unfolded: |*)

Theorem sub : forall n m : nat, n <= m -> n <> m -> S n <= m.
Abort. (* .none *)

(*| Here, ``n <= m`` is inductively defined as follows: |*)

Inductive le : nat -> nat -> Prop :=
| le_n : forall n : nat, le n n
| le_S : forall n m : nat, le n m -> le n (S m).

(*| I have not gotten very far, but my attempt looks like this: |*)

Theorem sub : forall n m : nat, n <= m -> n <> m -> n < m.
Proof.
  unfold lt. intro n. induction n.
  - induction m.
    + intros. exfalso. contradiction.
    + admit.

(*|
In the first inductive step (marked by the first admit), the inductive
hypothesis shows the following:
|*)

      Undo. (* .none *) Show 1. (* .unfold .messages *)

(*|
I am not sure how I can leverage this hypothesis to prove the subgoal.
I would appreciate any guidance in the right direction.
|*)

Admitted. (* .none *)

(*|
Answer
******

Since ``le`` is defined as an inductive predicate, it makes more sense
to do the induction on that, rather than ``n``. ``le`` doesn't make
any references to ``0`` or even ``S n`` (it does have ``S m``), so
induction on ``n`` is probably not the way to go. Induction on ``m``
*might* work, but it's probably harder than necessary.

Before starting a formal proof, it can often be helpful to think about
how you would prove this informally (still using the same definitions,
though). If you assume that ``n <= m``, then by the inductive
definition of ``lt``, this means that either ``n`` and ``m`` are the
same, or ``m`` is the successor of some number ``m'`` and ``n`` is
less than or equal to ``m'`` (can you see why the definition of ``lt``
implies this?). In the first case, we'll have to use the additional
hypothesis that ``n <> m`` to derive a contradiction. In the second
case, we won't even need that. ``n <= m'`` implies that ``S n <= S
m'``, so since ``m = S m'``, ``S n <= m``, i.e., ``n < m``.

For the formalization, we'll have to prove that assumption on the last
line that ``n <= m`` implies ``S n <= S m``. You should try a similar
informal analysis to prove it. Other than that, the informal proof
should be straightforward to formalize. Case analysis on ``H: n <= m``
is just ``destruct H.``.

----

One more thing. This isn't essential, but can often help in the long
run. When defining an inductive type (or predicate), if you can factor
out a parameter that's used the same way in each constructor, it can
make the induction principle more powerful. The way you have it with
``le``, ``n`` is universally quantified and used the same way for both
constructors. Every instance of ``le`` starts with ``le n``.
|*)

Reset le. (* .none *)
Inductive le : nat -> nat -> Prop :=
| le_n : forall n : nat, le n n
| le_S : forall n m : nat, le n m -> le n (S m).

(*| That means that we can factor out that index into a parameter. |*)

Inductive le' (n: nat) : nat -> Prop :=
| le_n' : le' n n
| le_S' : forall m : nat, le' n m -> le' n (S m).

(*| This gives you a slightly simpler/better induction principle. |*)

Check le'_ind. (* .unfold .messages *)

(*| Compare this to ``le_ind``. |*)

Check le_ind. (* .unfold .messages *)

(*|
Basically what's happening here is that with ``le_ind``, you have to
prove everything for every ``n``. With ``le'_ind``, you only need to
prove it for the particular ``n`` that you're using. This can
sometimes simplify proofs, though it's not necessary for the proof of
your theorem. It's a good exercise to prove that these two predicates
are equivalent.
|*)
