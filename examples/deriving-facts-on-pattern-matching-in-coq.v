(*|
#########################################
deriving facts on pattern matching in coq
#########################################

:Link: https://stackoverflow.com/questions/48276348/deriving-facts-on-pattern-matching-in-coq
|*)

(*|
Question
********

Consider the following program
|*)

Definition useGt0 (n: nat) (witness: n > 0) : nat :=
  10.

Fail Definition createGt0 (n: nat) : nat :=
  match n with
  | O => 42
  | S n' => useGt0 n _ (* ??? *)
  end. (* .fails *)

(*|
Clearly, ``n > 0`` is inhabited, because ``n = S n'``. However, how do
I get access to the proof that ``n = S n'``? From ``n = S n'``, we can
derive that ``n > 0``.

In general, I wish to understand: *How do I extract information from a
pattern match?*
|*)

(*|
Answer
******

The standard way to define ``createGt0`` function is to use the convoy
pattern (you can find several explanations using `[coq]
[convoy-pattern]
<https://stackoverflow.com/questions/tagged/coq+convoy-pattern>`__
search query on Stackoverflow). The standard link is A. Chlipala's
CPDT book.

Here is a solution:
|*)

Require Import PeanoNat.

Definition createGt0 (n : nat) : nat :=
  match n as x return (n = x -> nat) with
  | O => fun _ => 42
  | S n' => fun E =>
              useGt0 n (eq_ind_r (fun n => n > 0) (Nat.lt_0_succ n') E)
  end eq_refl.

(*|
Another option is to use ``Program`` mechanism, which lets you program
in non-dependently-typed style, deferring proof obligations until a
later time:
|*)

Reset createGt0. (* .none *)
Require Import Program.

Program Definition createGt0 (n : nat) : nat :=
  match n with
  | O => 42
  | S n' => useGt0 n _
  end.
Next Obligation. apply Nat.lt_0_succ. Qed.

(*| At last, you could use tactics to build your function: |*)

Reset createGt0. (* .none *)
Definition createGt0 (n : nat) : nat.
Proof.
  destruct n eqn:E.
  - exact 42.
  - refine (useGt0 n _).
    rewrite E.
    apply Nat.lt_0_succ.
Defined.

(*|
If you end your function with ``Qed``, Coq will consider it opaque and
won't reduce. Try ending the function with both ``Qed`` and
``Defined`` and execute the following command:
|*)

Compute createGt0 0.

(*|
----

**Q:** I am clearly out of my depth here. ``eq_ind_r`` states that if
a property ``P`` holds for ``x``, then ``x = y`` implies ``P y``,
correct?

**A:** Yes, it is correct. ``E`` has type ``n = S n'``, and
``Nat.lt_0_succ n'`` gives us a proof of ``S n' > 0``, but we want a
proof of ``n > 0``, so we use ``eq_ind_r`` to substitute ``n`` for ``S
n'`` in that proof of ``S n' > 0``.
|*)
