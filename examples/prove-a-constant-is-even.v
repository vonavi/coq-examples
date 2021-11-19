(*|
Prove a constant is even
========================

:Link: https://stackoverflow.com/questions/62326896/prove-a-constant-is-even
|*)

(*|
Question
--------

Given the inductive definition of evenness, how is it best proved
that, say, 1024 is an even number? Repeating `apply even_S` down to
zero is certainly not the right approach.
|*)

(*|
Answer (Arthur Azevedo De Amorim)
---------------------------------

As HTNW pointed out, you can use Ltac automation to produce such a
proof. This has the disadvantage of producing a large proof term
`even_S (even_S ... even_O)`, thus slowing down proofs. In this case,
it is better to reformulate the goal using a boolean decision
procedure:

.. coq:: none
|*)

Inductive even : nat -> Prop :=
| even_O : even O
| even_S : forall n, even n -> even (S (S n)).

(*||*)

Fixpoint evenb (n : nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S m) => evenb m
  end.

Lemma evenb_correct : forall n, evenb n = true <-> even n.
(* Fun exercise! *)
Admitted. (* .none *)

(*|
Coq can prove that `evenb 1024 = true` simply by evaluating the
left-hand side:
|*)

Goal (even 1024). apply evenb_correct. reflexivity. Qed.

(*|
Answer (HTNW)
-------------

Repeating `apply even_S` is not the way. `repeat apply even_S` is. If
`even_S` is a constructor, there's also `repeat constructor`.
|*)

Reset even. (* .none *)
Inductive even : nat -> Prop :=
| even_O : even O
| even_S : forall n, even n -> even (S (S n)).

Goal (even 1024). repeat apply even_S. exact even_O. Qed.
Goal (even 1024). repeat constructor. Qed.
(* also finds even_O, would leave as goal otherwise *)
