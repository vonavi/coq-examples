(*|
##########################################
Compute ``if`` in a decideable prop in coq
##########################################

:Link: https://stackoverflow.com/q/50733129
|*)

(*|
Question
********

I want to write a function that calculate count of ``true`` values of
``p 0 .. p t`` in a ``nat -> prop`` function.
|*)

Section count_sc.

  Variable p : nat -> Prop.
  Hypothesis p_dec : forall x : nat, {p x} + {~ p x}.

  Fixpoint count (x : nat) :=
    match x with
    | 0 => if p_dec 0 then 1 else 0
    | S y => if p_dec x then 1 + count y else count y
    end.

End count_sc.

Definition fret (x : nat) := False.

Axiom fret_dec : forall x : nat, { fret x } + { ~ fret x }.

Theorem hello_decide : forall x : nat, count fret fret_dec x = 0.
Proof.
  intros. induction x. unfold count.
  - Fail replace (fret_dec 0) with false. (* .fails *)

(*|
Before the ``replace`` tactic I should proof some goal like this:

.. code-block:: coq

    (if fret_dec 0 then 1 else 0) = 0

Coq does not automatically compute the value of the ``if`` statement.
and if I try to replace the ``fret_dec`` with it's value, I will get
this error:
|*)

    Fail replace (fret_dec 0) with false. (* .fails .unfold .messages *)
Abort. (* .none *)

(*|
How I can write ``count`` function that I can unfold and use it in
theorems?
|*)

(*|
Answer
******

You have declared ``fret_dec`` as an axiom. But that means it does not
have a definition, or implementation in other words. Thus, Coq cannot
compute with it.

You can still prove your theorem like so, using the ``destruct``
tactic:
|*)

Theorem hello_decide : forall x : nat, count fret fret_dec x = 0.
Proof.
  induction x as [| x IH].
  - unfold count. destruct (fret_dec 0) as [contra | _].
    + contradiction.
    + reflexivity.
  - simpl. rewrite IH. destruct (fret_dec (S x)) as [contra | _].
    + contradiction.
    + reflexivity.
Qed.

(*|
But, in this case it is really easy to provide such a decision
procedure instead of postulating it. And this simplifies the proof a
lot:
|*)

Definition fret_dec' (x : nat) : { fret x } + { ~ fret x }.
Proof. now right. Defined.

Theorem hello_decide' : forall x : nat, count fret fret_dec' x = 0.
Proof.
  induction x as [|x IH]; simpl.
  - reflexivity.
  - exact IH.
Qed.
