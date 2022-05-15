(*|
###########################################
Agda-like programming in Coq/Proof General?
###########################################

:Link: https://stackoverflow.com/q/41837820
|*)

(*|
Question
********

Unlike Agda, Coq tends to separate proofs from functions. The tactics
Coq gives are great for writing proofs, but I'm wondering if there is
a way to replicate some Agda-mode functionality.

Specifically, I'd like:

- Some equivalent of Agda's ``?`` or Haskell's ``_``, where I can omit
  part of a function while I'm writing it, and (hopefully) have Coq
  tell me the type I need to put there
- An equivalent of ``C-c C-r`` in Agda mode (``reify``), where you
  fill a ``?`` block with a function, and it will make new ``?``
  blocks for the needed arguments
- When I'm doing a ``match`` in a function, having Coq automatically
  write expand out the possible branches (like ``C-c C-a`` in
  Agda-mode)

Is this possible, in CoqIde or Proof General?
|*)

(*|
Answer
******

Let me teach you one weird trick. It may not be the answer to all your
concerns, but it might help, at least conceptually.

Let's implement addition for natural numbers, the latter being given
by
|*)

Inductive nat : Set :=
| zero : nat
| suc : nat -> nat.

(*| You can try to write addition by tactics, but this happens. |*)

Theorem plus' : nat -> nat -> nat.
Proof.
  induction 1.
  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
you can't see what you're doing.

The trick is to look more closely at what you're doing. We can
introduce a gratuitously dependent type, cloning ``nat``.
|*)

Inductive PLUS (x y : nat) : Set :=
| defPLUS : nat -> PLUS x y.

(*|
The idea is that ``PLUS x y`` is the type of "the way to compute
``plus x y``". We'll need a projection, allowing us to extract the
result of such a computation.
|*)

Theorem usePLUS : forall x y, PLUS x y -> nat.
Proof.
  induction 1. exact n.
Defined.

(*| Now we're ready to program by proving. |*)

Theorem mkPLUS : forall x y, PLUS x y.
Proof.
  Show. (* .unfold .messages *)

(*|
The conclusion of the goal shows us our current left-hand side and
context. The analogue of ``C-c C-c`` in Agda is...
|*)

  induction x.
  Show. (* .unfold .messages *)

(*|
And you can see it has done a case split! Let's knock off the base
case.
|*)

  intros y.
  - exact (defPLUS zero y y).

(*|
Invoking the constructor of ``PLUS`` is like writing an equation.
Imagine an ``=`` sign before its third argument. For the step case, we
need to make a recursive call.
|*)

  - intros y.
    eapply (fun h => (defPLUS (suc x) y (suc (usePLUS x y h)))).

(*|
To make the recursive call, we invoke ``usePLUS`` with the arguments
we want, here ``x`` and ``y``, but we abstract over the third
argument, which is the explanation of how actually to compute it. We
are left with just that subgoal, effectively the termination check.
|*)

    Show. (* .unfold .messages *)

(*| And now, rather than using Coq's guardedness check, you use... |*)

    auto.

(*|
...which checks that the inductive hypotheses cover the recursive
call. We're
|*)

Defined.

(*| We have a worker, but we need a wrapper. |*)

Theorem plus : nat -> nat -> nat.
Proof.
  intros x y.
  exact (usePLUS x y (mkPLUS x y)).
Defined.

(*| And we're ready to go. |*)

Eval compute in (plus (suc (suc zero)) (suc (suc zero))). (* .unfold *)

(*|
You *have* an interactive construction tool. You *can* game it to show
you the pertinent details of the problem you're solving by making
types more informative. The resulting proof script...
|*)

Reset mkPLUS. (* .none *)
Theorem mkPLUS : forall x y, PLUS x y.
Proof.
  induction x.
  - intros y.
    exact (defPLUS zero y y).
  - intros y.
    eapply (fun h => (defPLUS (suc x) y (suc (usePLUS x y h)))).
    auto.
Defined.

(*|
...is explicit about the program it constructs. You can see that's
defining addition.

If you automate this setup for program construction, then layer on an
interface showing you the program you're building and the key
problem-simplifying tactics, you get a funny little programming
language called Epigram 1.
|*)
