(*|
###################################################################################
Problems with missing information in Obligations when defining using Program in Coq
###################################################################################

:Link: https://stackoverflow.com/q/69138674
|*)

(*|
Question
********

I am new to Coq and trying to figure out how to use ``Program`` to
more easily define things and then solve obligations, however,
sometimes I am left with obligations that cannot be solved because
some information have been lost.

If for example I define the following (a bit contrived but the
simplest example I could think of), then the function f if a function
that takes two identical even numbers and return the double of that
number.
|*)

Require Import Coq.Program.Tactics. (* .none *)
Program Definition f {n : nat} (k1 k2 : {j : nat | j + j = n}) :
  {j : nat | j = n} := k1 + k2.
Next Obligation.

(*|
The problem is that, when I start solving the first obligation, this
is what I am left with
|*)

  Show 1. (* .unfold .messages *)
Abort. (* .none *)

(*|
witch can clearly not be solved, as I have lost the information about
``k1 + k1 = k2 + k2``, and I am left proving that two arbitrary
natural numbers are equal.

Why does this happen, and what do you do in that situation to make Coq
remember "*all the assumptions*"?
|*)

(*|
Answer
******

This the work of the ``program_simpl`` tactic, which is the default
``Obligation Tactic`` applied whenever you open an ``Obligation`` (and
also to completely solve obligations before you open them). You can
turn it off by setting it to ``idtac``. If that's too drastic, you can
just throw away its results if it fails to solve the obligation
outright (so obligations that can be solved automatically are).
|*)

Require Import Psatz.

#[local] Obligation Tactic := try now program_simpl.
#[program] Definition f {n : nat} (k1 k2 : {j : nat | j + j = n}) :
  {j : nat | j = n} := k1 + k2.
Next Obligation.
  intros n [k1 ?] [k2 ?].
  (* program_simpl is responsible for the usual automatic intros, but
  now we have to do it *)
  simpl. lia.
Qed.
