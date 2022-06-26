(*|
#################################
Explain a simple operation in Coq
#################################

:Link: https://stackoverflow.com/q/24177371
|*)

(*|
Question
********

I have the following code, Here ``O`` is the charater ``O`` not zero
``0``
|*)

Module Playground1.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Eval compute in (minustwo 4).

(*|
I just want to know how it evaluates to ``2``? I mean how it is
actually checking with a numeral and subtracting? I am not subtracting
anything here, still it is working? I want to know what is the basic
idea here? When I call ``minustwo 4`` how Coq know it is a numeral and
how it is returning the result? How the matching is working here?
|*)

(*|
Answer
******

It is quite easy with Coq to follow step by step what is going on. But
before we can do that, we need to know what your program looks like to
Coq without all the syntactic sugar. To do that, type the following in
your program:
|*)

Set Printing All.

(*| If you now print ``minustwo``, you will see that |*)

Print minustwo. (* .unfold *)

(*|
your pattern match is actually broken up into two pattern matches.

Not let us see step by step how Coq evaluates ``minustwo 4``. To do
so, create the following theorem:
|*)

Goal (minustwo 4 = 2).

(*|
We don't care that much about the theorem itself, we care more about
the fact that it contains the term ``minustwo 4``. We can now simplify
the expression step by step (you should run this in an ide to actually
see what is going on).

First, we unfold the definition of ``minustwo``, using a tactic called
``cbv delta``.
|*)

  cbv delta. (* unfold the definition of minustwo *)

(*| We can now call the function, using the tactic ``cbv beta``. |*)

  cbv beta. (* do the function call *)

(*| We can now do the pattern match with |*)

  cbv iota; cbv beta. (* pattern match *)

(*|
And because Coq broke up the match into two, we get to do it again
|*)

  cbv iota; cbv beta. (* pattern match *)

(*| And that is why ``minustwo 4`` is ``2`` |*)

  reflexivity.
Qed.
