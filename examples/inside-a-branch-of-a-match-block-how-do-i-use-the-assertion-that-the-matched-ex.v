(*|
##############################################################################################################################################
Inside a branch of a match block, how do I use the assertion that the matched expression is equal to the branch's data constructor expression?
##############################################################################################################################################

:Link: https://stackoverflow.com/q/14085189
|*)

(*|
Question
********

I am trying to develop a programming style that is based on preventing
bad input as soon as possible. For example, instead of the following
plausible definition for the predecessor function on the natural
numbers:
|*)

Definition pred1 n :=
  match n with
  | O   => None
  | S n => Some n
  end.

(*| I want to write it as follows: |*)

Theorem nope n (p : n = O) (q : n <> O) : False.
  contradict q. exact p.
Qed.

Fail Definition pred2 n (q : n <> O) :=
  match n with
  | S n => n
  | O   =>
      let p := _ in
      match nope n p q with end
  end. (* .fails *)

(*|
But I have no idea what to replace ``_`` with. My intuition suggests
me that there must be some ``assumption : n = O`` available in the ``|
O =>`` branch. Does Coq indeed introduce such an assumption? If so,
what is its name?
|*)

(*|
Answer
******

Coq doesn't automatically introduce such hypothesis, but you can
introduce it explicitly by using the full form of the ``match``
construction:
|*)

Definition pred2 n (q : n <> O) :=
  match n as n' return n = n' -> nat with
  | S p => fun _ => p
  | O   => fun Heq => match q Heq with end
  end (eq_refl n).

(*|
Explanations:

- ``return`` introduces a type annotation with the type of the whole
  ``match ... end`` expression;

- ``as`` introduces a variable name that can be used in this type
  annotation and will be substituted with the left hand side in each
  branch. Here,

  - in the first branch, the right hand side has type ``n = S p ->
    nat``;
  - in the second branch, the right hand side has type ``n = O ->
    nat``. Therefore, ``q Heq`` has type ``False`` and can be matched.

More information in the `reference manual
<http://coq.inria.fr/distrib/V8.4/refman/>`__, in the chapter on
`Extended pattern-matching
<http://coq.inria.fr/distrib/V8.4/refman/Reference-Manual022.html>`__.
|*)
