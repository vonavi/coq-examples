(*|
Coq: Recursive definition of fibonacci is ill-formed
====================================================

https://stackoverflow.com/questions/67758117/coq-recursive-definition-of-fibonacci-is-ill-formed
|*)

(*|
Question
--------

I am trying to define Fibonacci numbers using coq. This is my code:

.. coq:: unfold
|*)

Fail Fixpoint fibonacci (n:nat) : nat :=
  match n with
  | O => 1
  | S O => 1
  | S (S n') => fibonacci (S n') + fibonacci n
  end.

(*|
I am wondering why this is wrong. Parenthetically, in the third clause
of the match, I did not define the property of `n'` (e.g. `n': nat`),
what would be the default of the property of `n'`?

Thanks in advance!
|*)

(*|
Answer
------

All arguments of a recursive call must be structurally decreasing,
that is you must strip away one constructor symbol in the match. In
your case the `(S n')` argument is in fact structurally decreasing,
but Coq doesn't detect that (which is a bit silly) because you add
another constructor `S`, which is not allowed. The second argument is
wrong and should probably be `n'`. Besides one usually defines this
such that `fibonacci 0 = 0`.

To get around the issue of `(S n')` one gives it a separate name with
`as` as in:
|*)

Require Import List.

Fixpoint fibonacci (n:nat) : nat :=
  match n with
  | O => 0
  | S O => 1
  | S (S O) => 1
  | S ((S n'') as n') => fibonacci n' + fibonacci n''
  end.

Eval cbv in map fibonacci (seq 0 10). (* .unfold *)
