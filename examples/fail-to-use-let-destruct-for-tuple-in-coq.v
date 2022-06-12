(*|
#########################################
Fail to use let-destruct for tuple in Coq
#########################################

:Link: https://stackoverflow.com/q/30197166
|*)

(*|
Question
********

I'm a new user for Coq. I have defined some functions:
|*)

Definition p (a : nat) := (a + 1, a + 2, a + 3).

Fail Definition q :=
  let (s, r, t) := p 1 in
  s + r + t.

Definition q' :=
  match p 1 with
  | (s, r, t) => s + r + t
  end.

(*|
I'm trying to destruct the result of ``p`` into a tuple
representation. However coqc complains on ``q``:
|*)

Fail Definition q :=
  let (s, r, t) := p 1 in
  s + r + t. (* .unfold .messages *)

(*|
while ``q'`` can pass the compilation. If I change ``p`` to return a
pair ``(a + 1, a + 2)``, the corresponding ``q`` and ``q'`` both work
fine.

**Why let-destruct only allows pair? Or have I made any error in
syntax?** I've checked with Coq manual but found no clue.
|*)

(*|
Answer
******

What is a bit confusing in Coq is that there are *two* different forms
of destructing let. The one you are looking for needs a quote before
the pattern:
|*)

Reset Initial. (* .none *)
Definition p (a : nat) := (a + 1, a + 2, a + 3).

Definition q :=
  let '(s, r, t) := p 1 in
  s + r + t.

(*|
Prefixing the pattern with a quote allows you to use nested patterns
and use user-defined notations in them. The form without the quote
only works with one-level patterns, and doesn't allow you to use
notations, or refer to constructor names in your patterns.

----

**Q:** So the 3-member tuple should be regarded as destructing again
on the first member of pair, then I have to use 'quote'?
|*)
