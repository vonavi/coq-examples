(*|
How to debug tactic failure in a match goal branch?
===================================================

:Link: https://stackoverflow.com/questions/65501576/how-to-debug-tactic-failure-in-a-match-goal-branch
|*)

(*|
Question
--------

Let's say I have some complex tactics in the body of a `match goal`
branch that can easily go wrong in a way I might need to debug. Is
there a way to get the "real" error message from the branch if some
tactic fails, rather than simply getting "Error: No matching clauses
for match goal"?

Take as an example this fake tactic where `apply A, B, C` has several
chances for something to go wrong. I've been fighting with a real
tactic somewhat similar to this today.
|*)

Ltac three_applications :=
  match goal with
  | [
      A : _ (* something reasonable *),
      B : _ (* something reasonable *),
      C : _ (* something reasonable *)
    |- _ ]  =>
    idtac A B C;
    assert (F: _ (* something reasonable *))
      by apply A, B, C;
    solve [discriminate F]
  end.

(*| Thank you in advance! |*)

(*|
Answer
------

The easiest is to use `lazymatch goal` instead but it has different
semantics, but as I see you match only on one shape, it might be ok
for you.

The idea is that `match goal` might backtrack: if you have
|*)

Ltac tac :=
  match goal with
  | n : nat |- _ => destruct n; reflexivity
  | |- nat => exact 0
  end.

(*|
it will first try to find some `n : nat` in your hypotheses, starting
from the most recent, and then try the tactic `destruct n;
reflexivity`. If it fails, it will try to find another natural number.
If all of them fail, then it will look if the goal matches the second
clause instead, and if so execute `exact 0`. If that fails again, it
will backtrack once again and conclude that `No matching clauses for
match goal`.

On the other hand,
|*)

Reset tac. (* .none *)
Ltac tac :=
  lazymatch goal with
  | n : nat |- _ => destruct n; reflexivity
  | |- nat => exact 0
  end.

(*|
will find the first branch that matches, and then apply the tactic, if
it fails, no backtracking in the `lazymatch`, and it will give you the
error of the tactic in the corresponding branch.

Note that I would always use `lazymatch`, not just for debugging
purposes, when I don't find a use case for backtracking.

----

In case, `lazymatch` is not semantically equivalent to your match and
backtracking needs to be involved then it will be harder, but indeed,
using `idtac A B C` can help you see which branch it selected before
launching the error. Sometimes, writing

`Fail three_applications.`

instead of just

`three_applications.`

will help because `Fail` will usually keep the printing that you made
in the command, even if it failed in the end.

Once you know the branch, just apply your tactic manually.
|*)
