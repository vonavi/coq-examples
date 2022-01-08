(*|
######################################################
How do I provide implicit arguments explicitly in Coq?
######################################################

:Link: https://stackoverflow.com/q/47874422
|*)

(*|
Question
********

Suppose I have a definition ``f : x -> y -> z`` where ``x`` can be
easily inferred. I therefore choose to make ``x`` an implicit argument
using ``Arguments``.

Consider the following example:
|*)

Definition id : forall (S : Set), S -> S := fun S s => s.

Arguments id {_} s.

Check (id 1).

(*|
Clearly ``S = nat`` can be and is inferred by Coq, and Coq replies:
|*)

Check (id 1). (* .unfold .messages *)

(*|
However, at a later time, I want to make the implicit argument
explicit, say, for readability.

In other words, I would like something like:
|*)

(* We want to make it clear that the 2nd argument is nat *)
Fail Definition foo := id {nat} 1. (* .fails *)

(*|
Is this possible at all? If so, what is the appropriate syntax?
|*)

(*|
Answer
******

You can prepend the name with ``@`` to remove all implicits and
provide them explicitly:
|*)

Check @id nat 1.

(*|
You can also use ``(a:=v)`` to pass an implicit argument by name. This
can both clarify what argument is being passed and also allows you to
pass some implicits without passing ``_`` for the others:
|*)

Check id (S:=nat) 1.

Definition third {A B C : Type} (a : A) (b : B) (c : C) := c.
Check third (B:=nat) (A:=unit) tt 1 2.
