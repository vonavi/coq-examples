(*|
################################
Unfold a notation within a scope
################################

:Link: https://stackoverflow.com/q/39514651
|*)

(*|
Question
********

`This answer <https://stackoverflow.com/a/26032966/3335288>`__
provides a simple useful trick: ``unfold ">="`` is the same as
``unfold ge`` but does not require you to know that ``>=`` is the
notation for ``ge``.

Can you do the same for notations within a scope?
|*)

Require Import NArith.
Goal forall x, (x >= x)%N.
  unfold ">=".

(*|
Here ``unfold ">="`` does not do anything because it tries to unfold
``ge``, not ``N.ge``.

I have found the following solution:
|*)

  Open Scope N.
  unfold ">=".

(*|
But is there a syntax allowing to unfold this notation without first
opening the scope?
|*)

(*|
Answer
******

Yes, you can use the template ``unfold string % scope`` as follows:
|*)

Reset Initial. (* .none *)
Require Import NArith.
Goal forall x, (x >= x)%N.
  unfold ">=" % N.

(*| This gives us the goal |*)

  Show. (* .unfold .messages *)

(*|
with unfolded ``>=``.

----

**A:** ``(term) % scope`` is the standard syntax for local opening of
an interpretation scope. It so happens that Coq accepts it in this
case too. It's actually not ``scope``, but ``key``, I'm being sloppy
here.
|*)
