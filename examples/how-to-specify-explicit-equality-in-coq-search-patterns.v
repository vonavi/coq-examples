(*|
########################################################
How to specify explicit equality in Coq search patterns?
########################################################

:Link: https://stackoverflow.com/q/47488993
|*)

(*|
Question
********

Suppose we have a hypothesis ``x - x = 0``.

One would presume a theorem for this already exists, so we fire up
``SearchAbout (_ - _ = 0)``. In this case however, we actually know
that these underscores are equivalent. As such, I would prefer to
write something like ``SearchAbout (fun a => a - a = 0)`` or something
along those lines.

Is it possible?
|*)

(*|
Answer
******

First of all, you need to import the ``Arith`` module (or a module
supporting reasoning with the kind of numbers you'd like to deal
with):
|*)

Require Import Coq.Arith.Arith.

(*| Then ``Search (?x - ?x = 0).`` will return |*)

Search (?x - ?x = 0). (* .unfold .messages *)

(*|
You can also more concisely search for a relevant rewriting lemma with
``SearchRewrite (?x - ?x).`` (note that you only need to specify one
side of the equality).

By the way, the ``SearchAbout`` command is deprecated.
|*)
