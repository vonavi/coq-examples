(*|
############################################################
In Coq, how to remove a defined variable from the namespace?
############################################################

:Link: https://stackoverflow.com/q/46839466
|*)

(*|
Question
********

**In the coqtop interactive terminal, how do I remove a name I have
defined?**

For example, I can define a bool type with the following.
|*)

Inductive my_bool : Type :=
| my_true : my_bool
| my_false : my_bool.

(*| This works and I get the following output. |*)

Reset my_bool. (* .none *)
Inductive my_bool : Type :=
| my_true : my_bool
| my_false : my_bool. (* .unfold .messages *)

(*|
But then, if I want to redefine the ``my_bool`` term, I get error
|*)

Fail Inductive my_bool : Type :=
| my_true : my_bool
| my_false : my_bool
| neither : my_bool. (* .fails .unfold *)

(*|
Can I drop and redefine the ``my_bool`` term without exiting the
``coqtop`` session?
|*)

(*|
Answer
******

You can use ``Reset my_bool.`` to remove it from the environment.

Reference:
https://coq.inria.fr/refman/proof-engine/vernacular-commands.html#coq:cmd.reset:

    ``Reset`` *ident* removes all the objects in the environment since
    *ident* was introduced, including *ident*. *ident* may be the name
    of a defined or declared object as well as the name of a section.
    One cannot reset over the name of a module or of an object inside
    a module.
|*)
