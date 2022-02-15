(*|
###############################
How to import libraries in Coq?
###############################

:Link: https://stackoverflow.com/q/46027014
|*)

(*|
Question
********

I want to use ``&&`` as infix form of ``andb`` in Coq. Official documentation tells me ``&&`` is defined in ``Coq.Init.Datatypes`` module. I tried this:
|*)

Import Coq.Init.Datatypes.

(*| Still Coq gives error: |*)

Fail Check true && false. (* .unfold .messages *)

(*| What is the correct way to include Std library in Coq? |*)

(*|
Answer
******

You can use the ``Locate`` command to get some information on this:
|*)

Locate "&&".

(*| Here is its output: |*)

Locate "&&". (* .unfold .messages *)

(*|
The `manual
<https://coq.inria.fr/distrib/current/refman/Reference-Manual014.html#scopes>`__
says that

    The initial state of Coq declares three interpretation scopes and
    no lonely notations. These scopes, in opening order, are
    ``core_scope``, ``type_scope`` and ``nat_scope``.

As you can see, ``bool_scope`` where the ``&&`` notation lives isn't
open by default.

You can either specify the scope explicitly:
|*)

Check (true && false) % bool.

(*| or open it like so: |*)

Open Scope bool_scope.
Check true && false.
