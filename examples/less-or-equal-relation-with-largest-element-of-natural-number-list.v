(*|
less or equal relation with largest element of natural number list
==================================================================

:Link: https://stackoverflow.com/questions/67379273/less-or-equal-relation-with-largest-element-of-natural-number-list
|*)

(*|
Question
--------

I want to use definition of ``list_max_le``. After applying ``Search
list_max_le.`` I get nothing. How I can define ``list_max_le`` in Coq?
|*)

(*|
Answer
------
|*)

Require Import List.
Search "list" "max". (* .unfold *)

(*|
by using quotes ``"..."`` you search for definitions with has the
specified string in its *name*.

If you want to see the definition of ``list_max_le``, you use the
``Print`` command
|*)

Print list_max_le.

(*|
but in this case the definition is not very readable.

If you ``Search`` without ``"..."``, you search with a pattern that
tries to match part of the type definition.

So if you search
|*)

Search list_max. (* .unfold *)

(*|
You search for all definitions that contains the *term* ``list_max``.

You can have many strings and terms to refine your search. As an
example, if you want some lemma about induction on lists, it is
probably called something with "ind" in its name, and has the ``list``
term in its type (not necessarily in its name). So you can try
|*)

Search "ind" list.
