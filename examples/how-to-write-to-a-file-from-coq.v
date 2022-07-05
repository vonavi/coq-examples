(*|
################################
How to write to a file, from Coq
################################

:Link: https://stackoverflow.com/q/49746424
|*)

(*|
Question
********

This is probably a strange question to ask since Coq is supposed to be
a purely functional language, but ``Extraction`` exists and it clearly
has side effects, so I'd assume there's probably a more basic command
to just output a string or some constant to a file, something like
this:

.. code-block:: coq

    Extraction "file.txt" "hello"%string.

Is this possible? Would it require writing a custom extractor (I don't
even know if that's possible)?

The practical reason for this question is related to the motivation
for the extraction mechanism that is already present in Coq, but let's
say I want to output C code or something else that's not currently
supported. I could still write a function in Coq ``extract : Expr ->
string`` for a custom syntax that I formalize in an inductive type
``Expr``. How can I get this string out to a file?
|*)

(*|
Answer
******

You can use ``Redirect`` with ``Eval`` to get close:
|*)

Require Import String.
Open Scope string_scope.

Redirect "file.txt" Eval compute in "hello".

(* file.txt.out now contains:
     = "hello"
     : string
*)

(*|
Alternately, write your function ``extract`` in Coq, then use the
extraction mechanism to extract ``extract e`` for some ``e`` of
interest, and finally write an OCaml program that imports this
(string) constant and prints it. The reason to go this route is that
building up strings in Coq is so slow that you might not be able to
run ``Eval compute extract e`` but you might be able to run it in
OCaml. You can also then (in an unverified manner) replace Coq strings
with OCaml native strings so this process is actually efficient; this
is easy to do by importing ``ExtrOcamlString`` in Coq before
extraction.
|*)
