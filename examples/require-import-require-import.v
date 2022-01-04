(*|
###########################################
``Require``, ``Import``, ``Require Import``
###########################################

:Link: https://stackoverflow.com/q/47973317
|*)

(*|
Question
********

In Coq, what's the difference between ... ?

- ``Require X.``
- ``Import X.``
- ``Require Import X.``

I have basically memorized some common patterns. I usually see code
using ``Require Import X``. Then there's ``Import ListNotation``. And
I just noticed it's also possible to write just ``Require X``. What's
the difference? Some practical examples would be appreciated.
|*)

(*|
Answer
******

``Require`` loads a library whereas ``Import`` brings its definitions
into scope. ``Require Import`` does both. If you only have the library
loaded, you'll need to refer to names fully qualified. Coq allows
top-level modules corresponding to files to define modules; these have
to be imported separately to bring all of their definitions into
scope, and they can't be ``Require``\ d - that's what's going on with
``ListNotations``:
|*)

(* List is not loaded by default *)
Fail Check List.map. (* .fails *)

(* the full name is technically Coq.Lists.List *)
Require List.

(* note that lists are actually defined in Coq.Init.Datatypes which is
   imported by default, so [list] is unqualified and the [x::xs]
   notation is already defined *)
Print List.map. (* .unfold *)

(* bring everything in List into scope *)
Import List.
(* this includes the ListNotations submodule *)
Import ListNotations.

(* note that now list notations are available, and the list notation
   scope is open (from importing List) *)
Print List.map. (* .unfold *)

(*|
Note there are some quirks with how Coq handles modules, especially
compared to other languages:

- Coq does not require a full path to a module, only an unambiguous
  suffix. Indeed I rarely see full import paths, even to standard
  library modules.
- Notations cannot be used except by importing the module, and unlike
  most objects there's no way to refer to a notation, fully qualified
  or otherwise.
- Importing a module can have side effects, for example changing
  notation interpretation scopes or setting options if you use
  ``Global Set`` in the module being imported.
- Importing is fairly limited (especially compared to Haskell) -
  there's no way to rename a module at import time, or selectively
  import some definitions.
|*)
