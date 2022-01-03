(*|
#################################################################
``Import <Module>`` vs. ``Include <Module>`` in Coq Module system
#################################################################

:Link: https://stackoverflow.com/q/48837996
|*)

(*|
Question
********

What is the exact semantics of ``Include M1`` inside another module,
say ``M``? How is it different from doing ``Import M1`` inside the
module ``M``? More precisely what is the semantics of the following
command:

.. coq:: none
|*)

Module Type M1. End M1.
Module Type M2. End M2.
Module Type M3. End M3.

(*||*)

Module Type M := M1 <+ M2 <+ M3.

(*|
Answer
******

To summarize the semantics of both vernacular commands:

- The command ``Include M1`` (which can be used in the definition of a
  *module* or a *module type*\ ) asks Coq to make a copy of all the
  fields of ``M1``. Thus, it acts just like a "copy-and-paste" of the
  contents of ``M1`` inside the ambient module (resp. module type).
- The command ``Import M1`` (which can also be used in the definition
  of a *module* or a *module type*, but additionally requires that
  ``M1`` is a *module*\ ) allows one to refer to the fields of ``M1``
  with their short identifier (i.e., without needing to use qualified
  identifiers ``M1.field_name``)

Next, the syntax
|*)

Reset M. (* .none *)
Module Type M := M1 <+ M2 <+ M3.

(*| is a shortcut for: |*)

Reset M. (* .none *)
Module Type M.
  Include M1.
  Include M2.
  Include M3.
End M.

(*|
The relevant sections of Coq's reference manual are `Sect. 2.5.1
(Include)
<https://coq.inria.fr/distrib/V8.7.2/refman/gallina-ext.html#sec90>`__,
`Sect. 2.5.8 (Import)
<https://coq.inria.fr/distrib/V8.7.2/refman/gallina-ext.html#Import>`__
and you may also want to take a look at the `Export
<https://coq.inria.fr/distrib/V8.7.2/refman/gallina-ext.html#hevea_command55>`__
command (a variant of ``Import``).

If at some point you hesitate between ``Include`` and ``Import``, you
should probably try to use ``Import`` in the first place, because it
will have a lighter effect (it won't clone the contents of the
specified module but just define shorter names).

Finally, below are two comprehensive examples that illustrate the use
of modules, module types, and functors in Coq as well as the commands
``Include`` and ``Import``:
|*)

(********************************************)
(* Example involving a parameterized module *)
(********************************************)

Reset M1. (* .none *)
(* A signature *)
Module Type MT.
  Parameter t : Type.
End MT.

(* A bigger signature *)
Module Type MT1.
  Include MT.
  Parameter u : t.
  Parameter f : t -> t.
End MT1.

(* A parameterized module *)
Module F1 (M1 : MT1).
  Import M1. (* => we can now write f rather than M1.f *)
  Definition fu := f u.
End F1.

(* A module implementing MT1 *)
Module M1 <: MT1. (* => check the signature but don't make the module opaque *)
  Definition t := nat.
  Definition u := O.
  Definition f := S.
End M1.

(* Instantiation *)
Module FM1 := F1 M1.
Compute FM1.fu.

(*|
and I recall that `Compute
<https://coq.inria.fr/distrib/current/refman/vernacular.html#hevea_command97>`__
is a shortcut for ``Eval vm_compute in``
|*)

(**********************************************)
(* Extra example: a parameterized signature   *)
(*                                            *)
(* It can be noted that this feature of Coq   *)
(* module types has no equivalent in OCaml... *)
(**********************************************)

Module Type MT2 (M : MT).
  Parameter u : M.t.
  Import M. (* => we can now write t rather than M.t *)
  Parameter f : t -> t.
End MT2.

(* Another parameterized module *)
Module F2 (M : MT) (M2 : MT2 M).
  Import M2.
  Definition fu := f u.
End F2.

(* Modules implementing MT and MT2 *)
Module M <: MT.
  Definition t := bool.
End M.

Module M2 <: MT2 M.
  Definition u := false.
  Definition f := negb.
End M2.

(* Instantiation *)
Module FM2 := F2 M M2.
Compute FM2.fu.
