(*|
##################################################################
How to define an inductive type and a definition at the same time?
##################################################################

:Link: https://stackoverflow.com/q/23163562
|*)

(*|
Question
********

I want to have the following definitions:
|*)

Require Import String. (* .none *)
Fail Inductive a : Set :=
| basic : string -> a
| complex : string -> list t -> a. (* .fails *)

Fail Definition t := string * a * a. (* .fails *)

(*|
As you can see, when defining ``a``, ``t`` is used and when defining
``t``, ``a`` is used. My question is how can I define these two at the
same time?
|*)

(*|
Answer
******

You can define them mutually with the ``Inductive`` command.
|*)

Inductive a : Set :=
| basic : string -> a
| complex : string -> list t -> a
with t : Set :=
| t_intro : string * a * a -> t.

(*|
Or you can substitute using the definition of ``t``, and define ``t``
afterwards.
|*)

Reset a. (* .none *)
Inductive a : Set :=
| basic : string -> a
| complex : string -> list (string * a * a) -> a.

Definition t : Set := (string * a * a)%type.

Definition complex' : string -> list t -> a := complex.
