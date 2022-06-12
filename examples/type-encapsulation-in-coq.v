(*|
#########################
Type encapsulation in Coq
#########################

:Link: https://stackoverflow.com/q/30200952
|*)

(*|
Question
********

Is there a way in which I can define a type inside a Coq module but
encapsulate the constructors?

I want a client of the module to be capable to use the type but not to
construct members of that type, similar to what can be done in OCaml
with an abstract type.
|*)

(*|
Answer
******

Yes. You can define your type inside a module and assign a module type
to it:
|*)

Module Type FOO.

Variable t : Type.

End FOO.

Module Foo : FOO.

  Inductive typ :=
  | T : typ.

  Definition t := typ.

End Foo.

(* This fails *)
Fail Check Foo.T. (* .fails *)

(*|
Another possibility is to declare your module type as a dependent
record and parameterize your development over a suitable
implementation, e.g.
|*)

Record FOO := { t : Type }.

Section Defs.

  Variable Foo : FOO.

  (* Code ... *)

End Defs.

(* Instantiate FOO *)

Definition Foo := {| t := nat |}.

(*|
Strictly speaking, this doesn't hide the constructors of a type, but
as long as your client is only writing their definitions using the
interface, they won't be able to refer to your concrete
implementation.
|*)
