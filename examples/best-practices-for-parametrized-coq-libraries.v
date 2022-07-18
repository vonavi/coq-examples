(*|
#############################################
Best practices for parametrized Coq libraries
#############################################

:Link: https://stackoverflow.com/q/71143362
|*)

(*|
Question
********

I'm writing a library in Coq that depends on user-supplied type
parameters. One central part is a construction along the lines of
|*)

Require Import Ascii.
Require Import String.
Parameter UserType : Set. (* <<- placeholder for this example *)
Parameter UserToString : UserType -> string.

Inductive Tag : Set :=
| TBool
| TNat
| TUser
| TList : Tag -> Tag
| TSum : Tag -> Tag -> Tag.

Fixpoint decodeT (t : Tag) : Set :=
  match t with
  | TBool => bool
  | TNat => nat
  | TUser => UserType (* <<- needed here *)
  | TList t' => list (decodeT t')
  | TSum l r => sum (decodeT l) (decodeT r)
  end.
(* ...etc..., including: *)
Definition tostring (t : Tag) (v : decodeT t) : string :=
  (* match t with ... end *) "dummy".
(* and other stuff *)

(*|
so I can't avoid those ``Parameter``\ s in some form. The whole
library is split across multiple files, and because of the size it
would be pretty uncomfortable to put everything in one file.

There's a top-level wrapper that exports all sub-modules. Ideally, I'd
like to pass the parameters *once* when importing the library, and
then this wrapper can do some magic to propagate them to all
sub-modules, so that afterwards I don't have to worry about it
anymore.

I've looked into various approaches, but nothing worked so far.

If I wrap the file contents in ``Section``\ s, then the ``Parameter``\
s become extra arguments only on the definitions that use them, and
then I have to manually splice them in everywhere when using the
library's functions from outside.

If I don't wrap them in a ``Section``, they are module parameters but
I can't find a way to actually provide the value. (All forms of ``with
Definition`` seem to require a module signature / ``Module Type``?
Duplicating all names & types to make an explicit signature would be
prohibitively redundant, so maybe there is a way to make it work, but
I couldn't find it. The documentation is also rather unhelpful...)
Variations like using ``Context`` instead seem to have the same
problem, as far as I tested things.

I'm happy to make a ``Module Type UserDefs`` (or typeclass, or
whatever) that combines all the user definitions in a single value. I
just don't know how to actually get it into the submodules.

So how do I do it? What needs to happen inside that sample file above,
and what needs to happen on the outside, so that I can pass the
definitions in *once* and then get a fully configured library to
``Import``?
|*)

(*|
Answer
******

    then I have to manually splice them in everywhere when using the
    library's functions from outside.

This is typically addressed by a mix of implicit parameters and type
classes.

Declare a class for user-provided parameters.
|*)

Reset Initial. (* .none *)
Require Import String. (* .none *)
Class UserParams : Type :=
  { UserType : Set
  ; UserToString : UserType -> string
  }.

(* Make sure UserType and UserToString have UserParams as a maximally
   inserted implicit *)

(*|
Then in your library open sections parameterized by instances of that
class:
|*)

Require Import Ascii.
Require Import String.

Section MyLib.
  Context {userParams : UserParams}.
  (* Context generalizes Variable and allows you to set implicitness *)

  Inductive Tag : Set :=
  | TBool
  | TNat
  | TUser
  | TList : Tag -> Tag
  | TSum : Tag -> Tag -> Tag.

  Fixpoint decodeT (t : Tag) : Set :=
    match t with
    | TBool => bool
    | TNat => nat
    | TUser => UserType (* <<- needed here *)
    | TList t' => list (decodeT t')
    | TSum l r => sum (decodeT l) (decodeT r)
    end.
  (* ...etc..., including: *)
  Definition tostring (t : Tag) (v : decodeT t) : string :=
    (* match t with ... end *) "dummy".
  (* and other stuff *)

End MyLib.

(*|
Then users instantiate the class

.. code-block:: coq

    Require Import MyLib.

    Instance myParams : UserParams :=
      {| UserType := ...
       ; UserToString := ... |}.

And then your library functions will automatically be instantiated
when you use them.
|*)
