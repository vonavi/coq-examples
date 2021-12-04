(*|
#################################
Coq: Derive argument from context
#################################

:Link: https://stackoverflow.com/questions/53344715/coq-derive-argument-from-context
|*)

(*|
Question
********
|*)

(* I have a section with many variables and definitions. *)
Section SectionWithDefs.

  Context {A B C: Type}.

  Variable arg1: A -> B.
  Variable arg2: B -> C.

  (* Functions that uses these variables. *)
  Definition f a := arg2 (arg1 a).
  (* ... *)

End SectionWithDefs.

(* Now I want to use some of these functions. *)
Section AnotherSection.

  Context {A B C: Type}.

  (* Here are the arguments. *)
  Variable arg1: A -> B.
  Variable arg2: B -> C.

  Variable a: A.

  Section CallFunctionWithArgiments.

    (* We can directly pass the arguments to the function... *)
    Eval compute in (f arg1 arg2 a).

  End CallFunctionWithArgiments.

  Section LetBlock.

    (* ... or we can create a sequence of let expression. *)
    Let f := f arg1 arg2.
    (* ... *)

    Eval compute in (f a).

  End LetBlock.

End AnotherSection.

(*|
It is really hard to use the first approach since it is very difficult
to maintain such code. Writing becomes really painful when there are
more than five different functions with 4-5 arguments each.

The second case is more convenient. But I still have a lot of extra
lines with "let" declarations:

.. code-block:: coq

    Let f1 := ...
    Let f2 := ...
    ...
    Let fn := ...

Is there any way to avoid this extra boilerplate? Ideally, I want Coq
to just "guess" correct arguments using types or even names of terms
in a context.
|*)

(*|
Answer
******

If the context (i.e., the list of ``arg1``, ``arg2``, etc.) is simple
enough, you could use type classes to not have to pass arguments
around.
|*)

Reset SectionWithDefs. (* .none *)
(* I have a section with many variables and definitions. *)
Section SectionWithDefs.

  Context {A B C: Type}.

  Class Arg1 : Type := arg1 : A -> B.
  Context `{IArg1 : Arg1}.

  Class Arg2 : Type := arg2 : B -> C.
  Context `{IArg2 : Arg2}.

  (* Functions that uses these variables. *)
  Definition f a := arg2 (arg1 a).

  (* ... *)

End SectionWithDefs.

(* Now I want to use some of these functions. *)
Section AnotherSection.

  Context {A B C: Type}.

  (* Here are the arguments. *)
  Context `{MyIArg1 : Arg1 A B}.
  Context `{MyIArg2 : Arg2 B C}.

  Variable a: A.

  Section CallFunctionWithInstances.

    (* The implicit type class arguments [IArg1] and [IArg2] are
       resolved using instances in scope... *)
    Compute (f a).

  End CallFunctionWithInstances.

End AnotherSection.
