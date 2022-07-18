(*|
#############################################################################
Why does this Coq ``Definition`` fail? Coq Namespace error for Inductive Type
#############################################################################

:Link: https://stackoverflow.com/q/71267447
|*)

(*|
Question
********

I have the following Inductive Type and a test function:
|*)

Inductive parameter : Type :=
| Nop
| OneP : forall A, A -> parameter
| TwoP : forall (A : Type) (r : nat) (b : A), parameter.

Check (TwoP nat 1 5).

Fail Definition test (p : parameter) : option (nat * nat) :=
  match p with
  | TwoP nat x y => Some (x, y)
  | _ => None
  end. (* .fails *)

(*| The test function fails with the error: |*)

Fail Definition test (p : parameter) : option (nat * nat) :=
  match p with
  | TwoP nat x y => Some (x, y)
  | _ => None
  end. (* .unfold .messages *)

(*|
I don't understand why my definition does not work. Is there a
difference between ``nat`` and ``Datatypes.nat``?
|*)

(*|
Answer
******

In Coq, it is not possible to test what a type is. Consider the
following program:
|*)

Fail Definition is_nat (A : Type) : bool :=
  match A with
  | nat => true
  | _   => false
  end. (* .fails *)

(*|
If you try to run this, Coq tells you that the last branch is
redundant, and rejects the definition. The issue is that ``nat`` is
taken to be a variable name, not the ``nat`` data type from the
standard library. Therefore, the first branch matches every type
``A``, and the last branch is redundant. In your example, the pattern
``nat`` ends up masking the data type ``nat``, which is why you end up
seeing the qualified name ``Datatypes.nat``.

One way of solving this issue is to use a type of *codes* instead of
``Type``. For instance:
|*)

Reset Initial. (* .none *)
Inductive type : Type :=
| Bool
| Nat.

Definition type_denote t : Type :=
  match t with
  | Bool => bool
  | Nat => nat
  end.

Coercion type_denote : type >-> Sortclass.

Inductive parameter : Type :=
| Nop
| OneP : forall (A : type), A -> parameter
| TwoP : forall (A : type) (r : nat) (b : A), parameter.

Check (TwoP Nat 1 5).

Definition test (p : parameter) : option (nat * nat) :=
  match p with
  | TwoP Nat x y => Some (x, y)
  | _ => None
  end.

(*|
There are two issues with this solution. First, it requires you to
anticipate all types that you will need in ``parameter``, and add
those in the definition of ``type``. Second, it forces you to program
with dependent types, which can be hard to manipulate. It might be
possible to refactor your definitions to avoid the problem of type
matching altogether, although there is no one-size-fits-all solution
-- it depends on your application.
|*)
