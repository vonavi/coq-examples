(*|
##########################
Proving termination in Coq
##########################

:Link: https://stackoverflow.com/q/19507311
|*)

(*|
Question
********

How can I prove termination for ``size_prgm``? I tried, but can't come
up with a well founded relation to pass to ``Fix``.
|*)

Require Import List. (* .none *)
Inductive Stmt : Set :=
| assign : Stmt
| if' : list Stmt -> list Stmt -> Stmt.

Fail Fixpoint size_prgm (p : list Stmt) : nat :=
  match p with
  | nil    => 0
  | s :: t => size_prgm t +
                match s with
                | assign  => 1
                | if' b0 b1 => S (size_prgm b0 + size_prgm b1)
                end
  end. (* .fails *)

(*|
Answer (gallais)
****************

The termination oracle is quite better than what it used to be.
Defining a function ``sum_with`` using ``fold_left`` and feeding it
the recursive call to ``size_prgm`` works perfectly well.
|*)

Reset Initial. (* .none *)
Require Import List.

Inductive Stmt : Set :=
| assign : Stmt
| if' : list Stmt -> list Stmt -> Stmt.

Definition sum_with {A : Type} (f : A -> nat) (xs : list A) : nat :=
  fold_left (fun n a => n + f a) xs 0.

Fixpoint size_prgm (p : Stmt) : nat :=
  match p with
  | assign    => 1
  | if' b0 b1 => sum_with size_prgm b1 + sum_with size_prgm b0
  end.

(*|
Answer (Vinz)
*************

Short answer, since I don't have much time right now (I'll try to get
back to you later): this is a really usual (and silly) problem that
every Coq user has to experience one day.

If I recall correctly, there is two "general" solutions to this
problem and lots of very specific ones. For the two former:

1. build a inner fixpoint: I don't really remember how to do this
   properly.
2. use a mutual recursive type: The issue with your code is that you
   use ``list Stmt`` in your ``Stmt`` type, and Coq is not able to
   compute the induction principle you have in mind. But you could use
   a time like
|*)

Reset Initial. (* .none *)
Inductive Stmt : Set :=
| assign : Stmt
| if' : list_Stmt -> list_Stmt -> Stmt
with list_Stmt : Set :=
| Nil_Stmt : list_Stmt
| Cons_Stmt : Stmt -> list_Stmt -> list_Stmt.

(*|
Now write your function over this type and a bijection between this
type and your original ``Stmt`` type.
|*)
