(*|
Proving that s-expressions printing is injective
================================================

:Link: https://stackoverflow.com/questions/69617959/proving-that-s-expressions-printing-is-injective
|*)

(*|
Question
--------

I defined a type of s-expressions and it's printing functions.

.. coq:: none
|*)

Require Import Lists.List Strings.String.
Import ListNotations.

(*||*)

Inductive sexp : Set :=
  K : string -> list sexp -> sexp.

Fixpoint sexpprint (s : sexp) : list string :=
  match s with
    K n l => ["("%string]++[n]++(List.concat (map sexpprint l))++[")"%string]
  end.

(*|
(Yes, I understand it can be just string, not the list of strings, but
Coq have small amount of theorems for working with strings, but a big
amount for working with lists.)
|*)

(* more usual function *)
Fixpoint sexpprint' (s:sexp) :string :=
  match s with
    K n l => "(" ++ n ++ (String.concat "" (map sexpprint' l)) ++ ")"
  end.

(*|
And I've got stuck trying to prove this theorem:
|*)

Theorem sexpprint_inj s1 s2 :
  sexpprint s1 = sexpprint s2 -> s1 = s2.

(*|
Maybe there are some sources which can help me to plan the theorem's
proof? (books/articles/codes) How to prove it? (Maybe I need a special
kind of inductive principle, could you formulate its statement?)
|*)

(*|
Answer
------

The type ``sexp`` is an example of a *nested inductive type*, where
one of the recursive occurrences appears inside of another induction.
Such types are hard to work with in Coq, because the induction
principles that it generates by default are not useful. However, you
can fix this issue by writing down your own induction principle by
hand. Here is one possibility:

.. coq:: none
|*)

Reset sexp.

Require Import Coq.Lists.List Coq.Strings.String.
Import ListNotations.

(*||*)

Unset Elimination Schemes.
Inductive sexp : Type :=
| K : string -> list sexp -> sexp.
Set Elimination Schemes.

Definition tuple (T : sexp -> Type) (es : list sexp) :=
  fold_right (fun e R => T e * R)%type unit es.

Definition sexp_rect
           (T : sexp -> Type)
           (H : forall s es, tuple T es -> T (K s es)) :
  forall e, T e :=
  fix outer (e : sexp) : T e :=
    match e with
    | K s es =>
      let fix inner (es : list sexp) : tuple T es :=
          match es return tuple T es with
          | [] => tt
          | e :: es => (outer e, inner es)
          end in
      H s es (inner es)
    end.

Definition sexp_ind (T : sexp -> Prop) := sexp_rect T.

(*|
With this induction principle, it is now possible to prove your lemma
(exercise!), but you will need to generalize its statement a bit.

For a deeper discussion about these nested inductives, you can have a
look at `CPDT
<http://adam.chlipala.net/cpdt/html/Cpdt.InductiveTypes.html>`_.
|*)
