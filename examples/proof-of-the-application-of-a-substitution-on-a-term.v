(*|
####################################################
Proof of the application of a substitution on a term
####################################################

:Link: https://stackoverflow.com/q/45966001
|*)

(*|
Question
********

I am trying to proof that the application of an empty substitution on
a term is equal to the given term. Here is the code:
|*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Recdef.
Require Import Omega.
Import ListNotations.
Set Implicit Arguments.

Inductive Term : Type :=
| Var : nat -> Term
| Fun : string -> list Term -> Term.

Definition Subst : Type := list (nat * Term).

Definition maybe {X Y: Type} (x : X) (f : Y -> X) (o : option Y): X :=
  match o with
  | None   => x
  | Some a => f a
  end.

Fixpoint lookup {A B : Type} (eqA : A -> A -> bool)
         (kvs : list (A * B)) (k : A) : option B :=
  match kvs with
  | []           => None
  | (x, y) :: xs => if eqA k x then Some y else lookup eqA xs k
  end.

(*| I am trying to proof some properties of this function. |*)

Fixpoint apply (s : Subst) (t : Term) : Term :=
  match t with
  | Var x    => maybe (Var x) id (lookup beq_nat s x)
  | Fun f ts => Fun f (map (apply s ) ts)
  end.

Lemma empty_apply_on_term : forall t, apply [] t = t.
Proof.
  intros. induction t.
  - reflexivity.
Abort. (* .none *)

(*|
I am stuck after the ``reflexivity``. I wanted to do induction on the
list build in a term but if i do so i'ĺl get stuck in a loop.
|*)

(*|
Answer (Tej Chajed)
*******************

The problem is that the automatically generated inductive principle
for the ``Term`` type is too weak, because it has another inductive
type ``list`` inside it (specifically, ``list`` is applied to the very
type being constructed). Adam Chlipala's CPDT gives a good explanation
of what's going on, as well as an example of how to manually build a
better inductive principle for such types in the `inductive types
chapter
<http://adam.chlipala.net/cpdt/html/InductiveTypes.html#lab32>`__.
I've adapted his example ``nat_tree_ind'`` principle for your ``Term``
inductive, using the builtin ``Forall`` rather than a custom
definition. With it, your theorem becomes easy to prove:
|*)

Section Term_ind'.
  Variable P : Term -> Prop.

  Hypothesis Var_case : forall (n : nat), P (Var n).

  Hypothesis Fun_case : forall (s : string) (ls : list Term),
      Forall P ls -> P (Fun s ls).

  Fixpoint Term_ind' (tr : Term) : P tr :=
    match tr with
    | Var n => Var_case n
    | Fun s ls =>
        Fun_case s
                 ((fix list_Term_ind (ls : list Term) : Forall P ls :=
                     match ls with
                     | [] => Forall_nil _
                     | tr' :: rest =>
                         Forall_cons tr' (Term_ind' tr') (list_Term_ind rest)
                     end) ls)
    end.
End Term_ind'.

Lemma empty_apply_on_term : forall t, apply [] t = t.
Proof.
  intros. induction t using Term_ind'; simpl; auto.
  f_equal. induction H; simpl; auto.
  congruence.
Qed.
                                                                                        (*|
Answer (Arthur Azevedo De Amorim)
*********************************

This is a typical trap for beginners. The problem is that your
definition of ``Term`` has a recursive occurrence inside another
inductive type -- in this case, ``list``. Coq does not generate a
useful inductive principle for such types, unfortunately; you have to
program your own. Adam Chlipala's CDPT `has a chapter on inductive
types <http://adam.chlipala.net/cpdt/html/InductiveTypes.html>`__ that
describes the problem. Just look for "nested inductive types".
|*)
