(*|
###################################################
How to dependent match on a list with two elements?
###################################################

:Link: https://stackoverflow.com/q/71919638
|*)

(*|
Question
********

I'm trying to understand dependent types and dependent match in Coq, I
have the code below, at the bottom I have the ``add_pair`` function,
the idea is that I want to receive a (dependent) list with exactly two
elements and return the sum of the two elements in the list. Since the
size of the list is encoded in the type, I should be able to define it
as a total function, but I got an error saying that the ``match`` is
not ``exaustive``

Here is the code
|*)

Set Implicit Arguments.

Module IList.
Section Lists.
  (* o tipo generico dos elementos da lista *)
  Variable A : Set.

  (* data type da lista, recebe um nat que é
       o tamanho da lista *)
  Inductive t : nat -> Set :=
  | nil : t 0                 (* lista vazia, n = 0 *)
  | cons : forall (n : nat), A -> t n -> t (S n). (* cons de uma lista
                                              n = n + 1 *)
  (* concatena duas listas, n = n1 + n2 *)
  Fixpoint concat n1 (ls1 : t n1) n2 (ls2 : t n2) : t (n1 + n2) :=
    match ls1 in t n1 return t (n1 + n2) with
    | nil => ls2
    | cons x ls1' => cons x (concat ls1' ls2)
    end.

  (* computar o tamanho da lista é O(1) *)
  Definition length n (l : t n) : nat := n.
End Lists.
Arguments nil {_}.

(* Isso aqui serve pra introduzir notações pra gente poder
     falar [1;2;3] em vez de (cons 1 (cons 2 (cons 3 nil))) *)
Module Notations.
  Notation "a :: b" := (cons a b) (right associativity, at level 60) : list_scope.
  Notation "[ ]" := nil : list_scope.
  Notation "[ x ]" := (cons x nil) : list_scope.
  Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
  Open Scope list_scope.
End Notations.
Import Notations.

(* Error: Non exhaustive pattern-matching: no clause found for pattern [_] *)
Fail Definition add_pair (l : t nat 2) : nat :=
  match l in (t _ 2) return nat with
  | (cons x (cons y nil)) => x + y
  end. (* .fails *)

End IList.

(*|
Answer
******

Indeed, it is true that the match you provided is exhaustive, but the
pattern-matching algorithm of Coq is limited, and not able to detect
it. The issue, I think, is that it compiles a nested pattern-matching
such as yours (you have two imbricated ``cons``) down to a successions
of elementary pattern-matching (which have patterns of depth at most
one). But in the ``cons`` branch of the outer ``match``, the
information that the index should be ``1`` is lost if you do not
record it explicitly with an equality --- something the current
algorithm is not smart enough to do.

As a possible solution that avoids fiddling with impossible branches,
equalities, and the like, I propose the following:
|*)

Import IList. (* .none *)
Definition head {A n} (l : t A (S n)) : A :=
  match l with
  | cons x _ => x
  end.

Definition tail {A n} (l : t A (S n)) : t A n :=
  match l with
  | cons _ l' => l'
  end.

Definition add_pair (l : t nat 2) : nat :=
  head l + (head (tail l)).

(*|
----

For the record, a solution that *does* fiddle with the impossible
branches and records the information of the index using equalities
(there's probably a nicer version):

.. coq:: none
|*)

Reset head.

Require Import Lia.

Import Notations.

(*||*)

Definition add_pair (l : t nat 2) : nat :=
  match l in t _ m return m = 2 -> nat with
  | [] => fun e => ltac:(lia)
  | x :: l' => fun e =>
                 match l' in t _ m' return m' = 1 -> nat with
                 | [] => fun e' => ltac:(lia)
                 | x' :: l'' => fun e' =>
                                  match l'' in t _ m'' return m'' = 0 -> nat with
                                  | [] => fun _ => x + x'
                                  | _ => fun e'' => ltac:(lia)
                                  end ltac:(lia)
                 end ltac:(lia)
  end eq_refl.

(*|
The interesting part is the use of explicit equalities to record the
value of the index (these are used by the ``lia`` tactic to discard
impossible branches).

----

**Q:** Thank you, this is so cool! I didn't know that you can discard
impossible branches using ltac and never saw this ``ltac:...``, thank
you so much!

**Q:** The ``ltac:(lia)`` after ``end`` are the application of the
``fun e => ...`` functions returned by the match?

**A:** Yes! They are used to generate the right equalities from the
one available in context. For instance the lowest one constructs a
proof of ``m = 1`` from the proof of ``S m = 2`` available in context
(``e``).
|*)
