(*|
#########################################
Recursive use of typeclass methods in Coq
#########################################

:Link: https://stackoverflow.com/questions/52348668/recursive-use-of-typeclass-methods-in-coq
|*)

(*|
Question
********

Is there a way to use recursion with Coq's typeclasses? Like for e.g.,
in defining show for lists, if you want to call the ``show`` function
for lists recursively, then you will have to use a fixpoint like so:
|*)

Require Import Lists.List. (* .none *)
Import ListNotations. (* .none *)
Require Import Strings.String.
Require Import Strings.Ascii.

Local Open Scope string_scope.

Class Show (A : Type) : Type :=
  {
  show : A -> string
  }.

Section showNormal.
  Instance showList {A : Type} `{Show A} : Show (list A) :=
    {
    show :=
      fix lshow l :=
        match l with
        | nil => "[]"
        | x :: xs => show x ++ " : " ++ lshow xs
        end
    }.
End showNormal.

(*|
Which is all well and good, but what if I want to define some helper
function that I'll use for defining ``Show`` instances? Like I want to
create a more DAZZLING show function called ``magicShow`` that prints
stars around something...
|*)

Definition magicShow {A : Type} `{Show A} (a : A) : string :=
  "** " ++ show a ++ " **".

Fail Instance showMagicList {A : Type} `{Show A} : Show (list A) :=
  {
  show :=
    fix lshow l :=
      match l with
      | nil => "[]"
      | x :: xs => show x ++ " : " ++ magicShow xs
      end
  }. (* .unfold .fails *)

(*|
However, in this case Coq can't find a show instance for the list
``xs`` to pass to ``magicShow``.

Is there any way to do this in general? I.e., can you define a method
for a typeclass using functions that rely upon the typeclass instance
that you're defining?
|*)

(*|
Answer
******

If you must do this, it can be simulated by explicitly using the
constructor of the underlying ``Record`` (since "Typeclasses are
Records", to quote from Software Foundations [`1
<https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html>`__]),
which can be instantiated using the function(s) being defined as a
fixpoint. I'll post three examples and explain where this can be
useful.

The example you posted could be solved like this (all code tested for
Coq 8.10.1):
|*)

Reset Show. (* .none *)
Require Import Strings.String.

Local Open Scope list_scope.
Local Open Scope string_scope.

Class Show (A : Type) : Type :=
  {
  show : A -> string
  }.

Definition magicShow {A : Type} `{Show A} (a : A) : string :=
  "** " ++ show a ++ " **".

Print Show. (* .unfold *)
Check Build_Show. (* .unfold *)
Check @magicShow. (* .unfold *)

Instance showMagicList {A : Type} `{Show A} : Show (list A) :=
  {
  show :=
    fix lshow l :=
      match l with
      | nil => "[]"
      | x :: xs => show x ++ " : " ++ @magicShow _ (@Build_Show _ lshow) xs
      end
  }.

(*|
If you are trying to define several typeclass methods like this, it's
tricky to instantiate the record constructor, but it can be done by
treating the functions as if they were defined by mutual recursion
(although there doesn't necessarily have to be any actual mutual
recursion). Here's a contrived example where ``Show`` now has two
methods. Notice that the typeclass instance is added to the context
with an anonymous ``let-in`` binding. Evidently, this is enough to
satisfy Coq's typeclass resolution mechanism.
|*)

Reset Show. (* .none *)
Require Import Strings.String.

Local Open Scope list_scope.
Local Open Scope string_scope.

Class Show (A : Type) : Type :=
  {
  show1 : A -> string;
  show2 : A -> string
  }.

Definition magicShow1 {A : Type} `{Show A} (a : A) : string :=
  "** " ++ show1 a ++ " **".

Definition magicShow2 {A : Type} `{Show A} (a : A) : string :=
  "** " ++ show2 a ++ " **".

Fixpoint show1__list {A : Type} `{Show A} (l : list A) : string :=
  let _ := (@Build_Show _ show1__list show2__list) in
  match l with
  | nil => "[]"
  | x :: xs => show1 x ++ " : " ++ magicShow1 xs
  end
with
show2__list {A : Type} `{Show A} (l : list A) : string :=
  let _ := (@Build_Show _ show1__list show2__list) in
  match l with
  | nil => "[]"
  | x :: xs => show1 x ++ " : " ++ magicShow2 xs
  end.

Instance showMagicList {A : Type} `{Show A} : Show (list A) :=
  {
  show1 := show1__list;
  show2 := show2__list
  }.

(*|
So why would you want to do this? A good example is when you are
defining decidable equality on (rose) trees. In the middle of the
definition, we have to recursively appeal to decidable equality of
``list (tree A)``. We would like to use the standard library helper
function ``Coq.Classes.EquivDec.list_eqdec`` [`2
<https://coq.inria.fr/library/Coq.Classes.EquivDec.html>`__], which
shows how to pass decidable equality on a type ``A`` to ``list A``.
Since ``list_eqdec`` requires a typeclass instance (the very one we
are in the middle of defining), we have to use the same trick above:
|*)

Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Utils.

Set Implicit Arguments.
Generalizable Variables A.

Inductive tree (A : Type) : Type :=
| leaf : A -> tree A
| node : list (tree A) -> tree A.

Program Instance tree_eqdec `(eqa : EqDec A eq) : EqDec (tree A) eq :=
  { equiv_dec := fix tequiv t1 t2 :=
      let _ := list_eqdec tequiv in
      match t1, t2 with
      | leaf a1, leaf a2 =>
        if a1 == a2 then in_left else in_right
      | node ts1, node ts2 =>
        if ts1 == ts2 then in_left else in_right
      | _, _ => in_right
      end
  }.

Solve Obligations with unfold not, equiv, complement in *;
  program_simpl; intuition (discriminate || eauto).

Next Obligation.
  destruct t1;
    destruct t2;
    (program_simpl || unfold complement, not, equiv in *; eauto).
Qed.

Solve Obligations with split;
(intros; try unfold complement, equiv ; program_simpl).

(*|
Commentary: There is no constructor for creating a record of type
``EqDec`` (since it only has one class method), so to convince Coq
that ``list (tree A)`` has decidable equality, the invocation is
simply ``list_eqdec tequiv``. For the uninitiated, ``Program`` here is
simply allowing for holes in the definition of the instance to be
filled in later as ``Obligation``'s, which is more convenient than
writing the appropriate proofs inline.
|*)
