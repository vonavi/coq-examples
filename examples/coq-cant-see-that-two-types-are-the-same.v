(*|
#########################################
Coq can't see that two types are the same
#########################################

:Link: https://stackoverflow.com/q/32487915
|*)

(*|
Question
********

I am trying to define the ``rev`` function on a vector, the size of it
is embedded in it and I can't figure out how to define the ``rev``
function on it.

Here is my type definition:
|*)

Inductive vect {X : Type} : nat -> Type -> Type :=
| Nil  : vect 0 X
| Cons : forall n, X -> vect n X -> vect (S n) X.

(*| I have defined some useful functions on it: |*)

Fixpoint app {X : Type} {n m : nat} (v1 : vect n X) (v2 : vect m X) :
  vect (n + m) X :=
  match v1 with
  | Nil => v2
  | Cons _ x xs => Cons _ x (app xs v2)
  end.

Infix ":::" := (Cons _) (at level 60).
Notation "{{ }}" := Nil (format "{{ }}").
Notation "{{ x }}" := (Cons _ x Nil).

Fixpoint fold_left {X Y : Type} {n : nat}
         (f : Y -> X -> Y) (acc : Y) (v : vect n X) : Y :=
  match v with
  | Nil => acc
  | Cons _ x xs => fold_left f (f acc x) xs
  end.

(*|
And now, I want to define ``rev``. My first tentative was through
``fold_left`` but it turned out to be a total failure.
|*)

Fail Fixpoint rev {X : Type} {n : nat} (v : @vect X n X) : @vect X n X :=
  fold_left (fun (X : Type) (k : nat) (acc : vect k X) (x : X) =>
               x ::: acc) {{ }} v. (* .fails *)

(*| I don't understand the error |*)

Fail Fixpoint rev {X : Type} {n : nat} (v : @vect X n X) : @vect X n X :=
  fold_left (fun (X : Type) (k : nat) (acc : vect k X) (x : X) =>
               x ::: acc) {{ }} v. (* .unfold .messages *)

(*|
----

My second tentative is almost good but Coq can't see that ``S n = (n +
1)`` natively and I don't know how to tell Coq so.
|*)

Fail Fixpoint rev {X : Type} {n : nat} (v : @vect X n X) : @vect X n X :=
  match v in (vect n X) return (vect n X) with
  | Nil => Nil
  | Cons _ x xs => app (rev xs) {{ x }}
  end. (* .fails *)

(*| The error being |*)

Fail Fixpoint rev {X : Type} {n : nat} (v : @vect X n X) : @vect X n X :=
  match v in (vect n X) return (vect n X) with
  | Nil => Nil
  | Cons _ x xs => app (rev xs) {{ x }}
  end. (* .unfold .messages *)

(*|
Answer
******

::

    Fixpoint rev {X : Type} {n : nat} (v : @vect X n X) : @vect X n X :=
      fold_left (fun (X : Type) (k : nat) (acc : vect k X) (x : X) =>
                   x ::: acc) {{ }} v.

The first explicit argument to ``fold_left`` must have a type of the
form ``?1 -> ?2 -> ?1``, i.e. a function of two arguments whose return
type is the same as the first argument. [Dependent] "product" is Coq
terminology for a function. You're passing a term of the form ``fun
(X:Type) b c d => …``, so ``?1`` is ``Type``, and the term ``fun c d
=> …`` (which obviously has a product type) must have the type ``?``
given the context, so it must have the type ``Type``, i.e. it must be
a sort.

If you try to fix this, you'll realize that your ``fold_left``
function doesn't work here: you need to vary the length of the vector
during the iteration, but the iterator argument to ``fold_left`` has a
type that's constant during the iteration. With the ``fold_left``
function that you have, if you start from the accumulator ``Nil``,
which is a vector of length ``0``, you'll end up with a result of the
same type, again a vector of length ``0``.

I haven't thought about how to define a more general iterator that
would let you define ``rev``, but I'm sure it's possible.

----

As to your second attempt, the problem with ``vect (n0 + 1) X`` and
``vect (S n0) X`` is that they are not the same type, because ``n0 +
1`` is not convertible to ``S n0``. The terms ``n0 + 1`` are equal but
not convertible, and terms used as types are only interchangeable if
they're convertible.

If two types are equal, you can write a function that "casts" a term
of one type into a term of the other type. In fact, the general
function to do that is ``eq_rect``, the destructor for the equality
type family. You may find it to define a specialized function to cast
a vector to a vector of provably-but-not-necessarily-convertibly equal
length.
|*)

Definition vect_eq_nat {X : Type} {m n : nat} (H : m = n) v :=
  eq_rect _ (fun k => @vect X k X) v _ H.

(*|
If the usage of ``eq_rect`` doesn't immediately stand out, you can
define such functions through tactics. Just be sure that you're
defining a function that not only has the right type but has the
desired result, and make the definition transparent.
|*)

Reset vect_eq_nat. (* .none *)
Definition vect_eq_nat {X : Type} {m n : nat} :
  m = n -> @vect X m X -> @vect X n X.
Proof.
  intros. rewrite <- H. exact X0.
Defined.

Print vect_eq_nat.

(*|
You can also use the ``Program`` vernacular to mix proofs and terms.
|*)

Require Import Coq.Program.Tactics.
Require Import Lia.

Program Definition vect_plus_comm {X : Type} {n : nat} (v : @vect X (n+1) X) :
  @vect X (S n) X := vect_eq_nat _ v.
Solve Obligation 0 with (intros; lia).

(*| Now you can use this auxiliary definition to define ``rev``. |*)

Fixpoint rev {X : Type} {n : nat} (v : @vect X n X) : @vect X n X :=
  match v in (vect n X) return (vect n X) with
  | Nil => Nil
  | Cons _ x xs => vect_plus_comm (app (rev xs) (Cons _ x Nil))
  end.

(*|
You can use ``Program Fixpoint`` to define ``rev`` directly, once
you've put that casting step in place. The one proof obligation is the
equality between ``S n0`` and ``n0 + 1``.
|*)

Program Fixpoint rev' {X : Type} {n : nat} (v : @vect X n X) : @vect X n X :=
  match v in (vect n X) return (vect n X) with
  | Nil => Nil
  | Cons _ x xs => vect_eq_nat _ (app (rev' xs) (Cons _ x Nil))
  end.
Solve Obligation 0 with (intros; lia).

(*|
----

**A:** A type for ``fold_left`` that works is
|*)

Reset fold_left. (* .none *)
Require Import PeanoNat. (* .none *)
Fixpoint fold_left {X : Type} {Y : nat -> Type} {n k : nat}
         (f : forall m, Y m -> X -> Y (S m)) (acc : Y k)
         (v : @vect X n X) : Y (n + k) :=
  match v with
  | Nil => eq_rect_r Y acc (Nat.add_0_l k)
  | Cons n' x v' =>
      eq_rect_r Y (fold_left f (f k acc x) v') (Nat.add_succ_comm n' k)
  end.
