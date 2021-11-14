(*|
Vector error : The type of this term is a product
=================================================

https://stackoverflow.com/questions/63955903/vector-error-the-type-of-this-term-is-a-product
|*)

(*|
Question
--------

I want last k elements of vector. I wrote this code with reference to
`Coq.Vectors.VectorDef
<https://coq.inria.fr/library/Coq.Vectors.VectorDef.html>`_.
|*)

 Require Import Coq.Reals.Reals.

 (* vector of R *)
 Inductive Euc: nat -> Type:=
 | RO : Euc 0
 | Rn : forall {n: nat}, R -> Euc n -> Euc (S n).

 Notation "[ ]" := RO.
 Notation "[ r1 , .. , r2 ]" := (Rn r1 .. ( Rn r2 RO ) .. ).
 Infix ":::" := Rn (at level 60, right associativity).

 (* return length of vector *)
 Definition EucLength {n} (e: Euc n): nat:= n.

 Definition rectEuc (P: forall {n}, Euc (S n) -> Type)
            (bas: forall a: R, P [a])
            (rect: forall {n} a (v: Euc (S n)), P v -> P (a ::: v)) :=
   fix rectEuc_fix {n} (v: Euc (S n)) : P v :=
     match v with
       | @Rn 0 a v' =>
         match v' with
         | RO => bas a
         | _ => fun devil => False_ind (@IDProp) devil
         end
       | @Rn (S nn') a v' => rect a v' (rectEuc_fix v')
       | _ => fun devil => False_ind (@IDProp) devil
 end.

 (* eliminate last element from vector *)
 Definition EucElimLast :=
   @rectEuc (fun n _ => Euc n) (fun a => []) (fun _ a _ H => a ::: H).

 (* this function has an error *)
 Fail Definition rectEucLastN (P: forall {n}, nat -> Euc n -> Type)
                 (bas: forall {n} k (e: Euc n), P k e)
                 (rect: forall {n} k a (e: Euc (S n)), P k e -> P (S k) (a ::: e)) :=
   fix rectEuc_fix {n} (k: nat) (e: Euc n): P k e :=
     match k,e with
     | S k', e' ::: es =>
       rect k' e' (rectEuc_fix k' (EucElimLast ((EucLength e) - 1) e))
     | 0%nat, e' ::: es => bas k e
     | _, _ => fun devil => False_ind (@IDProp) devil
     end. (* .unfold *)

(*|
The problem is the second line from the bottom of the code.

Why does last pattern have an error?
|*)

(*|
Answer
------

The function term that you see on the branch of `rectEuc` is how you
tell Coq that a pattern-match branch is contradictory. In your first
recursive function, for instance, you use it to say that the first
`v'` cannot be a cons because its length is zero. The reason you are
getting the error in the last branch is because that case is not
contradictory: nothing in the type of your function prevents the case
`k = 0` and `n = 0`.

To write dependently typed programs over indexed families, you often
need to use the *convoy pattern*: to refine the type of an argument
`x` after branching on some expression, your `match` needs to return a
function that abstracts over `x`. For instance, this function computes
the last element of a vector by recursion over its length. In the `S`
branch, we need to know that the length of `v` is connected to `n`
somehow.
|*)

Definition head n (v : Euc (S n)) : R :=
  match v with
  | x ::: _ => x
  end.

Definition tail n (v : Euc (S n)) : Euc n :=
  match v with
  | _ ::: v => v
  end.

Fixpoint last n : Euc (S n) -> R :=
  match n with
  | 0   => fun v => head 0 v
  | S n => fun v => last n (tail _ v)
  end.

(*|
Here is the code for extracting the last `k` elements. Note that its
type uses the `Nat.min` function to specify the length of the result:
the result cannot be larger than the original vector!
|*)

Fixpoint but_last n : Euc (S n) -> Euc n :=
  match n with
  | 0   => fun _ => []
  | S n => fun v => head _ v ::: but_last n (tail _ v)
  end.

Fixpoint snoc n (v : Euc n) (x : R) : Euc (S n) :=
  match v with
  | [] => [x]
  | y ::: v => y ::: snoc _ v x
  end.

Fixpoint lastk k : forall n, Euc n -> Euc (Nat.min k n) :=
  match k with
  | 0 => fun _ _ => []
  | S k => fun n =>
    match n return Euc n -> Euc (Nat.min (S k) n) with
    | 0 => fun _ => []
    | S n => fun v => snoc _ (lastk k _ (but_last _ v)) (last _ v)
    end
  end.

(*|
Personally, I would advise you against programming in this style in
Coq, since it makes it difficult to write programs and understand them
later. It is usually better to write a program without dependent types
and prove after the fact that it has some property that you care
about. (E.g. try to show that reversing a list twice yields the same
list using vectors!) Of course, there are cases where dependent types
are useful, but most of the time they are not needed.
|*)
