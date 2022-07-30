(*|
##########################
Dependent pattern matching
##########################

:Link: https://proofassistants.stackexchange.com/q/1549
|*)

(*|
Question
********

upd. What I would like to do is to put ``a = RedNode' ..`` into
current context (when using ``refine``). I found this technique here
https://stackoverflow.com/questions/27316254/coq-keeping-information-in-a-match-statement
.

This code works:
|*)

Inductive color : Set := Red | Black.

Inductive rbtree : color -> nat -> Set :=
| Leaf : rbtree Black 0
| RedNode : forall n, rbtree Black n -> nat -> rbtree Black n -> rbtree Red n
| BlackNode : forall c1 c2 n,
    rbtree c1 n -> nat -> rbtree c2 n -> rbtree Black (S n).

Inductive rtree : nat -> Set :=
| RedNode' : forall c1 c2 n, rbtree c1 n -> nat -> rbtree c2 n -> rtree n.

Definition balance1 n (a : rtree n) (data : nat) c2 (t : rbtree c2 n)
  : { c : color & rbtree c (S n) }.
  refine (
      match a with
      | RedNode' _ c0 _ t1 y t2 => fun Heqa => _
      end (eq_refl a)).
Abort. (* .none *)

(*|
My question is in next (slightly modified definition) of ``balance1``:
|*)

Definition balance1 n (a : rtree n) (data : nat) c2 (t : rbtree c2 n)
  : { c : color & rbtree c (S n) }.
  Fail refine (
      match a as ax in rtreen nx return a = ax -> _ with
      | RedNode' _ c0 _ t1 y t2 => fun Heqa => _
      end (eq_refl a)). (* .fails *)
Abort. (* .none *)

(*|
And now Coq does not see that ``a`` and ``ax`` the same because it is
not able to see that ``n`` and ``nx`` are the same.

What is going on and how to express equality between ``n`` and ``nx``
(so, Coq will see I can have ``a = ax``)?

(an example is taken from CPDT).

----

**A:** What I would like to do is to put ``RedNode'`` into current
context (which I see in proof mode when using refine). I found this
here
https://stackoverflow.com/questions/27316254/coq-keeping-information-in-a-match-statement
|*)

(*|
Answer
******

As mentioned by Pierre Castèran, the first definition works because
Coq infers a (useless) return type ``ax = ax -> _``. If you really
want to maintain an equality like ``a = ax`` you need to work a bit
more to have (a modification of) ``a`` and ``ax`` at the same type.
The first possibility is to make explicit the equality between the
natural number indices and rewrite along it in the return clause:
|*)

(* First possibility: take an equation between the indices as argument
   and transport along that equation *)
Definition balance1 n (a : rtree n) (data : nat) c2 (t : rbtree c2 n)
  : { c : color & rbtree c (S n) }.
  refine (
      match a as ax in rtree nx return
            forall (en : n = nx) (ea : eq_rect n rtree a nx en = ax), _
      with
      | RedNode' _ c0 _ t1 y t2 => fun Heqn Heqa => _
      end eq_refl eq_refl).
Abort.

(*|
The second possibility, which is a variant on the first used a lot by
the `Equations <https://github.com/mattam82/Coq-Equations>`__ library,
packs together a natural number with an rtree in a dependent sum, so
that the resulting pair has no dependence and equality can be used
directly on the pairs:
|*)

(* Variant: pack the index n together with the element a : rtree n and
   take an equation between the packed arguments *)

(* Definition and notation for dependent sum *)
Set Primitive Projections.
Record sigma A (B : A -> Type) := mkSig { pr1 : A; pr2 : B pr1 }.
Unset Primitive Projections.
Arguments sigma {A} B.
Arguments mkSig {A} B pr1 pr2.
Notation "'Σ' x .. y , P" :=
  (sigma (fun x => .. (sigma (fun y => P)) ..))
    (at level 200, x binder, y binder, right associativity,
      format "'[  ' '[  ' Σ  x  ..  y ']' ,  '/' P ']'") : type_scope.

Notation "( x , .. , y , z )" :=
  (@mkSig _ _ x .. (@mkSig _ _ y z) ..)
    (right associativity, at level 0,
      format "( x ,  .. ,  y ,  z )").
Notation " x .1 " := (pr1 x) (at level 3, format "x .1").
Notation " x .2 " := (pr2 x) (at level 3, format "x .2").

Definition balance2 n (a : rtree n) (data : nat) c2 (t : rbtree c2 n)
  : { c : color & rbtree c (S n) }.
  refine (
      match a as ax in rtree nx return
            (n, a) = (nx, ax) -> _
      with
      | RedNode' _ c0 _ t1 y t2 => fun Heqa => _
      end eq_refl).
Abort.

(*|
In both cases, actually using these equalities afterwards will be
somewhat painful: you might be able to use them thanks to decidable
equality on natural numbers and its consequences (in particular
``UIP_nat`` in ``Coq.Arith.Peano_dec`` if you use the stdlib).

But more globally, you should consider whether maintining such an
equality will be really useful for proving your goal: ``a`` does not
appear in the conclusion, nor in any other premise so you should not
need to know anything about it beyond its content once
pattern-matched.
|*)
