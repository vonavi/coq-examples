(*|
#######################################################
Representing Higher-Order Functors as Containers in Coq
#######################################################

:Link: https://stackoverflow.com/questions/54864518/representing-higher-order-functors-as-containers-in-coq
|*)

(*|
Question
********

Following `this
<https://people.cs.kuleuven.be/~tom.schrijvers/Research/papers/haskell2014.pdf>`__
approach, I'm trying to model functional programs using effect
handlers in Coq, based on an implementation in Haskell. There are two
approaches presented in the paper:

- Effect syntax is represented as a functor and combined with the free
  monad.

  .. code-block:: haskell

      data Prog sig a = Return a | Op (sig (Prog sig a))

  Due to the termination check not liking non-strictly positive
  definitions, this data type can't be defined directly. However,
  containers can be used to represent strictly-positive functors, as
  described in `this paper <https://arxiv.org/pdf/1805.08059.pdf>`__.
  This approach works but since I need to model a scoped effect that
  requires explicit scoping syntax, mismatched begin/end tags are
  possible. For reasoning about programs, this is not ideal.

- The second approach uses higher-order functors, i.e. the following
  data type.

  .. code-block:: haskell

      data Prog sig a = Return a | Op (sig (Prog sig) a)

  Now sig has the type ``(* -> *) -> * -> *``. The data type can't be
  defined in Coq for the same reasons as before. I'm looking for ways
  to model this data type, so that I can implement scoped effects
  without explicit scoping tags.

My attempts of defining a container for higher-order functors have not
been fruitful and I can't find anything about this topic. I'm thankful
for pointers in the right direction and helpful comments.

Edit: One example of scoped syntax from the paper that I would like to
represent is the following data type for exceptions.

.. code-block:: haskell

    data HExc e m a = Throw' e | forall x. Catch' (m x) (e -> m x) (x -> m a)

Edit2: I have merged the suggested idea with my approach.
|*)

Inductive Ext Shape (Pos : Shape -> Type -> Type -> Type)
          (F : Type -> Type) A :=
  ext : forall s, (forall X, Pos s A X -> F X) -> Ext Shape Pos F A.

Class HContainer (H : (Type -> Type) -> Type -> Type) :=
  {
  Shape   : Type;
  Pos     : Shape -> Type -> Type -> Type;
  to      : forall M A, Ext Shape Pos M A -> H M A;
  from    : forall M A, H M A -> Ext Shape Pos M A;
  to_from : forall M A (fx : H M A), @to M A (@from M A fx) = fx;
  from_to : forall M A (e : Ext Shape Pos M A), @from M A (@to M A e) = e
  }.

Section Free.
  Variable H : (Type -> Type) -> Type -> Type.

  Inductive Free (HC__F : HContainer H) A :=
  | pure : A -> Free HC__F A
  | impure : Ext Shape Pos (Free HC__F) A -> Free HC__F A.
End Free.

(*|
The code can be found `here
<https://gist.github.com/nbun/3e3f2198eae099c8409bf41c04271b3c>`__.
The Lambda Calculus example works and I can prove that the container
representation is isomorphic to the data type. I have tried to to the
same for a simplified version of the exception handler data type but
it does not fit the container representation.

Defining a smart constructor does not work, either. In Haskell, the
constructor works by applying ``Catch'`` to a program where an
exception may occur and a continuation, which is empty in the
beginning.

.. code-block:: haskell

    catch :: (HExc <: sig) => Prog sig a -> Prog sig a
    catch p = inject (Catch' p return)

The main issue I see in the Coq implementation is that the shape needs
to be parameterized over a functor, which leads to all sorts of
problems.
|*)

(*|
Answer (Li-yao Xia)
*******************

This answer gives more intuition about how to derive containers from
functors than my previous one. I'm taking quite a different angle, so
I'm making a new answer instead of revising the old one.

Simple recursive types
======================

Let's consider a simple recursive type first to understand
non-parametric containers, and for comparison with the parameterized
generalization. Lambda calculus, without caring about scopes, is given
by the following functor:
|*)

Inductive LC_F (t : Type) : Type :=
| App : t -> t -> LC_F t
| Lam : t -> LC_F t.
Reset LC_F. (* .none *)

(*|
There are two pieces of information we can learn from this type:

- The *shape* tells us about the constructors (``App``, ``Lam``), and
  potentially also auxiliary data not relevant to the recursive nature
  of the syntax (none here). There are two constructors, so the shape
  has two values. ``Shape := App_S | Lam_S`` (``bool`` also works, but
  declaring shapes as standalone inductive types is cheap, and named
  constructors also double as documentation.)
- For every shape (i.e., constructor), the *position* tells us about
  recursive occurences of syntax in that constructor. ``App`` contains
  two subterms, hence we can define their two positions as booleans;
  ``Lam`` contains one subterm, hence its position is a unit. One
  could also make ``Pos (s : Shape)`` an indexed inductive type, but
  that is a pain to program with (just try).

.. coq::
|*)

(* Lambda calculus *)
Inductive ShapeLC :=
| App_S    (* The shape   App _ _ *)
| Lam_S.   (* The shape   Lam _ *)

Definition PosLC s :=
  match s with
  | App_S => bool
  | Lam_S => unit
  end.

(*|
Parameterized recursive types
=============================

Now, properly scoped lambda calculus:
|*)

Inductive LC_F (f : Type -> Type) (a : Type) : Type :=
| App : f a -> f a -> LC_F f a
| Lam : f (sum unit a) -> LC_F f a.

(*|
In this case, we can still reuse the ``Shape`` and ``Pos`` data from
before. But this functor encodes one more piece of information: how
each position changes the type parameter ``a``. I call this parameter
the context (``Ctx``).
|*)

Definition CtxLC (s : ShapeLC) : PosLC s -> Type -> Type :=
  match s with
  | App_S => fun _ a => a (* subterms of App reuse the same context *)
  | Lam_S => fun _ a => sum unit a
    (* Lam introduces one variable in the context of its subterm *)
  end.

(*|
This container ``(ShapeLC, PosLC, CtxLC)`` is related to the functor
``LC_F`` by an isomorphism: between the sigma ``{ s : ShapeLC & forall
p : PosLC s, f (CtxLC s p a) }`` and ``LC_F a``. In particular, note
how the function ``y : forall p, f (CtxLC s p)`` tells you exactly how
to fill the shape ``s = App_S`` or ``s = Lam_S`` to construct a value
``App (y true) (y false) : LC_F a`` or ``Lam (y tt) : LC_F a``.

My previous representation encoded ``Ctx`` in some additional type
indices of ``Pos``. The representations are equivalent, but this one
here looks tidier.

Exception handler calculus
==========================

We'll consider just the ``Catch`` constructor. It has four fields: a
type ``X``, the main computation (which returns an ``X``), an
exception handler (which also recovers an ``X``), and a continuation
(consuming the ``X``).
|*)

Inductive Exc_F (E : Type) (F : Type -> Type) (A : Type) :=
| ccatch : forall X, F X -> (E -> F X) -> (X -> F A) -> Exc_F E F A.

(*|
The shape is a single constructor, but you must include ``X``.
Essentially, look at all the fields (possibly unfolding nested
inductive types), and keep all the data that doesn't mention ``F``,
that's your shape.
|*)

Inductive ShapeExc :=
| ccatch_S (X : Type). (* The shape   ccatch X _ (fun e => _) (fun x => _) *)

(* equivalently, Definition ShapeExc := Type. *)

(*|
The position type lists all the ways to get an ``F`` out of an
``Exc_F`` of the corresponding shape. In particular, a position
contains the arguments to apply functions with, and possibly any data
to resolve branching of any other sort. In particular, you need to
know the exception type to store exceptions for the handler.

.. coq:: none
|*)

Set Implicit Arguments.
Set Contextual Implicit.
Variable getX : ShapeExc -> Type.

(*||*)

Inductive PosExc (E : Type) (s : ShapeExc) : Type :=
| main_pos                      (* F X *)
| handle_pos (e : E)            (* E -> F X *)
| continue_pos (x : getX s).    (* X -> F A *)

(* The function getX takes the type X contained in a ShapeExc value,
   by pattern-matching: getX (ccatch_S X) := X. *)

(*|
Finally, for each position, you need to decide how the context
changes, i.e., whether you're now computing an ``X`` or an ``A``:
|*)

Definition Ctx (E : Type) (s : ShapeExc) (p : PosExc E s) : Type -> Type :=
  match p with
  | main_pos | handle_pos _ => fun _ => getX s
  | continue_pos _ => fun A => A
  end.

(*|
Using the conventions from `your code
<https://gist.github.com/nbun/3e3f2198eae099c8409bf41c04271b3c>`__,
you can then encode the ``Catch`` constructor as follows:

.. code-block:: coq

    Definition Catch' {E X A}
               (m : Free (C__Exc E) X)
               (h : E -> Free (C__Exc E) X)
               (k : X -> Free (C__Exc E) A) : Free (C__Exc E) A :=
      impure (@ext (C__Exc E) (Free (C__Exc E)) A (ccatch_S X)
                   (fun p =>
                      match p with
                      | main_pos => m
                      | handle_pos e => h e
                      | continue_pos x => k x
                      end)).

    (* I had problems with type inference for some reason, hence @ext is
       explicitly applied *)

Full gist
https://gist.github.com/Lysxia/6e7fb880c14207eda5fc6a5c06ef3522

----

**Q:** This is a really helpful answer and detailed walk-through (and,
again, a good example of why I like the Coq/FP-community so much ; )).
Is there any citable publication/reference you've read/wrote that
gives similar details to the the usage of containers for more
complicated functors? Since you named your first gist
"FreeIndexedMonad", I was wondering if `Indexed Containers
<http://strictlypositive.org/indexed-containers.pdf>`__ are related?
After a first glance I couldn't tell if they are also capable of
handling similar examples to the one above.

**A:** Thanks! This paper is indeed closely related! The two
presentations here and in the paper are basically equivalent. They
actually represent higher-order functors ``(I -> Type) -> (O ->
Type)`` and you can generalize ``Ctx s : Pos s -> Type -> Type`` to
``Ctx s : Pos s -> O -> I`` to do the same here. Sadly I don't know
any publication to point to offhand otherwise.
|*)

(*|
Answer (Li-yao Xia)
*******************

The main trick in the "first-order" free monad encoding is to encode a
functor ``F : Type -> Type`` as a container, which is essentially a
dependent pair ``{ Shape : Type ; Pos : Shape -> Type }``, so that,
for all ``a``, the type ``F a`` is isomorphic to the sigma type ``{ s
: Shape & Pos s -> a }``.

Taking this idea further, we can encode a higher-order functor ``F :
(Type -> Type) -> (Type -> Type)`` as a container ``{ Shape : Type &
Pos : Shape -> Type -> (Type -> Type) }``, so that, for all ``f`` and
``a``, ``F f a`` is isomorphic to ``{ s : Shape & forall x : Type, Pos
s a x -> f x }``.

I don't quite understand what the extra ``Type`` parameter in ``Pos``
is doing there, but It Works(TM), at least to the point that you can
construct some lambda calculus terms in the resulting type.

For example, the lambda calculus syntax functor:
|*)

Reset LC_F. (* .none *)
Inductive LC_F (f : Type -> Type) (a : Type) : Type :=
| App : f a -> f a -> LC_F f a
| Lam : f (sum unit a) -> LC_F f a.

(*| is represented by the container ``(Shape, Pos)`` defined as: |*)

(* LC container *)

Reset Shape. (* .none *)
(* Two values in bool = two constructors in LC_F *)
Definition Shape : Type := bool.

Inductive App_F (a : Type) : Type -> Type :=
| App_ (b : bool) : App_F a a.

Inductive Lam_F (a : Type) : Type -> Type :=
| Lam_ : Lam_F a (sum unit a).

Definition Pos (b : bool) : Type -> (Type -> Type) :=
  match b with
  | true => App_F
  | false => Lam_F
  end.

(*|
Then the free-like monad ``Prog`` (implicitly parameterized by
``(Shape, Pos)``) is given by:
|*)

Inductive Prog (a : Type) : Type :=
| Ret : a -> Prog a
| Op (s : Shape) : (forall b, Pos s a b -> Prog b) -> Prog a.

(*|
Having defined some boilerplate, you can write the following example:

.. code-block:: coq

    (* \f x -> f x x *)
    Definition omega {a} : LC a :=
      Lam (* f *) (Lam (* x *)
                     (let f := Ret (inr (inl tt)) in
                      let x := Ret (inl tt) in
                      App (App f x) x)).

Full gist:
https://gist.github.com/Lysxia/5485709c4594b836113736626070f488
|*)
