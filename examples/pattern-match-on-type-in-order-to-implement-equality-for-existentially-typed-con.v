(*|
###############################################################################################
Pattern-match on type in order to implement equality for existentially typed constructor in Coq
###############################################################################################

:Link: https://stackoverflow.com/q/42140009
|*)

(*|
Question
********

Let's say I have again a small problem with my datatype with an
existential quantified component. This time I want to define when two
values of type ``ext`` are equal.
|*)

Inductive ext (A : Set) :=
| ext_ : forall (X : Set), option X -> ext A.

Fail Definition ext_eq (A : Set) (x y : ext A) : Prop :=
  match x with
  | ext_ _ ox => match y with
                 | ext_ _ oy => (* only when they have the same types *)
                     ox = oy
                 end
  end.

(*|
What I'd like to do is somehow distinguish between the cases where the
existential type is actually same and where it's not. Is this a case
for ``JMeq`` or is there some other way to accomplish such a case
distinction?

I googled a lot, but unfortunately I mostly stumbled upon posts about
dependent pattern matching.

I also tried to generate a (boolean) scheme with ``Scheme Equality for
ext``, but this wasn't successful because of the type argument.
|*)

(*|
Answer
******

    What I'd like to do is somehow distinguish between the cases where
    the existential type is actually same and where it's not.

This is not possible as Coq's logic is compatible with the univalence
axiom which says that isomorphic types are equal. So even though
``(unit * unit)`` and ``unit`` are syntactically distinct, they cannot
be distinguished by Coq's logic.

A possible work-around is to have a datatype of codes for the types
you are interested in and store that as an existential. Something like
this:
|*)

Reset Initial. (* .none *)
Inductive Code : Type :=
| Nat : Code
| List : Code -> Code.

Fixpoint meaning (c : Code) :=
  match c with
  | Nat     => nat
  | List c' => list (meaning c')
  end.

Inductive ext (A : Set) :=
| ext_ : forall (c : Code), option (meaning c) -> ext A.

Lemma Code_eq_dec : forall (c d : Code), {c = d} + {c <> d}.
Proof.
  intros c. induction c; intros d; destruct d.
  - left. reflexivity.
  - right. inversion 1.
  - right. inversion 1.
  - destruct (IHc d).
    + left. congruence.
    + right. inversion 1. contradiction.
Defined.

Definition ext_eq (A : Set) (x y : ext A) : Prop.
  refine (match x with
          | @ext_ _ c ox =>
              match y with
              | @ext_ _ d oy =>
                  match Code_eq_dec c d with
                  | left eq   => _
                  | right neq => False
                  end end end).
  subst. exact (ox = oy).
Defined.

(*|
However this obviously limits quite a lot the sort of types you can
pack in an ``ext``. Other, more powerful, languages (e.g. equipped
with `Induction-recursion
<https://en.wikipedia.org/wiki/Induction-recursion>`__) would give you
more expressive power.

----

**A:** Nice workaround! Let me add a couple comments: (1)
``Code_eq_dec`` can be *literally* defined using the ``decide
equality`` tactic, which will really shine when we start adding more
data constructors into ``Code``; (2) ``ext_`` can be destructed using
the ``let`` expression (since it has only one constructor), which
makes the code a bit more concise: ``let (c,ox) := x in ...``
|*)
