(*|
################################################
What is Coq's type system doing in this example?
################################################

:Link: https://stackoverflow.com/q/45362643
|*)

(*|
Question
********

I'm confused about the behavior of Coq's type system on the match
portion of the proof term in the definition of h below:
|*)

Set Implicit Arguments.

Definition h := fun (a b : nat) (e : a = b) =>
                  (fun (x y : nat) (HC : b = y) (H : x = y) =>
                     (match H in (_ = y0) return (b = y0 -> b = x) with
                      | @eq_refl _ _ => fun HC0 : b = x => HC0
                      end HC)) a b (eq_refl b) e.

(*| ``Check h`` tells us the overall type is |*)

Check h. (* .unfold .messages *)

(*|
Since the type of ``H`` is ``x = y``, it looks like the match will
return a term of type ``b = y -> b = x`` due to the return clause.
After applying the various terms that follow, we get the expected type
for ``h``.

However, fun ``HC0 : b = x => HC0`` is the identity function of type
``b = x -> b = x``. I don't believe there is any coercion that would
force ``b = x -> b = x`` to be recognized as type ``b = y -> b = x``.

My best guess is that the constructor for ``H``, being ``@eq_refl nat
x`` of type ``x = x``, is unique. Since ``H`` is also of type ``x =
y``, the names ``x`` and ``y`` bind to the same term. Thus, the type
system decides ``b = x -> b = x`` is of type ``b = y -> b = x``. Is
this close? Is this kind of behavior explained or documented
somewhere? I looked at iota reduction, but I don't think that is
correct.
|*)

(*|
Answer
******

That is pretty much it. This behavior is documented (look for "the
``match ... with ... end`` construction" in `the manual
<https://coq.inria.fr/refman/language/cic.html#the-match-with-end-construction>`__),
although understanding what is going on there can be a bit daunting.

First, recall how a typical ``match`` is checked in Coq:
|*)

Inductive list (T : Type) :=
| nil : list T
| cons : T -> list T -> list T.

Definition tail (T : Type) (l : list T) : list T :=
  match l with
  | nil _     => @nil T
  | cons x l' => l'
  end.

(*|
Coq checks (1) that every constructor of the ``list`` type has a
corresponding branch in the ``match``, and (2) that each branch has
the same type (in this case, ``list T``) assuming that the constructor
arguments introduced in each branch have the appropriate types (here,
assuming that ``x`` has type ``T`` and ``l'`` has type ``list T`` in
the second branch).

In such simple cases, the type used to check each branch is exactly
the same as the type of the whole match expression. However, this is
*not* always true: sometimes, Coq uses a more specialized type based
on information that it extracts from the branch that it is checking.
This happens often when doing case analysis on *indexed* inductive
types, like ``eq``:
|*)

Inductive eq (T : Type) (x : T) : T -> Prop :=
| eq_refl : @eq T x x.

(*|
(The ``=`` notation is just infix syntax sugar for ``eq``.)

The arguments of an inductive type given to the right of the colon are
special in Coq: they are known as *indices*. Those appearing to the
left (in this case, ``T`` and ``x``) are known as *parameters*.
Parameters must all be different in the declaration of an inductive
type, and must match exactly the ones used in the result of all
constructors. For instance, consider the following illegal snippet:
|*)

Fail Inductive eq' (T : Type) (x : T) : T -> Type :=
| eq_refl' : @eq' nat 4 3. (* .fails *)

(*|
Coq rejects this example because it finds ``nat`` instead of ``T`` in
the result of the ``eq_refl'`` constructor.

Indices, on the other hand, do not have this restriction: the indices
appearing on the return type of constructors can be any expression of
the appropriate type. Furthermore, that expression may differ
depending on the constructor we are at. Because of this, Coq allows
the return type of each branch to vary depending on the choice of the
index of each branch. Consider the following slightly simplified
version of your original example.
|*)

Reset h. (* .none *)
Definition h (a b : nat) (e : a = b) : b = a :=
  match e in _ = x return x = a with
  | eq_refl => eq_refl : a = a
  end.

(*|
Since the second argument to ``eq`` is an index, it could in principle
vary depending on the constructor used. Since we only find out what
that index actually is when we look into the constructor that was
used, Coq allows the return type of the match to depend on that index:
the ``in`` clause of the match gives names to all the indices of an
inductive type, and these names become bound variables that can be
used in the ``return`` clause.

When typing a branch, Coq finds out what the values of the indices
were, and substitutes those values for the variables declared in the
``in`` clause. This match has only one branch, and that branch forces
the index to be equal to the second argument in the type of ``e`` (in
this case, ``a``). Thus, Coq tries to make sure that the type of that
branch is ``a = a`` (that is, ``x = a`` with ``a`` substituted for
``x``). We can thus simply provide ``eq_refl : a = a`` and we are
done.

Now that Coq checked that all branches are correct, it assigns to the
entire match expression the type of the ``return`` clause with the
index of the type of ``e`` substituted for ``x``. This variable ``e``
has type ``a = b``, the index is ``b``, and thus the resulting type is
``b = a`` (that is, ``x = a`` with ``b`` substituted for ``x``).

`This answer <https://stackoverflow.com/a/24601292/1633770>`__
provides more explanations on the difference between parameters and
indices, if that helps.

----

**A:** I find it helpful to think of "internal" and "external"
interpretations of the ``return`` type annotation: the internal
interpretation is used to typecheck the expression returned from each
branch of the ``match`` using the constructor arguments; the external
interpretation is used to determine the overall result type of the
``match`` expression using the actual arguments to the ``match``.

**A:** So in the original example: for the internal interpretation,
``eq_refl`` is of type ``x = x`` so the interpretation is ``b = x -> b
= x`` which ``fun HC0 : b = x => HC0`` satisfies; for the external
interpretation, ``H`` is of type ``x = y`` so the overall result type
of the match expression is ``b = y -> b = x``.

**A:** `This chapter
<https://coq.inria.fr/distrib/current/refman/addendum/extended-pattern-matching.html>`__
of the manual explores the subtleties of the ``match`` construct in
Coq.
|*)
