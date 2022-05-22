(*|
########################################
Inductive definition for family of types
########################################

:Link: https://stackoverflow.com/q/37366941
|*)

(*|
Question
********

I have been struggling on this for a while now. I have an inductive
type:
|*)

Definition char := nat.
Definition string := list char.

Inductive Exp : Set :=
| Lit  : char -> Exp
| And  : Exp -> Exp -> Exp
| Or   : Exp -> Exp -> Exp
| Many : Exp -> Exp.

(*| from which I define a family of types inductively: |*)

Inductive Language : Exp -> Set :=
| LangLit     : forall c : char, Language (Lit c)
| LangAnd     :
  forall r1 r2 : Exp, Language(r1) -> Language(r2) -> Language(And r1 r2)
| LangOrLeft  : forall r1 r2 : Exp, Language(r1) -> Language(Or r1 r2)
| LangOrRight : forall r1 r2 : Exp, Language(r2) -> Language(Or r1 r2)
| LangEmpty   : forall r : Exp, Language (Many r)
| LangMany    :
  forall r : Exp, Language (Many r) -> Language r -> Language (Many r).

(*|
The rational here is that given a regular expression ``r : Exp`` I am
attempting to represent the language associated with ``r`` as a type
``Language r``, and I am doing so with a single inductive definition.

I would like to prove:
|*)

Lemma L1 : forall (c : char) (x : Language (Lit c)),
    x = LangLit c.
Abort. (* .none *)

(*|
(In other words, the type ``Language (Lit c)`` has only one element,
i.e. the language of the regular expression ``'c'`` is made of the
single string ``"c"``. Of course I need to define some semantics
converting elements of ``Language r`` to ``string``)

Now the specifics of this problem are not important and simply serve
to motivate my question: let us use ``nat`` instead of ``Exp`` and let
us define a type ``List n`` which represents the lists of length
``n``:
|*)

Parameter A : Set.
Inductive List : nat -> Set :=
| ListNil  : List 0
| ListCons : forall n : nat, A -> List n -> List (S n).

(*|
Here again I am using a single inductive definition to define a family
of types ``List n``.

I would like to prove:
|*)

Lemma L2 : forall x : List 0, x = ListNil.
Abort. (* .none *)

(*|
(in other words, the type ``List 0`` has only one element).

I have run out of ideas on this one.

Normally when attempting to prove (negative) results with inductive
types (or predicates), I would use the ``elim`` tactic (having made
sure all the relevant hypothesis are inside my goal (``generalize``)
and only variables occur in the type constructors). But ``elim`` is no
good in this case.
|*)

(*|
Answer
******

If you are willing to accept more than just the basic logic of Coq,
you can just use the ``dependent destruction`` tactic, available in
the ``Program`` library (I've taken the liberty of rephrasing your
last example in terms of standard-library vectors):
|*)

Require Coq.Vectors.Vector.

Require Import Program.

Lemma l0 A (v : Vector.t A 0) : v = @Vector.nil A.
Proof.
  now dependent destruction v.
Qed.

(*|
If you inspect the term, you'll see that this tactic relied on the
``JMeq_eq`` axiom to get the proof to go through:
|*)

Print Assumptions l0. (* .unfold *)

(*|
Fortunately, it is possible to prove ``l0`` without having to resort
to features outside of Coq's basic logic, by making a small change to
the statement of the previous lemma.
|*)

Lemma l0_gen A n (v : Vector.t A n) :
  match n return Vector.t A n -> Prop with
  | 0 => fun v => v = @Vector.nil A
  | _ => fun _ => True
  end v.
Proof.
  now destruct v.
Qed.

Lemma l0' A (v : Vector.t A 0) : v = @Vector.nil A.
Proof.
  exact (l0_gen A 0 v).
Qed.

(*|
We can see that this new proof does not require any additional axioms:
|*)

Print Assumptions l0'. (* .unfold *)

(*|
What happened here? The problem, roughly speaking, is that in Coq we
cannot perform case analysis on terms of dependent types whose indices
have a specific shape (such as ``0``, in your case) *directly*.
Instead, we must prove a more general statement where the problematic
indices are replaced by variables. This is exactly what the ``l0_gen``
lemma is doing. Notice how we had to make the match on ``n`` return a
function that abstracts on ``v``. This is another instance of what is
known as `"convoy pattern"
<http://adam.chlipala.net/cpdt/html/Cpdt.MoreDep.html>`__. Had we
written

.. code-block:: coq

    match n with
    | 0 => v = @Vector.nil A
    | _ => True
    end.

Coq would see the ``v`` in the ``0`` branch as having type ``Vector.t
A n``, making that branch ill-typed.

Coming up with such generalizations is one of the big pains of doing
dependently typed programming in Coq. Other systems, such as Agda,
make it possible to write this kind of code with much less effort, but
it was only recently `shown
<https://people.cs.kuleuven.be/~jesper.cockx/Without-K/Pattern-matching-without-K.pdf>`__
that this can be done without relying on the extra axioms that Coq
wanted to avoid including in its basic theory. We can only hope that
this will be simplified in future versions.

----

**A:** I also find this alternative proof ``by apply: eq_dep_eq; move
E: {1 2}0 v => iz v; case: iz / v E.`` useful sometimes. Indeed,
``eq_dep`` and similar tricks can be very useful when working with
dependent types.
|*)
