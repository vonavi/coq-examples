(*|
#######################################
A simple case of universe inconsistency
#######################################

:Link: https://stackoverflow.com/q/51029234
|*)

(*|
Question
********

I can define the following inductive type:
|*)

Inductive T : Type -> Type :=
| c1 : forall (A : Type), A -> T A
| c2 : T unit.

(*|
But then the command ``Check (c1 (T nat))`` fails with the message:
|*)

Fail Check (c1 (T nat)). (* .fails .unfold *)

(*|
How can I tweak the above inductive definition so that ``c1 (T nat)``
does not cause a universe inconsistency, and without setting universe
polymorphism on?

The following works, but I would prefer a solution without adding
equality:
|*)

Reset Initial. (* .none *)
Inductive T (A : Type) : Type :=
| c1 : A -> T A
| c2' : A = unit -> T A.

Definition c2 : T unit := c2' unit eq_refl.

Check (c1 (T nat)). (* .unfold *)

(*|
Answer
******

Let me first answer the question of why we get the universe
inconsistency in the first place.

Universe inconsistencies are the errors that Coq reports to avoid
proofs of ``False`` via Russell's paradox, which results from
considering the set of all sets which do not contain themselves.

There's a variant which is more convenient to formalize in type theory
called Hurken's Paradox; see `Coq.Logic.Hurkens
<https://coq.inria.fr/library/Coq.Logic.Hurkens.html>`__ for more
details. There is a specialization of Hurken's paradox which proves
that no type can retract to a smaller type. That is, given

.. code-block:: coq

    U := Type@{u}
    A : U
    down : U -> A
    up : A -> U
    up_down : forall (X:U), up (down X) = X

we can prove ``False``.

----

This is almost exactly the setup of your ``Inductive`` type.
Annotating your type with universes, you start with
|*)

Reset Initial. (* .none *)
Universes i j. (* .none *)
Inductive T : Type@{i} -> Type@{j} :=
| c1 : forall (A : Type@{i}), A -> T A
| c2 : T unit.

(*| Note that we can invert this inductive; we may write |*)

Definition c1' (A : Type@{i}) (v : T A) : A :=
  match v with
  | c1 A x => x
  | c2 => tt
  end.

Lemma c1'_c1 (A : Type@{i}) : forall v, c1' A (c1 A v) = v.
Proof. reflexivity. Qed.

(*|
Suppose, for a moment, that ``c1 (T nat)`` typechecked. Since ``T nat
: Type@{j}``, this would require ``j <= i``. If it gave us that ``j <
i``, then we would be set. We could write ``c1 Type@{j}``. And this is
exactly the setup for the variant of Hurken's that I mentioned above!
We could define

.. code-block:: coq

    u = j
    U := Type@{j}
    A := T Type@{j}
    down : U -> A := c1 Type@{j}
    up : A -> U := c1' Type@{j}
    up_down := c1'_c1 Type@{j}

and hence prove ``False``.

Coq needs to implement a rule for avoiding this paradox. As described
`here
<https://github.com/coq/coq/issues/7929#issuecomment-400376700>`__,
the rule is that for each (non-parameter) argument to a constructor of
an inductive, if the type of the argument has a sort in universe
``u``, then the universe of the inductive is constrained to be ``>=
u``. In this case, this is stricter than Coq needs to be. As mentioned
by SkySkimmer `here
<https://github.com/coq/coq/issues/7929#issuecomment-400384621>`__,
Coq could recognize arguments which appear directly in locations which
are indices of the inductive, and disregard those in the same way that
it disregards parameters.

----

So, to finally answer your question, I believe the following are your
only options:

1. You can ``Set Universe Polymorphism`` so that in ``T (T nat)``,
   your two ``T``\ s take different universe arguments. (Equivalently,
   you can write ``Polymorphic Inductive``.)
2. You can take advantage of how Coq treats parameters of inductive
   types specially, which mandates using equality in your case. (The
   requirement of using equality is a general property of going from
   indexed inductive types to parameterized inductives types---from
   moving arguments from after the ``:`` to before it.)
3. You can pass Coq the flag ``-type-in-type`` to entirely disable
   universe checking.
4. You can `fix bug #7929 <https://github.com/coq/coq/issues/7929>`__,
   which I reported as part of digging into this question, to make Coq
   handle arguments of constructors which appear in index-position in
   the inductive in the same way it handles parameters of inductive
   types.
5. (You can find another edge case of the system, and manage to trick
   Coq into ignoring the universes you want to slip past it, and
   probably find a proof of ``False`` in the process. (Possibly
   involving module subtyping, see, e.g., `this recent bug in modules
   with universes <https://github.com/coq/coq/issues/7695>`__.))
|*)
