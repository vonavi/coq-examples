(*|
################################################################################
Retrieving constraints from GADT to ensure exhaustion of pattern matching in Coq
################################################################################

:Link: https://stackoverflow.com/q/56525092
|*)

(*|
Question
********

Let's define two helper types:
|*)

Inductive AB : Set := A | B.
Inductive XY : Set := X | Y.

(*| Then two other types that depend on ``XY`` and ``AB`` |*)

Inductive Wrapped : AB -> XY -> Set :=
| W : forall (ab : AB) (xy : XY), Wrapped ab xy
| WW : forall (ab : AB), Wrapped ab (match ab with A => X | B => Y end).

Inductive Wrapper : XY -> Set :=
  WrapW : forall (xy : XY), Wrapped A xy -> Wrapper xy.

(*|
Note the ``WW`` constructor – it can only be value of types ``Wrapped
A X`` and ``Wrapped B Y``.

Now I would like to pattern match on ``Wrapper Y``:

.. coq:: unfold fails
|*)

Fail Definition test (wr : Wrapper Y) : nat :=
  match wr with
  | WrapW Y w =>
    match w with
    | W A Y => 27
    end
  end.

(*|
Why does it happen? ``Wrapper`` forces contained ``Wrapped`` to be
``A`` version, the type signature forces ``Y`` and ``WW`` constructor
forbids being ``A`` and ``Y`` simultaneously. I don't understand why
this case is being even considered, while I am forced to check it
which seems to be impossible.

How to workaround this situation?
|*)

(*|
Answer (HTNW)
*************

Let's simplify:
|*)

Inductive MyTy : Set -> Type :=
  MkMyTy : forall (A : Set), A -> MyTy A.

Fail Definition extract (m : MyTy nat) : nat :=
  match m with MkMyTy _ x => S x end. (* .unfold .fails *)

(*|
This is because I said

.. code-block:: coq

    Inductive MyTy : Set -> Type

This made the first argument to ``MyTy`` an index of ``MyTy``, as
opposed to a parameter. An inductive type with a parameter may look
like this:
|*)

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

(*|
Parameters are named on the left of the ``:``, and are not
``forall``-d in the definition of each constructor. (They are still
present in the constructors' types outside of the definition: ``cons :
forall (A : Type), A -> list A -> list A``.) If I make the ``Set`` a
parameter of ``MyTy``, then ``extract`` can be defined:
|*)

Reset MyTy. (* .none *)
Inductive MyTy (A : Set) : Type :=
  MkMyTy : A -> MyTy A.

Definition extract (m : MyTy nat) : nat :=
  match m with MkMyTy _ x => S x end.

(*|
The reason for this is that, on the inside, a ``match`` *ignores*
anything you know about the indices of the scrutinee from the outside.
(Or, rather, the underlying ``match`` expression in Gallina ignores
the indices. When you write a ``match`` in the source code, Coq tries
to convert it into the primitive form while incorporating information
from the indices, but it often fails.) The fact that ``m : MyTy nat``
in the first version of ``extract`` simply did not matter. Instead,
the match gave me ``S : Set`` (the name was automatically chosen by
Coq) and ``x : S``, as per the constructor ``MkMyTy``, with no mention
of ``nat``. Meanwhile, because ``MyTy`` has a parameter in the second
version, I actually get ``x : nat``. The ``_`` is really a placeholder
this time; it is mandatory to write it as _, because there's nothing
to match, and you can ``Set Asymmetric Patterns`` to make it
disappear.

The reason we distinguish between parameters and indices is because
parameters have a lot of restrictions—most notably, if ``I`` is an
inductive type with parameters, then the parameters must appear as
variables in the return type of each constructor:

.. coq:: fails
|*)

Fail Inductive F (A : Set) : Set := MkF : list A -> F (list A).
                                                 (* ^--------^
                                                    BAD: must appear as F A *)

(*|
In your problem, we should make parameters where we can. E.g. the
``match wr with Wrap Y w => _ end`` bit is wrong, because the ``XY``
argument to ``Wrapper`` is an index, so the fact that ``wr : Wrapper
Y`` is ignored; you would need to handle the ``Wrap X w`` case too.
Coq hasn't gotten around to telling you that.
|*)

Reset Wrapped. (* .none *)
Inductive Wrapped (ab : AB) : XY -> Set :=
| W : forall (xy : XY), Wrapped ab xy
| WW : Wrapped ab (match ab with A => X | B => Y end).

Inductive Wrapper (xy : XY) : Set := WrapW : Wrapped A xy -> Wrapper xy.

(*| And now your ``test`` compiles (almost): |*)

Definition test (wr : Wrapper Y) : nat :=
  match wr with
  | WrapW _ w => (* mandatory _ *)
    match w with
    | W _ Y => 27 (* mandatory _ *)
    end
  end.

(*|
because having the parameters gives Coq enough information for its
``match``-elaboration to use information from ``Wrapped``'s index. If
you issue ``Print test.``, you can see that there's a bit of
hoop-jumping to pass information about the index ``Y`` through the
primitive ``match``\ s which would otherwise ignore it. `See the
reference manual for more information.
<https://coq.inria.fr/refman/addendum/extended-pattern-matching.html>`__
|*)

(*|
Answer (radrow)
***************

The solution turned out to be simple but tricky:

.. coq:: none
|*)

Reset AB.

Inductive AB : Set := A | B.
Inductive XY : Set := X | Y.

Inductive Wrapped : AB -> XY -> Set :=
| W : forall (ab : AB) (xy : XY), Wrapped ab xy
| WW : forall (ab : AB), Wrapped ab (match ab with A => X | B => Y end).

Inductive Wrapper : XY -> Set :=
  WrapW : forall (xy : XY), Wrapped A xy -> Wrapper xy.

(*||*)

Definition test (wr : Wrapper Y): nat.
  refine (match wr with
          | WrapW Y w =>
            match w in Wrapped ab xy return ab = A -> xy = Y -> nat with
            | W A Y => fun _ _ => 27
            | _ => fun _ _ => _
            end eq_refl eq_refl
          end);
    [ | | destruct a]; congruence.
Defined.

(*|
The issue was that Coq didn't infer some necessary invariants to
realize that ``WW`` case is ridiculous. I had to explicitly give it a
proof for it.

In this solution I changed ``match`` to return a function that takes
two proofs and brings them to the context of our actual result:

- ``ab`` is apparently ``A``
- ``xy`` is apparently ``Y``

I have covered real cases ignoring these assumptions, and I deferred
"bad" cases to be proven false later which turned to be trivial. I was
forced to pass the ``eq_refl``\ s manually, but it worked and does not
look that bad.
|*)
