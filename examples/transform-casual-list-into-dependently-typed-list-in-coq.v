(*|
########################################################
Transform casual list into dependently typed list in Coq
########################################################

:Link: https://stackoverflow.com/questions/55150915/transform-casual-list-into-dependently-typed-list-in-coq
|*)

(*|
Question
********

I have following definition of list in Coq:
|*)

Variable A : Set.
Variable P : A -> Prop.
Hypothesis P_dec : forall x, {P x} + {~(P x)}.

Inductive plist : nat -> Set :=
| pnil : plist O
| pcons : A -> forall n, plist n -> plist n
| pconsp : forall (a : A) n, plist n -> P a -> plist (S n).

(*|
It describes "list of elements of type ``A`` where at least ``n`` of
them fulfill predicate ``P``".

My task is to create function that will convert casual list into
``plist`` (with maximum possible ``n``). My attempt was to first count
all elements that match ``P`` and then set the output type according
to the result:
|*)

Require Import Coq.Lists.List. (* .none *)
Import ListNotations. (* .none *)
Fixpoint pcount (l : list A) : nat :=
  match l with
  | nil => O
  | h :: t => if P_dec h then S(pcount t) else pcount t
  end.

Fail Fixpoint plistIn (l : list A) : (plist (pcount l)) :=
  match l with
  | nil => pnil
  | h :: t => match P_dec h with
              | left proof => pconsp h _ (plistIn t) proof
              | right _ => pcons h _ (plistIn t)
              end
  end. (* .unfold .fails *)

(*|
However, I get an error in the line with ``left proof``.

The problem is that Coq cannot see that ``S (pcount t)`` equals
``pcount (h :: t)`` knowing that ``P h``, which was already proven. I
cannot let Coq know this truth.

How to define this function correctly? Is it even possible to do so?
|*)

(*|
Answer
******

You can use dependent pattern-matching, as the result type ``plist
(pcount (h :: t))`` depends on whether ``P_dec h`` is ``left`` or
``right``.

Below, the keyword ``as`` introduces a new variable ``p``, and
``return`` tells the type of the whole ``match`` expression,
parameterized by ``p``.
|*)

Fixpoint plistIn (l : list A) : (plist (pcount l)) :=
  match l with
  | nil => pnil
  | h :: t => match P_dec h as p return plist (if p then _ else _) with
              | left proof => pconsp h (pcount t) (plistIn t) proof
              | right _ => pcons h _ (plistIn t)
              end
  end.

(*|
The type ``plist (if p then _ else _)`` must be equal to ``plist
(pcount (h :: t))`` when substituting ``p := P_dec h``. Then in each
branch, say ``left proof``, you need to produce ``plist (if left proof
then _ else _)`` (which reduces to the left branch).

It's a bit magical that Coq can infer what goes in the underscores
here, but to be safe you can always spell it out: ``if p then S
(pcount t) else pcount t`` (which is meant to exactly match the
definition of ``pcount``).

----

**Q:** Could you explain why ``return if p then plist (S (pcount t))
else plist (pcount t) with`` doesn't work here, or should I ask
another question?

**A:** That's fine here. This doesn't work because when checking
whether ``if P_dec h then plist (S (pcount t)) else plist (pcount t)``
is equal to ``plist (if P_dec h then S (pcount t) else pcount t)``,
the typechecker only considers beta-equivalence, but these two terms
are not beta-equivalent. You may prove ``(if ... then pcount ... else
pcount ... ) = pcount (if ... then ... else ...)`` as a theorem, but
this ``=`` ("propositional equality") is a much weaker notion of
equality than beta-equivalence (or more precisely, "definitional
equality") which is used by the typechecker.
|*)
