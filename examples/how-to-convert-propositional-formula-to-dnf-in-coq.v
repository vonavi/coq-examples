(*|
##################################################
How to convert propositional formula to DNF in Coq
##################################################

:Link: https://stackoverflow.com/q/35507853
|*)

(*|
Question
********

I have defined my propositional formulas as follows:
|*)

Parameter propVar : Set. (* .none *)
Inductive propForm : Set :=
| top : propForm
| bot : propForm
| var : propVar -> propForm
| orp : propForm -> propForm -> propForm
| andp : propForm -> propForm -> propForm.

(*|
I am trying to define a function for transforming a propositional
formula into one in DNF. For this, I have defined a function which
distributes terms using the distributive law:
|*)

Notation "p \/p q" := (orp p q) (at level 20). (* .none *)
Notation "p /\p q" := (andp p q) (at level 20). (* .none *)
Fixpoint distribute (f : propForm) : propForm -> propForm :=
  fix distribute1 (g : propForm) : propForm :=
    match f with
    | f1 \/p f2 => match g with
                   | g1 \/p g2 => distribute1 g1 \/p distribute1 g2
                   | _ => distribute f1 g \/p distribute f2 g
                   end
    | _ => match g with
           | g1 \/p g2 => distribute1 g1 \/p distribute1 g2
           | _ => f /\p g
           end
    end.

(*|
This function works fine. However, I still need to define a function
which transforms the propositional formula to DNF. The following
function would do what I want, however it is not accepted by Coq
because the function is not structurally decreasing in f' for the last
case. Any hints and tips would be appreciated.
|*)

Fail Fixpoint toDNF (f' : propForm) : propForm :=
  match f' with
  | top => f'
  | bot => f'
  | var _ => f'
  | f1 \/p f2 => toDNF f1 \/p toDNF f2
  | f1 /\p f2 => toDNF (distribute f1 f2)
  end. (* .fails *)

(*|
Answer
******

Your function is a special case of normalizing an expression from a
semi-ring. I wrote a `post
<http://poleiro.info/posts/2015-04-13-writing-reflective-tactics.html>`__
explaining how to do that in the case of arithmetic expressions, using
the Ssreflect and MathComp libraries, but I'll include a more direct
answer here.

One idea is to use lists of lists to represent formulas in DNF: after
all, they are just a conjunction of a list of disjunctions, which are
just lists of literals. You can then reuse the list library to write
your function:
|*)

Reset Initial. (* .none *)
Module Sol1.

  Require Import Coq.Lists.List.
  Import ListNotations.

  Notation propVar := nat.

  Inductive propAtom :=
  | top | bot | var :> propVar -> propAtom.

  Inductive propForm : Set :=
  | atom :> propAtom -> propForm
  | orp : propForm -> propForm -> propForm
  | andp : propForm -> propForm -> propForm.

  Definition dnfForm := list (list propAtom).

  Fixpoint andd (f1 f2 : dnfForm) : dnfForm :=
    match f1 with
    | [] =>
        (* false && f2 = false *)
        []
    | cf :: f1 =>
        (* (cf || f1) && f2 = cf && f2 || f1 && f2 *)
        map (app cf) f2 ++ andd f1 f2
    end.

  Fixpoint toDNF (f : propForm) : dnfForm :=
    match f with
    | atom a => [[a]]
    | orp f1 f2 => toDNF f1 ++ toDNF f2
    | andp f1 f2 => andd (toDNF f1) (toDNF f2)
    end.

  Compute (toDNF (andp (orp 3 4) (orp 1 2))).

End Sol1.

(*|
There are two things to note here. First, I factored variables and
constants as a separate ``propAtom`` type, and I have called
``distribute`` ``andd``, because you can think of it as computing the
AND of two expressions in DNF.

Here's another solution that is based on your original code. It seems
that your ``distribute`` function preserves the invariant of being in
DNF; that is, if ``f1`` and ``f2`` are in DNF, then so is ``distribute
f1 f2``. Thus, you can just flip the order of the calls:
|*)

Module Sol2.

  Notation propVar := nat.

  Inductive propForm : Set :=
  | top : propForm
  | bot : propForm
  | var :> propVar -> propForm
  | orp : propForm -> propForm -> propForm
  | andp : propForm -> propForm -> propForm.

  Fixpoint distribute (f:propForm) : propForm -> propForm :=
    fix distribute1 (g:propForm) : propForm :=
      match f with
      | orp f1 f2 => match g with
                     | orp g1 g2 => orp (distribute1 g1) (distribute1 g2)
                     | _ => orp (distribute f1 g) (distribute f2 g)
                     end
      | _ => match g with
             | orp g1 g2 => orp (distribute1 g1) (distribute1 g2)
             | _ => andp f g
             end
      end.

  Fixpoint toDNF (f':propForm):propForm :=
    match f' with
    | top => f'
    | bot => f'
    | var _ => f'
    | orp f1 f2 => orp (toDNF f1) (toDNF f2)
    | andp f1 f2 => distribute (toDNF f1) (toDNF f2)
    end.

  Compute (toDNF (andp (orp 3 4) (orp 1 2))).

End Sol2.

(*|
----

**Q:** Thank you, I had actually all ready proven that my distribute
indeed preserves the invariant of being in DNF. However, I had not
realized the repercussion that I could flip the order of the calls.
Because I need equivalence between the propositional formulas,
defining a sepperate type would have been a lot of work, since I would
also require complete and sound conversions.

**A:** I see your point, but it's not actually too bad, since you can
always write a function to convert a DNF formula (as a list of lists)
back to a generic one. If you have a good infrastructure to reason
about lists and algebraic structures (as Ssreflect provides), then the
amount of code that you'll save definitely justifies using this
approach.
|*)
