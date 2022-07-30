(*|
##########################################################
Why is my recursive definition of ``list_min`` ill-formed?
##########################################################

:Link: https://proofassistants.stackexchange.com/q/1465
|*)

(*|
Question
********

I'm new to Coq and I'm on my own (self-learning).

Question:
=========

    Define a function ``list_min`` that takes a list of natural
    numbers and returns the least element of the list.

`Source
<https://cs.pomona.edu/classes/cs54/book/Structures.html#lab71>`__

My solution:
============
|*)

Fail Fixpoint list_min (l : list nat) : option nat :=
  match l with
  | nil => None
  | cons h nil => Some h
  | cons h (cons h' t') => list_min (cons (min h h') t')
  end. (* .fails *)

(*|
Coq's complain:
===============
|*)

Fail Fixpoint list_min (l : list nat) : option nat :=
  match l with
  | nil => None
  | cons h nil => Some h
  | cons h (cons h' t') => list_min (cons (min h h') t')
  end. (* .unfold .messages *)

(*|
Questions
=========

1. Where does ``l0`` come from?
2. Is there a way to inform Coq such that ``(cons x y)`` is shorter
   than ``(cons (cons x y))`` and thus my ``list_nat`` will always
   terminate?
|*)

(*|
Answer (Meven Lennon-Bertrand)
******************************

1. ``l0`` comes from the fact that deep pattern-matching such as yours
   (where you have two constructors) get elaborated to a succession of
   one-level pattern-matching. So your pattern-matching actually
   elaborates to something like

   .. code-block:: coq

       match l with
       | nil => None
       | cons h l0 =>
           match l0 with
           | nil => Some h
           | cons h' t' => list_min (cons (min h h') t')
           end
       end.

2. There are two possibilities here: the first is to rely on tools
   such as `Program
   <https://coq.inria.fr/refman/addendum/program.html>`__ to give you
   the possibility to specify a measure showing termination. In your
   case, this would give something like
|*)

Require Import Program.

Program Fixpoint list_min (l : list nat) {measure (length l)} : option nat :=
  match l with
  | nil => None
  | cons h nil => Some h
  | cons h (cons h' t') => list_min (cons (min h h') t')
  end.

(*|
   In general, ``Program`` generates *obligations*, corresponding to
   each case of your pattern-matching, where you have to show that the
   measure indeed decreases. But in your simple example, it is able to
   solve them automatically, so you do not have to do anything. If you
   want to look at those obligations, you can use ``Obligation Tactic
   := idtac.`` before your definition to remove the automation, and
   ``Next Obligation`` after it to look at these obligations.

3. If you do not want to drag in ``Program`` and all its complexity,
   another solution is to rewrite your program in order to perform
   structural induction. Here is a possible solution:
|*)

Reset Initial. (* .none *)
Fixpoint list_min (l : list nat) : option nat :=
  match l with
  | nil => None
  | cons h l => match list_min l with
                | None => Some h
                | Some m => Some (min h m)
                end
  end.

(*|
Answer (kyo dralliam)
*********************

For the first question, it is important to know that Coq does not
support nested pattern matching primitively at the level of its kernel
(it would be too complicated). On a definition where you match at
depth 2 of a list (in the 2nd and 3rd branches) as in you question,
Coq desugars the nested pattern match into a pair of pattern matches:
|*)

Fail Fixpoint list_min (l : list nat) : option nat :=
  match l with
  | nil => None
  | cons h l0 =>
      match l0 with
      | nil => Some h
      | cons h' t' => list_min (cons (min h h') t')
      end
  end. (* .fails *)

(*|
So the ``l0`` that appear in the error is a trace of that desugaring
operation corresponding to the intermediary list.

Now, for the second question, Coq only allows structurally decreasing
fixpoints, which means that recursive calls have to happen on
syntactical subterms of the main argument of your fixpoint (as
precised by a ``{struct t}`` instruction or inferred by Coq -- in your
case ``l`` is the main argument inferred by Coq). ``cons (min h h')
t'`` is *not* a subterm of ``l`` so Coq cannot accept this recursive
call.

The solutions you can consider are:

- use well founded induction on the length of your list rather than
  structural induction on the list (this is a generic solution, but a
  bit involved and it might not compute exactly the way you could
  expect); or
- modify your function (for instance using an accumulator for
  additional data) so that it is actually structurally decreasing.
|*)
