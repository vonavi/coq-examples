(*|
#############################################
Fixpoint with ``Prop`` inhabitant as argument
#############################################

:Link: https://stackoverflow.com/q/51763716
|*)

(*|
Question
********

Consider the definition of ``find`` in `the standard library
<https://coq.inria.fr/library/Coq.Lists.List.html#find>`__, which as
the type ``find: forall A : Type, (A -> bool) -> list A -> option A``.

Of course, ``find`` has to return an ``option A`` and not an ``A``
because we don't know wether there is a "valid" element in the list.

Now, say I find this definition of ``find`` painful, because we have
to deal with the option, even when we are sure that such an element
exists in the list.

Hence, I'd like to define ``myFind`` which additionnaly takes a proof
that there is such an element in the list. It would be something like:

.. code-block:: coq

    Variable A: Type.
    Fixpoint myFind
             (f: A -> bool)
             (l: list A)
             (H: exists a, In a l /\ f a = true): A :=
             ...

If I am not mistaken, such a signature informally says: "Give me a
function, a list, and a proof that you have a "valid" element in the
list".

My question is: how can I use the hypothesis provided and define my
fixpoint?

What I have in mind is something like:

.. code-block:: coq

    match l with
    | nil => (* Use H to prove this case is not possible *)
    | hd :: tl =>
      if f hd
      then hd
      else
        (* Use H and the fact that f hd = false
           to prove H': exists a, In a tl /\ f a = true *)
        myFind f tl H'
    end.

----

An bonus point would be to know whether I can embbed a property about
the result directly within the type, for instance in our case, a proof
that the return value ``r`` is indeed such that ``f r = true``.
|*)

(*|
Answer (Anton Trunov)
*********************

We can implement this ``myFind`` function by structural recursion over
the input list. In the case of empty list the ``False_rect`` inductive
principle is our friend because it lets us switch from the logical
world to the world of computations. In general we cannot destruct
proofs of propositions if the type of the term under construction
lives in ``Type``, but if we have an inconsistency the system lets us.

We can handle the case of the non-empty input list by using the
*convoy pattern* (there is a number of great answers on Stackoverflow
explaining this pattern) and an auxiliary lemma ``find_not_head``.

It might be useful to add that I use the convoy pattern twice in the
implementation below: the one on the top level is used to let Coq know
the input list is empty in the first ``match``-branch -- observe that
the type of ``H`` is different in both branches.
|*)

From Coq Require Import List.
Import ListNotations.
Set Implicit Arguments.

(* so we can write `f a` instead of `f a = true` *)
Coercion is_true : bool >-> Sortclass.

Section Find.
  Variables (A : Type) (f : A -> bool).

  (* auxiliary lemma *)
  Fact find_not_head h l : f h = false ->
                           (exists a, In a (h :: l) /\ f a) ->
                           exists a, In a l /\ f a.
  Proof. intros E [a [[contra | H] fa_true]]; [congruence | now exists a]. Qed.

  Fixpoint myFind (l : list A) (H : exists a : A, In a l /\ f a) :
    {r : A | f r} :=
    match l with
    | [] => fun H : exists a : A, In a [] /\ f a =>
              False_rect {r : A | f r}
                         match H with
                         | ex_intro _ _ (conj contra _) =>
                           match contra with end
                         end
    | h :: l => fun H : exists a : A, In a (h :: l) /\ f a =>
                  (if f h as b return (f h = b -> {r : A | f r})
                   then fun Efh => exist _ h Efh
                   else fun Efh => myFind l (find_not_head Efh H)) eq_refl
    end H.
End Find.

(*| Here is a simplistic test: |*)

From Coq Require Import Arith.
Section FindTest.
  Notation l := [1; 2; 0; 9].
  Notation f := (fun n => n =? 0).
  Fact H : exists a, In a l /\ f a.
  Proof. exists 0; intuition. Qed.

  Compute myFind f l H.
(*
  = exist (fun r : nat => f r) 0 eq_refl
  : {r : nat | f r}
*)
End FindTest.

(*|
Answer (larsr)
**************

You can also use ``Program`` to help you construct the proof arguments
interactively. You fill in as much as you can in the program body and
leave ``_`` blanks that you get to fill in later with proof tactics.
|*)

Require Import List Program.

Section Find.

  Variable A : Type.
  Variable test : A -> bool.

  Program Fixpoint FIND l (H : exists a, test a = true /\ In a l) :
    {r | test r = true} :=
    match l with
    | [] => match (_ : False) with end
    | a :: l' => if dec (test a) then a else FIND l' _
    end.

  Next Obligation.
    firstorder; congruence.
  Defined.

End Find.

(*|
``Program`` is a little better at not forgetting information when you
do case analysis (it knows the convoy pattern) but it is not perfect,
hence the use of ``dec`` in the ``if`` statement.

(Notice how Coq was able to handle the first obligation, to construct
a term of type ``False``, all by itself!)
|*)
