(*|
############################
How to make sublists in Coq?
############################

:Link: https://stackoverflow.com/q/36896291
|*)

(*|
Question
********

I'm working in Coq and trying to figure out how to do the next thing:
If I have a list of natural numbers and a given number ``n``, I want
to break my list in what goes before and after each of the ``n``'s. To
make it clearer, if I have the list ``[1; 2; 0; 3; 4; 0; 9]`` and the
number ``n = 0``, then I want to have as output the three lists:
``[1;2]``, ``[3;4]`` and ``[9]``. The main problem I have is that I
don't know how to output several elements on a ``Fixpoint``. I think I
need to nest ``Fixpoint``\ s but I just don't see how. As a very raw
idea with one too many issues I have:
|*)

Require Import PeanoNat List. (* .none *)
Import ListNotations. (* .none *)
Fail Fixpoint SubLists (A : list nat) (m : nat) :=
  match A with
  | [] => []
  | n :: A0 => if n =? m then SubLists L else n :: SubLists L
  end. (* .fails *)

(*|
I would very much appreciate your input on how to do this, and how to
navigate having an output of several elements.
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

You can do this by combining a few fixpoints:
|*)

Reset Initial. (* .none *)
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint prefix n l :=
  match l with
  | [] => []
  | m :: l' => if beq_nat n m then [] else m :: prefix n l'
  end.

Fixpoint suffix n l :=
  match l with
  | [] => l
  | m :: l' => if beq_nat n m then l' else suffix n l'
  end.

Fixpoint split_at n l :=
  match l with
  | [] => []
  | m :: l' => prefix n (m :: l') :: split_at n (suffix n (m :: l'))
  end.

(*|
Notice that Coq's termination checker accepts the recursive call to
``split_at``, even though it is not done syntactically a subterm of
``l``. The reason for that is that it is able to detect that suffix
only outputs subterms of its argument. But in order for this to work,
we *must* return ``l``, and not ``[]`` on its first branch (try
changing it to see what happens!).
|*)

(*|
Answer (ejgallego)
******************

In addition to Arthur's solution, you can use an accumulator, which is
typical of Functional Programming style:
|*)

Reset Initial. (* .none *)
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

Definition add_acc m (s : list (list nat)) :=
  match s with
  | []      => [[m]]
  | s :: ss => (m :: s) :: ss
  end.

Fixpoint split_seq n l acc :=
  match l with
  | []      => map (@rev _) (rev acc)
  | m :: l' => if beq_nat n m
               then split_seq n l' ([] :: acc)
               else split_seq n l' (add_acc m acc)
  end.

Compute (split_seq 0 [1; 2; 0; 3; 4; 0; 9] []).

(*|
Note that the result is reversed so you need to use ``rev``. A bonus
exercise is to improve this.

EDIT: Provided second variant that doesn't add ``[]`` for repeated
separators.
|*)

Definition reset_acc (s : list (list nat)) :=
  match s with
  | [] :: ss => [] :: ss
  | ss       => [] :: ss
  end.

Fixpoint split_seq_nodup n l acc :=
  match l with
  | []      => map (@rev _) (rev acc)
  | m :: l' => if beq_nat n m
               then split_seq_nodup n l' (reset_acc acc)
               else split_seq_nodup n l' (add_acc m acc)
  end.

Compute (split_seq_nodup 0 [1; 2; 0; 3; 4; 0; 9] []).

(*|
----

**A:** (1) For ``reset_acc``'s body I'd write ``match s with | [] :: _
=> s | _ => [] :: s`` (2) For novice Coq programmers, not familiar
with the `@ syntax
<https://coq.inria.fr/refman/Reference-Manual004.html#Implicits-explicitation>`__:
it turns off "implicitness", so ``(@rev _)`` stands for ``(@rev
nat)``. Without ``@``, one could have used eta-expansion: ``map (fun
xs => rev xs) (rev acc)``.
|*)

(*|
Answer (gallais)
****************

An alternative way to tackle this issue is to formally describe the
problem you are trying to solve and then either write a
dependently-typed function proving that this problem can indeed be
solved or using tactics to slowly build up your proof.

This is, if I am not mistaken, a relation describing the relationship
between the outputs ``n`` and ``ns`` you want to pass your function
and the output ``mss`` you want to get back.

The ``(* ------- *)`` lines are simple comments used to suggest that
these constructors should be seen as `inference rules
<https://en.wikipedia.org/wiki/Inference_rule>`__: whatever is under
one such line is the conclusion one can make based on the assumptions
above it.

.. coq:: none
|*)

Reset Initial.

Require Import Arith.
Require Import List.
Local Open Scope list_scope.

(*||*)

Inductive SubListsRel (n : nat) :
  forall (ns : list nat) (mss : list (list nat)), Prop :=
| base      : SubListsRel n nil (nil :: nil)
| consEq    : forall ns m mss,
    n = m -> SubListsRel n ns mss ->
    (* ------------------------------ *)
    SubListsRel n (m :: ns) (nil :: mss)
| consNotEq : forall ns m ms mss,
    (n <> m) -> SubListsRel n ns (ms :: mss) ->
    (* -------------------------------------- *)
    SubListsRel n (m :: ns) ((m :: ms) :: mss).

(*|
We can then express your ``Sublists`` problem as being, given inputs
``n`` and ``ns``, the existence of an output ``mss`` such that
``SubListsRel n ns mss`` holds:
|*)

Definition SubLists (n : nat) (ns : list nat) : Set :=
  { mss | SubListsRel n ns mss }.

(*|
Using tactics we can readily generate such ``Sublists`` for concrete
examples in order to sanity-check our specification. We can for
instance take the example you had in your original post:
|*)

Example example1 : SubLists 0 (1 :: 2 :: 0 :: 3 :: 4 :: 0 :: 9 :: nil).
Proof.
  eexists. repeat econstructor; intro Hf; inversion Hf.
Defined.

(*|
And check that the output is indeed the list you were expecting:
|*)

Check (eq_refl : proj1_sig example1
                 = ((1 :: 2 :: nil) :: (3 :: 4 :: nil) :: (9 :: nil) :: nil)).

(*|
Now comes the main part of this post: the proof that ``forall n ns,
SubLists n ns``. Given that the premise of ``consNotEq`` assumes that
``mss`` is non-empty, we will actually prove a strengthened statement
in order to make our life easier:
|*)

Definition Strenghtened_SubLists (n : nat) (ns : list nat) : Set :=
  { mss | SubListsRel n ns mss /\ mss <> nil }.

(*|
And given that oftentimes we will have goals of the shape
``something_absurd -> False``, I define a simple tactic to handle
these things. It introduces the absurd assumption and inverts it
immediately to make the goal disappear:
|*)

Ltac dismiss := intro Hf; inversion Hf.

(*|
We can now prove the main statement by proving the strengthened
version by induction and deducing it. I guess that here it's better
for you to step through it in Coq rather than me trying to explain
what happens. The key steps are the ``cut`` (proving a stronger
statement), ``induction`` and the case analysis on ``eq_nat_dec``.
|*)

Lemma subLists : forall n ns, SubLists n ns.
Proof.
  intros n ns. cut (Strenghtened_SubLists n ns).
  - intros [mss [Hmss _]]. eexists. eassumption.
  - induction ns.
    + eexists. split; [econstructor | dismiss].
    + destruct IHns as [mss [Hmss mssNotNil]];
        destruct (eq_nat_dec n a).
      * eexists. split; [eapply consEq; eassumption | dismiss].
      * destruct mss; [apply False_rect, mssNotNil; reflexivity |].
        eexists. split; [eapply consNotEq; eassumption | dismiss].
Defined.

(*|
Once we have this function, we can come back to our example and
generate the appropriate ``Sublists`` this time not by calling tactics
but by running the function ``subLists`` we just defined.
|*)

Example example2 : SubLists 0 (1 :: 2 :: 0 :: 3 :: 4 :: 0 :: 9 :: nil) :=
  subLists _ _.

(*|
And we can ``Check`` that the computed list is indeed the same as the
one obtained in ``example1``:
|*)

Check (eq_refl : proj1_sig example1 = proj1_sig example2).

(*|
**Nota Bene**: It is paramount here that our proofs are ended with
``Defined`` rather than ``Qed`` in order for them to be unfolded when
computing with them (which is what we want to do here: they give us
the ``list (list nat)`` we are looking for!).

`A gist
<https://gist.github.com/gallais/e6c7dac6542459037a9b3935f3fd3741>`__
with all the code and the right imports.
|*)

(*|
Answer (Anton Trunov)
*********************

Here is another take, based on the standard library function
``List.fold_left``. It works by maintaining an accumulator, which is a
pair of the overall *reversed* result (a list of lists) and a current
sublist (also reversed while accumulating). Once we reach a delimiter,
we reverse the current sublist and put it into the resulting list of
sublists. After executing ``fold_left``, we reverse the result in the
outermost ``match`` expression.
|*)

Reset Initial. (* .none *)
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

Definition split_skip_dup_delims (m : nat) (xs : list nat) :=
  match fold_left
          (fun (acctup: _ * _) x =>
             let (acc, rev_subl) := acctup in
             if beq_nat x m
             then match rev_subl with (* a delimiter found *)
                  | [] => (acc, []) (* do not insert empty sublist *)
                  | _ => (rev rev_subl :: acc, []) end
             else (acc, x :: rev_subl)) (* keep adding to the current sublist *)
          xs
          ([],[]) with
  | (acc, []) => rev acc        (* list ends with a delimiter *)
  | (acc, rev_subl) => rev (rev rev_subl :: acc) (* no delimiter at the end *)
  end.

Eval compute in split_skip_dup_delims 0 [1; 2; 0; 0; 0; 3; 4; 0; 9]. (* .unfold *)
