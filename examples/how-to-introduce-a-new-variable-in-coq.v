(*|
#######################################
How to introduce a new variable in Coq?
#######################################

:Link: https://stackoverflow.com/q/33005260
|*)

(*|
Question
********

I was wondering if there is a way to introduce an entirely new
variable during the proof of a theorem in Coq?

For a complete example, consider the following property `from here
<http://www.cis.upenn.edu/~bcpierce/sf/current/Prop.html>`__ about the
evenness of the length of a list.
|*)

Require Import List. (* .none *)
Import ListNotations. (* .none *)
Inductive ev_list {X : Type}: list X -> Prop :=
| el_nil : ev_list []
| el_cc  : forall x y l, ev_list l -> ev_list (x :: y :: l).

(*|
Now I want to prove that for any list ``l`` if its ``length`` is even,
then ``ev_list l`` holds:

.. coq:: none
|*)

Inductive ev : nat -> Prop :=
| ev_O  : ev O
| ev_SS : forall n, ev n -> ev (S (S n)).

(*||*)

Lemma ev_length__ev_list' : forall X (l : list X), ev (length l) -> ev_list l.
Proof.
  intros X l H.

(*| which gives: |*)

  Show. (* .unfold .messages *)

(*|
Now, I'd like to "define" a new free variable ``n`` and a hypothesis
``n = length l``. In hand-written math, I think we can do this, and
then do induction about ``n``. But is there a way to do the same in
Coq?

Note. the reasons I ask are that:

1. I don't want to introduce this ``n`` artificially into the
   statement of the theorem itself, as is done in the page linked
   earlier, which IMHO is unnatural.
2. I tried to ``induction H.``, but it seems not working. Coq wasn't
   able to do case analysis on ``length l``'s ``ev``-ness, and no
   induction hypothesis (IH) was generated.
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

This is a common issue in Coq proofs. You can use the ``remember``
tactic:
|*)

  remember (length l) as n.

(*|
If you're doing induction on ``H`` as well, you might also have to
generalize over ``l`` beforehand, by doing
|*)

  generalize dependent l.
  induction H.

(*|
Answer (eponier)
****************

If you want to add a new variable only for your induction, you can use directly
|*)

  Restart. (* .none *) intros X l H. (* .none *)
  induction (length l) eqn:H0.
Admitted. (* .none *)

(*|
Answer (Konstantin Weitz)
*************************

According to the Curry-Howard Isomorphism, hypothesis in your context
are just variables. You can define new variables with a function. The
following ``refine`` tactic extends the goal with a fresh variable
``n`` (that is set to ``length l``) and a proof ``e`` that ``n =
length l`` (that is set to ``eq_refl``).
|*)

Reset ev_length__ev_list'. (* .none *)
Lemma ev_length__ev_list' : forall X (l : list X), ev (length l) -> ev_list l.
Proof.
  intros X l H.
  refine ((fun n (e:n = length l) => _) (length l) eq_refl).
  (* proof *)
Admitted.
