(*|
##################################################
Instantiating an existential with a specific proof
##################################################

:Link: https://stackoverflow.com/q/46791645
|*)

(*|
Question
********

I'm currently trying to write a tactic that instantiates an
existential quantifier using a term that can be generated easily (in
this specific example, from ``tauto``). My first attempt:
|*)

Ltac mytac :=
  match goal with
    | |- (exists (_ : ?X), _) =>
      cut X; [ let t := fresh "t" in intro t; exists t; firstorder | tauto ]
  end.

(*| This tactic will work on a simple problem like |*)

Lemma obv1 (X : Set) : exists f : X -> X, f = f.
  mytac.
Qed.

(*| However it won't work on a goal like |*)

Lemma obv2 (X : Set) : exists f : X -> X, forall x, f x = x.
  mytac. (* .unfold *)
Abort. (* .none *)

(*|
Here I would like to use this tactic, trusting that the ``f`` which
``tauto`` finds will be just ``fun x => x``, thus subbing in the
specific proof (which should be the identity function) and not just
the generic ``t`` from my current script. How might I go about writing
such a tactic?
|*)

(*|
Answer (Tej Chajed)
*******************

It's much more common to create an existential variable and let some
tactic (``eauto`` or ``tauto`` for example) instantiate the variable
by unification.

On the other hand, you can also literally use a tactic to provide the
witness using tactics in terms:
|*)

Reset Initial. (* .none *)
Ltac mytac :=
  match goal with
  | [ |- exists (_ : ?T), _ ] => exists (ltac:(tauto) : T)
  end.

Lemma obv1 (X : Set) : exists f : X -> X, f = f.
Proof.
  mytac. auto.
Qed.

(*|
You need the type ascription ``: T`` so that the tactic-in-term
``ltac:(tauto)`` has the right goal (the type the ``exists`` expects).

I'm not sure this is all that useful (usually the type of the witness
isn't very informative and you want to use the rest of the goal to
choose it), but it's cool that you can do this nonetheless.

----

**Q:** Do you happen to know if there are more powerful tactics for finding unifiers? Just playing around a bit it seems that the ``eexists`` + ``eauto/tauto`` approach doesn't work on something with multiple instantiations like
|*)

Lemma two_ids (X : Set) : exists f g : X -> X, forall x, f (g x) = x.
Abort. (* .none *)

(*| or something a touch trickier like |*)

Lemma const : forall (X Y : Set) (y : Y), exists f : X -> Y,
  forall x x', f x = f x'.
Abort. (* .none *)

(*| (the needed unifier being ``fun _ => y``) |*)

(*|
Answer (eponier)
****************

You can use ``eexists`` to introduce an existential variable, and let
``tauto`` instantiates it.

This give the following simple code.
|*)

Lemma obv2 (X : Set) : exists f : X -> X, forall x, f x = x.
  eexists; tauto.
Qed.
