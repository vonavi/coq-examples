(*|
####################################################################
How to turn an single unification variable into a goal, during proof
####################################################################

:Link: https://stackoverflow.com/questions/53549618/how-to-turn-an-single-unification-variable-into-a-goal-during-proof
|*)

(*|
Question
********

I want to construct an existential variable interactively. I can't use
`Grab Existential Variables
<https://coq.inria.fr/refman/proof-engine/proof-handling.html#coq:cmd.grab-existential-variables>`__
because I need to fill the existential before I complete the goal.

**Minimal example** Here is a minimal example (since it's simple, it
has other solutions, but it illustrates my question)
|*)

Context (A: Type).
Parameter P Q: A -> Prop.
Definition filter: forall {a}, P a -> A := fun a Pa => a.
Lemma my_lemma:
  forall a b, Q b -> (Q b -> P a) ->
              exists a (H: P a), P (filter H).
Proof.
  intros ?? H H0. do 2 eexists.

(*|
At this point, there are two solutions that don't answer my questions:
(1) I could run (``eauto``) and then do ``Grab Existential
Variables``, but suppose that eauto doesn't succeed until I
instantiate the unification variable; (2) I could just pass the proof
term explicitly with ``instantiate (1 := H0 H)`` (or even
``instantiate (1:= ltac:(eauto))``), but assume that the proof of the
xistential was tedious and we wished to do it interactively.

What else can we do? We can try to use ``cut`` or ``assert``, like so:
|*)

  match goal with
  | [|- P (filter ?x)] =>
    match type of x with
    | ?T => assert (HH : T) by eauto
    end
  end.

(*|
But ``HH`` is not in the context of the unification variable, so it
can't be instantiated.
|*)

  Fail instantiate (1 := HH). (* .unfold .in .messages *)
Abort. (* .none *)

(*|
As far as I can tell, the only way to solve this is to use ``Show
Existentials``, see the type of the variable copy it by hand, roll
back the proof to before the unification was introduced and construct
the variable there. In the example it looks like this:
|*)

Lemma my_lemma:
  forall a b, Q b -> (Q b -> P a) ->
              exists a (H: P a), P (filter H).
Proof.
  intros ?? H H0. do 2 eexists.
  Show Existentials.
  Restart.
  (* This command restores the proof editing process to the original goal. *)
  intros ?? H H0.
  assert (HH: P a) by eauto.
  eexists. exists HH. auto.
Qed.

(*|
Obviously, I would like to avoid this workflow. So, anyway to turn the
existential variables into subgoals?
|*)

(*|
Answer
******

Your best bet is probably to avoid creating the existential variable
as an evar in the first place. You don't have to construct the
variable by hand to do this; if you can identify where it's created,
you can wrap the offending tactic with ``unshelve t``, which turns all
evars created by ``t`` into goals. Where this might be difficult is if
the relevant tactic is deep inside some automation and difficult to
identify or change.
|*)
