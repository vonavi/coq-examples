(*|
###################################
How to give a counterxample in Coq?
###################################

:Link: https://stackoverflow.com/q/13862940
|*)

(*|
Question
********

Is it possible to give a counterexample for a statement which doesn't
hold in general? Like, for example that the all quantor does not
distribute over the connective ``or``. How would you state that to
begin with?
|*)

Parameter X : Set.
Parameter P : X -> Prop.
Parameter Q : X -> Prop.

(* This holds in general *)
Theorem forall_distributes_over_and :
  (forall x : X, P x /\ Q x) -> (forall x : X, P x) /\ (forall x : X, Q x).
Proof.
  intro H. split. apply H. apply H.
Qed.

(* This doesn't hold in general *)
Theorem forall_doesnt_distributes_over_or :
  (forall x : X, P x \/ Q x) -> (forall x : X, P x) \/ (forall x : X, Q x).
Abort.

(*|
Answer (Ptival)
***************

Here is a quick and dirty way to prove something similar to what you
want:
|*)

Theorem forall_doesnt_distributes_over_or :
  ~ (forall X P Q, (forall x : X, P x \/ Q x) ->
                   (forall x : X, P x) \/ (forall x : X, Q x)).
Proof.
  intros H.
  assert (X : forall x : bool, x = true \/ x = false).
  - destruct x; intuition.
  - specialize (H _ (fun b => b = true) (fun b => b = false) X).
    destruct H as [H | H].
    now specialize (H false).
    now specialize (H true).
Qed.

(*|
I have to quantify ``X``, ``P`` and ``Q`` inside the negation in order
to be able to provide the one I want. You couldn't quite do that with
your ``Parameter``\ s as they somehow fixed an abstract ``X``, ``P``
and ``Q``, thus making your theorem potentially true.
|*)

(*|
Answer (Yves)
*************

In general, if you want to produce a counterexample, you can state the
negation of the formula and then prove that this negation is
satisfied.
|*)
