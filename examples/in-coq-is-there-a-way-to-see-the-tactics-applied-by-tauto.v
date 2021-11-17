(*|
In Coq, is there a way to see the tactics applied by tauto?
===========================================================

:Link: https://stackoverflow.com/questions/66812480/in-coq-is-there-a-way-to-see-the-tactics-applied-by-tauto
|*)

(*|
Question
--------

Is there a way to see the tactics applied by tauto? I.e., run tauto
and get a list of tactics to apply (not including tauto)?
|*)

(*|
Answer
------

tauto is a tactic directly written in OCaml, so it does not apply
other tactics - it constructs a proof term. But you can have a look at
the proof term it constructs.

E.g.
|*)

Goal forall P Q : Prop, P /\ Q -> P.
  tauto.
  Show Proof. (* .unfold *)

(*| The `fun (P Q : Prop) (H : P /\ Q)` corresponds to `intros P Q H`.
Then it uses `and_ind` with a function as argument. This corresponds
to `exact (and_ind (fun P' Q' => P') H)`. As you can see the trick is
in the construction of the function argument of `and_ind`.

It is instructive to look at these proof terms, but if you would do
the proof manually, you would usually do it in a different way than
tauto does.

And if you look at proof terms of tauto, isolate the goal you proof
with tauto - otherwise the proof term will be hard to digest.
|*)
