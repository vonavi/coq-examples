(*|
How to provide proof that two values are different?
===================================================

https://stackoverflow.com/questions/62779463/how-to-provide-proof-that-two-values-are-different
|*)

(*|
Question
--------

I am looking for an example in Coq for difference between two
statements. True is equal to false and true is not equal to true. I do
not find how to finish the proof, if have this expression `true <>
true`.
|*)

(*|
Answer
------

Let's check a casual example when you have:
|*)

Theorem easily : true <> false. (* .unfold *)
Abort. (* .none *)

(*| you can just desugar the `<>` negation to some `Prop -> False`, |*)

Theorem easily : true <> false.
  intro H. (* .unfold *)
Abort. (* .none *)

(*|
As `H` is a contradiction, you can just use `inversion H` and finish
the proof, dependently typed talking you just have to provide
anti-congruence absurd between the values, in Coq it can be done with
`eq_rect`.
|*)

Theorem easily : true <> false.
  intro H.
  (* check eq_rect with Compute eq_rect *)
  pose (fun h => @eq_rect _ _ (fun x => match x with
                                        | true => True
                                        | false => False
                                        end) h _ H) as c.
  simpl in c. (* .unfold *)
  exact (c I).
Qed.

(*| In your example, you just have to provide proof that `true = true`. |*)

Reset easily. (* .none *)
Theorem easily : true <> true -> False.
  intro H. cbv in H. exact (H eq_refl).
  Restart. (* or just contradiction *)
  contradiction.
Qed.

(*|
Remember with easily you can finish any goal that has `true <> true`
as a premise.
|*)
