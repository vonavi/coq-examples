(*|
#######################################################################################################
How to prove non-equality of terms produced by two different constructors of the same inductive in Coq?
#######################################################################################################

:Link: https://stackoverflow.com/q/60616748
|*)

(*|
Question
********

Consider I have an inductive:
|*)

Inductive DirectSum {L R: Type}: Type :=
| Left: L -> @DirectSum L R
| Right: R -> @DirectSum L R.

(*| How do I prove that |*)

Goal forall L R: Type, forall l: L, forall r: R, Left L <> Right R.

(*| ? |*)

(*|
Answer
******

The ``easy`` tactic is powerful enough to solve this:
|*)

Reset Initial. (* .none *)
Inductive DirectSum (L R: Type): Type :=
| Left: L -> DirectSum L R
| Right: R -> DirectSum L R.

Arguments Left {_ _}.
Arguments Right {_ _}.

Goal forall L R: Type, forall l: L, forall r: R, Left l <> Right r.
  easy.
Qed.

(*|
The reason this works, internally, is pattern matching. We can write a
function that returns ``True`` on ``Left`` and ``False`` on ``Right``.
If the terms were equal, we would get ``True = False``, which entails
a contradiction.
|*)
