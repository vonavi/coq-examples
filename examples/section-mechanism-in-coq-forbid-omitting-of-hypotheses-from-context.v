(*|
####################################################################
Section mechanism in Coq. Forbid omitting of hypotheses from context
####################################################################

:Link: https://stackoverflow.com/q/54804957
|*)

(*|
Question
********

I need more primitive mechanism of generalization in sections. For example,
|*)

Section sec.
  Context (n : nat).
  Definition Q := bool.
End sec.
Check Q. (* .unfold *)

(*|
I will obtain ``Q : Set``, but I need ``Q : nat -> Set``.

I've tried ``Context``, ``Hypotheses``, ``Variables``. It doesn't
work. How to obtain such behavior?
|*)

(*|
Answer
******

This is not a thing you can do with ``Definition ... :=``. However,
you can use ``Proof using``:
|*)

Reset Initial. (* .none *)
Section sec.
  Context (n : nat).
  Definition Q : Set.
  Proof using n. exact bool. Defined.
End sec.
Check Q. (* .unfold *)
