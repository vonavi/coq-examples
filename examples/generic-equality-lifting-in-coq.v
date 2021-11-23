(*|
Generic equality lifting in coq
===============================

:Link: https://stackoverflow.com/questions/60616818/generic-equality-lifting-in-coq
|*)

(*|
Question
--------

Is there any tactic or fact or something else to lift equality into a
constructor of inductive and reverse, unlift equality of inductive
constructors to equality of constructor arguments, i.e.:

| `forall T: Type, forall t1 t2: T, Some t1 = Some t2 -> t1 = t2`
| `forall T: Type, forall t1 t2: T, t1 = t2 -> Some t1 = Some t2`
|*)

(*|
Answer
------

The first principle is usually known as the injectivity of
constructors, and there are multiple tactic that can use it. One
option is the ``injection`` tactic:
|*)

Goal forall T: Type, forall t1 t2: T, Some t1 = Some t2 -> t1 = t2.
  intros T t1 t2 H. injection H as H. apply H.
Qed.

(*|
The other principle is valid for any function, not just constructors.
You can use the ``f_equal`` tactic:
|*)

Goal forall T: Type, forall t1 t2: T, t1 = t2 -> Some t1 = Some t2.
  intros T t1 t2 H. f_equal. exact H.
Qed.

(*|
Note that in this situation it is often easier to simply rewrite with
the equality, since it avoids generating multiple goals when you have
a multiple-argument function:
|*)

Goal forall T: Type, forall t1 t2: T, t1 = t2 -> Some t1 = Some t2.
  intros T t1 t2 H. rewrite H. trivial.
Qed.
