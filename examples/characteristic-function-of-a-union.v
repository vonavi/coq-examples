(*|
##################################
Characteristic function of a union
##################################

:Link: https://stackoverflow.com/questions/53352033/characteristic-function-of-a-union
|*)

(*|
Question
********

In a constructive setting such as Coq's, I expect the proof of a
disjunction ``A \/ B`` to be either a proof of ``A``, or a proof of
``B``. If I reformulate this on subsets of a type ``X``, it says that
if I have a proof that ``x`` is in ``A union B``, then I either have a
proof that ``x`` is in ``A``, or a proof that ``x`` is in ``B``. So I
want to define the characteristic function of a union by case
analysis,
|*)

Definition characteristicUnion (X : Type) (A B : X -> Prop)
           (x : X) (un : A x \/ B x) : nat.
(*|
It will be equal to 1 when ``x`` is in ``A``, and to 0 when ``x`` is
in ``B``. However Coq does not let me
|*)
  Fail destruct un. (* .unfold .fails .in .messages *)
Abort. (* .none *)

(*|
Is there another way in Coq to model subsets of type ``X``, that would
allow me to construct those characteristic functions on unions? I do
not need to extract programs, so I guess simply disabling the previous
error on case analysis would work for me.

Mind that I do not want to model subsets as ``A : X -> bool``. That
would be unecessarily stronger: I do not need laws of excluded middle
such as "either ``x`` is in ``A`` or ``x`` is not in ``A``".
|*)

(*|
Answer (ejgallego)
******************

As pointed out by @András Kovács, Coq prevents you from "extracting"
computationally relevant information from types in Prop in order to
allow some more advanced features to be used. There has been a lot of
research on this topic, including recently Univalent Foundations /
HoTT, but that would go beyond the scope of this question.

In your case you want indeed to use the type ``{ A } + { B }`` which
will allow you to do what you want.
|*)

(*|
Answer (András Kovács)
**********************

I think the union of subsets should be a subset as well. We can do
this by defining union as pointwise disjunction:
|*)

Definition subset (X : Type) : Type := X -> Prop.
Definition union {X : Type}(A B : subset X) : subset X :=
  fun x => A x \/ B x.
