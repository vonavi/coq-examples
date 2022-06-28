(*|
################################################
How to use the ``Lemma`` inside a module in Coq?
################################################

:Link: https://stackoverflow.com/q/15154401
|*)

(*|
Question
********

I defined a module type in one file called ``A.v``
|*)

Module Type WeakPair.
(* ... *)
End WeakPair.

Module WeakPairProps (Import WP : WeakPair).

  Lemma Weak_A : Prop. Admitted.

End WeakPairProps.

(*|
Then I want to define another file ``B.v`` that can use the ``Lemma``
in ``WeakPairProps`` for example: ``Weak_A``. Because
``WeakPairProps`` is not a module type so I do not know how to write a
module that can reuse the lemma in ``WeakPairProps``.
|*)

(*|
Answer
******

First you need to define a module that *implements* the module type
``WeakPair``:
|*)

Module WeakPairImpl <: WeakPair.
(* stuff goes here *)
End WeakPairImpl.

(*|
Now you can *instantiate* the functor ``WeakPairProps``:
|*)

Module WeakPairPropsInst := WeakPairProps(WeakPairImpl).

(*| You are now able to refer to the lemma: |*)

Check WeakPairPropsInst.Weak_A. (* .unfold *)

(*|
You can *import* ``WeakPairPropsInst`` if you desire not to use
qualified names.
|*)
