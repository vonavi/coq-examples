(*|
########################################
How can I use type arguments in an ltac?
########################################

:Link: https://stackoverflow.com/questions/55463216/how-can-i-use-type-arguments-in-an-ltac
|*)

(*|
Question
********

I'm trying to write the following function:

.. code-block:: coq

    Ltac restore_dims :=
      repeat match goal with
             | [ |- context[@Mmult ?m ?n ?o ?A ?B]] =>
               let Matrix m' n' := type of A in
               let Matrix n'' o' := type of B in
               replace m with m' by easy
             end.

That is, I want to use information about the types of ``A`` and ``B``
(which are both matrices with 2 dimension arguments) in my Ltac. Is
that possible, and if so, how?

(Ideally, this would replace the ``m`` in question with ``m'`` and
likewise for ``n`` and ``o`` for all matrix products in my goal.)
|*)

(*|
Answer
******

You can do syntactical matching on type of ``A`` to extract the
arguments.

.. code-block:: coq

    Ltac restore_dims :=
      repeat match goal with
             | [ |- context[@Mmult ?m ?n ?o ?A ?B]] =>
               match type of A with
               | Matrix ?m' ?n' => replace m with m' by easy
               end;
               match type of B with
               | Matrix ?n'' ?o' => replace n with n'' by easy
               (* or whatever you wanted to do with n'' and o' *)
               end
             end.

If you think ``m`` and ``m'`` will be convertible, not merely equal,
and you care about having nice proof terms, consider using the tactic
`change
<https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.change>`__
instead of ``replace`` e.g. ``change n'' with n``. This won't add
anything to the proof term, so it might be easier to work with.
|*)
