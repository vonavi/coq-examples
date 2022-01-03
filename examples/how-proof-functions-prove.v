(*|
##########################
How proof functions prove?
##########################

:Link: https://stackoverflow.com/q/61959394
|*)

(*|
Question
********

It'd help my understanding the 'programs/proofs' parallelism if
somebody was kind enough to explain me how the proof function is used
in the following simple case:
|*)

Theorem ex1 : forall n : nat, 7*5 < n -> 6*6 <= n.
Proof.
  intros. assumption.
Qed.

(*| The proof function: |*)

Print ex1. (* .unfold .messages *)

(*|
Is the proof function executed in the proof process? How its return
value is used? Is it correct to say that the return value of ``ex1``
is an instance of the type ``forall n : nat, 7 * 5 < n -> 6 * 6 <=
n``?
|*)

(*|
Answer
******

    Is it correct to say that the return value of ex1 is an instance
    of the type ``forall n : nat, 7 * 5 < n -> 6 * 6 <= n``?

Not quite. It would be more correct to say that the return type of
``ex1`` is ``6 * 6 <= n``, where ``n`` is the first argument passed to
``ex1``, or that ``ex1`` has type ``forall n, 7 * 5 < n -> 6 * 6 <=
n``.

    Is the proof function executed in the proof process?

Not necessarily. Execution here means "simplification" or
"normalization". The term built by the proof is usually not
simplified. For example:
|*)

Theorem foo : True.
Proof.
  assert (H : True -> True).
  { intros H'. exact H'. }
  apply H. exact I. (* I is a proof of True *)
Qed.

Print foo. (* .unfold *)

(*|
Simplifying this proof means replacing ``H`` by ``fun H' : True =>
H'`` and reducing the application, which yields ``I``. You can see
this by asking Coq to compute this term:
|*)

Compute let H : True -> True := fun H' : True => H' in H I. (* .unfold *)

(*|
*However*:

    How its return value is used?

Every proof that you enter in Coq goes a type-checking step to ensure
it is correct. One of the things the type checker does is to simplify
terms when comparing their types. In Coq, two terms that compute to
the same normal form are considered equal. The term given in the
result, ``H``, was given type ``7 * 5 < n``. But ``a < b`` is defined
as ``S a <= b``; thus we can also view ``H`` as having type ``S (7 *
5) <= n``. Coq now needs to ensure that ``H`` has type ``6 * 6 <= n``,
which it does, because the two lower bounds compute to 36. Thus, there
is computation happening when you enter a proof in Coq, but the
computation is performed by the type-checker, not the proof term (even
though the proof term does have computational behavior).
|*)
