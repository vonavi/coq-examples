(*|
##########################
Coq: local ltac definition
##########################

:Link: https://stackoverflow.com/q/51961226
|*)

(*|
Question
********

If there is a way to define a "local" Ltac expresion which I can use
to proof a lemma but not visible outside?

.. code-block:: coq

    Lemma Foo ...
    Proof.
      Ltac ll := ...
      destrict t.
      - reflexivity.
      - ll.
      - ll.
    Qed.

    (* ll should not be visible here *)
|*)

(*|
Answer
******

You can use a section:
|*)

Section Foo.
  Ltac solve := exact I.
  Lemma Foo : True.
  Proof.
    solve.
  Qed.
End Foo.
