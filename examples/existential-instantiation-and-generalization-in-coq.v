(*|
###################################################
Existential instantiation and generalization in coq
###################################################

:Link: https://stackoverflow.com/q/10686164
|*)

(*|
Question
********

Can someone please give me a simple example of existential
instantiation and existential generalization in Coq? When I want to
prove ``exists x, P``, where ``P`` is some ``Prop`` that uses ``x``, I
often want to name ``x`` (as ``x0`` or some such), and manipulate
``P``. Can this be one in Coq?
|*)

(*|
Answer
******

If you're going to prove the existential directly and not through a
lemma, you can use ``eapply ex_intro``. This introduces an existential
variable (written ``?42``). You can then manipulate the term. To
complete the proof, you need to eventually provide a way to construct
a value for that variable. You can do this explicitly with the
``instantiate`` tactic, or implicitly through tactics such as
``eauto``.

Beware that it is often cumbersome to work with existential variables.
Many tactics assume that all terms are instantiated and may hide
existentials in subgoals; you'll only find out when ``Qed`` tells you
"Error: Attempt to save an incomplete proof". You should only use
existential variables when you have a plan to instantiate them soon.

Here's a silly example that illustrates the use of ``eapply``.
|*)

Goal exists x, 1 + x = 3.
Proof.                        (* ⊢ exists x, 1 + x = 3 *)
  eapply ex_intro.            (* ⊢ 1 + ?42 = 3 *)
  simpl.                      (* ⊢ S ?42 = 3 *)
  apply f_equal.              (* ⊢ ?42 = 2 *)
  reflexivity.                (* proof completed *)
Qed.

(*|
----

**A:** With Coq trunk you can turn uninstantiated existentials into
subgoals at the end of the proof - which is something I wished for for
a long time.

**A:** An addition to the previous comment: this can be done with
``Grab Existential Variables.``
|*)
