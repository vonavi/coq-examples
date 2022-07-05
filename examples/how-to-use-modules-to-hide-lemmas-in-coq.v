(*|
#########################################
How to use modules to hide lemmas in Coq?
#########################################

:Link: https://stackoverflow.com/q/11451536
|*)

(*|
Question
********

I have a theorem ``T``, its proof, and the zillion lemmas used in
proving it.

I would like to hide the lemmas, and make available only the theorem
-- mainly because I don't want to have to think of good, global names
for the Lemmas.

Can I place the theorem, its proof, and the lemmas in a module,
restricted with a module type, and make only the theorem available?

Something like:

.. code-block:: coq

    Module Type T_MY_T.
    End T_MY_T.

    Module T_My_theorem : T_MY_T.
      Lemma L1 : ...
      Proof. Admitted.
      Lemma L2 : ...
      Proof. Admitted.
      Theorem My_Great_Theorem : ...
      Proof. apply L1; apply L2. Qed.
    End T_My_theorem.

If so, can someone please post or point me to a simple example?
|*)

(*|
Answer
******

The ``Module Type A`` should contain Axioms for the theorems you wish
to export. The ``Module B : A`` contains these axioms as theorems that
need to be proven. It can also contain whatever lemmas and other
machinery needed to prove the theorems. To access a theorem from
outside the module, you can ``apply B.Theorem1``, etc.
|*)
