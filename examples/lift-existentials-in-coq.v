(*|
########################
Lift existentials in Coq
########################

:Link: https://stackoverflow.com/questions/54944574/lift-existentials-in-coq
|*)

(*|
Question
********

Can this lemma be proven in Coq?
|*)

Lemma liftExists : forall (P : nat -> nat -> Prop),
    (forall n : nat, exists p : nat, P n p)
    -> exists (f : nat -> nat), forall n : nat, P n (f n).
Abort. (* .none *)

(*|
The simple ``destruct`` does not compile, because we cannot eliminate
the object ``exists p:nat, P n p`` in sort ``Prop``, to produce the
function ``f`` in sort ``Set``.

If Coq cannot prove this lemma, then what is the meaning of ``forall
n:nat, exists p:nat, P n p``? In constructive mathematics it would
mean the existence of the function ``f``, but I have the impression
that we will never see this function ``f`` in Coq, not even in sort
``Prop`` as expressed above.
|*)

(*|
Answer
******

It is not provable in Coq because of the restriction on eliminating
``Prop`` into ``Set``. As for the philosophical "meaning", I'm not
sure if anyone has a very good story about this. The inhabitants of
``forall n:nat, exists p:nat, P n p`` are functions returning a pair
of ``p`` and a proof, but in addition they a functions that can be
ignored when compiling programs because you know that nothing will
look at the value that was returned.

So partly this system of ``Prop`` versus ``Set`` is a way to compile
programs more efficiently, but actually this is also used for logical
properties. In Coq the ``Prop`` type is impredicative and the ``Set``
type is not, and even so it's consistent to assume the law of exluded
middle for ``Prop``\ s as an axiom, and to prove that this is
consistent you can appeal to a "`proof-irrelevant model
<http://www.lix.polytechnique.fr/~werner/publis/cc.pdf>`__", where you
interpret types in ``Prop``\ s as sets by ignoring all information
except whether they are inhabited or not. From a classical logic
perspective (where all you care about are truth values) that makes
sense, but if you are interested in constructive mathematics it's a
bit weird!
|*)
