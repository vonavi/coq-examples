(*|
###############################################
How to prove equality from equality of ``Some``
###############################################

:Link: https://stackoverflow.com/q/60304522
|*)

(*|
Question
********

I want to prove equality of two ``nat`` numbers in Coq:
|*)

Goal forall (a b : nat), Some a = Some b -> a = b.
Proof. intros. (* .unfold *)
Abort. (* .none *)

(*|
Answer (Théo Winterhalter)
**************************

When you have an equality such as this, usually, the quickest way to
go is by using the ``inversion`` tactic which will more or less
exploit injectivity of constructors.
|*)

Lemma foo : forall (a b : nat), Some a = Some b -> a = b.
Proof.
  intros a b e. inversion e. reflexivity.
Qed.

(*|
The case of ``Some`` however is special enough that you might want to
write it differently (especially if you ant to be able to read the
proof that's generated). You can write some *get* function for
``option`` using a default value:
|*)

Definition get_opt_default {A : Type} (x : A) (o : option A) :=
  match o with
  | Some a => a
  | None => x
  end.

(*|
So that ``get_opt_default x (Some a) = a``. Now using ``f_equal
(get_opt_default a)`` on equality ``Some a = Some b`` you get

.. code-block:: coq

    get_opt_default a (Some a) = get_opt_default a (Some b)

which simplifies to

.. code-block:: coq

    a = b

.. coq::
|*)

Lemma Some_inj : forall A (a b : A), Some a = Some b -> a = b.
Proof.
  intros A a b e. apply (f_equal (get_opt_default a)) in e.
  cbn in e. exact e.
Qed.

(*|
This is something that can be done in general. Basically you write an
extractor for your value as a function and you apply it to both sides
of the equality. By computation it will yield the expected result.
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

The ``congruence`` tactic is powerful enough to solve this goal by
itself. More generally, there are situations where you would like to
derive ``a = b`` as an additional hypothesis starting from an equality
``H : x = y`` of terms that begin with the same constructor. In this
case, you can call

.. code-block:: coq

    injection H.

to extract the equalities implied by this hypothesis.
|*)


(*|
Answer (ejgallego)
******************

I think it is instructive to write the basic lemma down:
|*)

Definition some_inj A (x y : A) (h_eq : Some x = Some y) : x = y :=
  match h_eq with
  | eq_refl _ => eq_refl
  end.

(*|
Actually, that seems surprising; indeed Coq is elaborating the match
to help the user, and the reality is a bit more ugly, as witnessed by
the term:
|*)

Print some_inj. (* .unfold *)

(*|
So indeed the return type of the match is doing quite a bit of work to
tell Coq that the constructor is injective.
|*)
