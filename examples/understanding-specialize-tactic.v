(*|
Understanding specialize tactic
===============================

:Link: https://stackoverflow.com/questions/56828692/understanding-specialize-tactic
|*)

(*|
Question
--------

Trying to comprehend the `answer
<https://stackoverflow.com/a/56773900/789186>`_ of @keep_learning I
walked through this code step by step:
|*)

Require Import List. (* .none *)
Import ListNotations. (* .none *)
Inductive nostutter {X : Type} : list X -> Prop :=
| ns_nil : nostutter []
| ns_one : forall (x : X), nostutter [x]
| ns_cons: forall (x : X) (h : X) (t : list X),
    nostutter (h :: t) -> x <> h -> nostutter (x :: h :: t).

Example test_nostutter_4 : not (nostutter [3;1;1;4]).
Proof.
  intro. inversion_clear H. inversion_clear H0.
  unfold not in H2.
  (* We are here *)
  specialize (H2 eq_refl).
  apply H2.
Qed.

(*|
Here is what we have before executing ``specialize``

.. coq:: none
|*)

Reset test_nostutter_4.
Example test_nostutter_4 : not (nostutter [3;1;1;4]).
Proof.
  intro. inversion_clear H. inversion_clear H0.

(*||*)

  unfold not in H2. (* .unfold .hyps .goals *)

(*|
Here is ``eq`` Prop whose constructor ``eq_refl`` is used in
``specialize``:
|*)

  Print eq. (* .unfold .messages *)

(*| I can't explain, how this command works: |*)

  specialize (H2 eq_refl).

(*|
I read about ``specialize`` in reference manual, but the explanation
there is too broad. As far as I understand it sees that ``1 = 1``
expression in ``H2`` satisfies ``eq_refl`` constructor and therefore
``eq`` proposition is ``True``. Then it simplifies the expression:

.. code-block:: coq

    True -> False => False

And we get
|*)

  Undo. (* .none *) specialize (H2 eq_refl). (* .unfold .hyps .goals *)
Abort. (* .none *)

(*|
Can somebody provide me a minimal example with explanation of what is
``specialize`` doing, so I could freely use it?

Update
~~~~~~

Trying to imitate how ``specialize`` works using apply I did the
following:
|*)

Example specialize {A B: Type} (H: A -> B) (a: A): B.
Proof.
  apply H in a. (* .unfold *)
Abort. (* .none *)

(*|
Almost the same as ``specialize``, only different hypothesis name.

In ``test_nostutter_4`` theorem I tried this and it worked:

.. coq:: none
|*)

Example test_nostutter_4 : not (nostutter [3;1;1;4]).
Proof.
  intro. inversion_clear H. inversion_clear H0.
  unfold not in H2.

(*||*)

  remember (@eq_refl nat 1) as Heq.
  apply H2 in Heq as H3. (* .unfold *)
Abort. (* .none *)

(*|
This one was more complex, we had to introduce a new hypothesis
``Heq``. But we got what we need - ``H3`` at the end.

Does specialize internally use something like remember? Or is it
possible to solve it with apply but without remember?
|*)

(*|
Answer
------

``specialize``, in its simplest form, simply replaces a given
hypothesis with that hypothesis applied to some other term.

In this proof,
|*)

Example specialize {A B: Type} (H: A -> B) (a: A): B.
Proof.
  specialize (H a). exact H.
Qed.

(*|
we initially have the hypothesis ``H: A -> B``. When we call
``specialize (H a)``, we apply ``H`` to ``a`` (apply as in function
application). This gives us something of type ``B``. ``specialize``
then gets rid of the old ``H`` for us and replaces it with the result
of the application. It gives the new hypothesis the same name: ``H``.

In your case, we have ``H2: 1 = 1 -> False``, which is a function from
the type ``1 = 1`` to the type ``False``. That means that ``H2``
applied to ``eq_refl`` is of type ``False``, i.e. ``H2 eq_refl:
False``. When we use the tactic ``specialize (H2 eq_refl).``, the old
``H2`` is cleared and replaced by a new term (``H2 eq_refl``) whose
type is ``False``. It keeps the old name ``H2``, though.

``specialize`` is useful when you're sure that you're only going to
use a hypothesis once, since it automatically gets rid of the old
hypothesis. One disadvantage is that the old name may not fit the
meaning of the new hypothesis. However, in your case and in my
example, ``H`` is a generic enough name that it works either way.

----

To your update...

``specialize`` is a core tactic defined directly in the ltac plugin.
It doesn't use any other tactic internally, since it is its internals.

If you want to keep a hypothesis, you can use the ``as`` modifier,
which works for both ``specialize`` and ``apply``. In the proof
|*)

Reset specialize. (* .none *)
Example specialize {A B: Type} (H: A -> B) (a: A): B.
Proof.

(*|
if you do ``specialize (H a) as H0.``, instead of clearing ``H``,
it'll introduce a new hypothesis ``H0: B``. ``apply H in a as H0.``
has the same effect.
|*)
