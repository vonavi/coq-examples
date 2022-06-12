(*|
#########################################
How to disable my custom notation in Coq?
#########################################

:Link: https://stackoverflow.com/q/30294602
|*)

(*|
Question
********

I've defined a notation to simulate imperative style programming by
|*)

Notation "a >> b" := (b a) (at level 50).

(*|
However after that, all function-application expression are
represented as ``>>`` style. For example, in proof mode of Coq
Toplevel, I can see

.. code-block:: coq

    bs' : nat >> list

while actually it should be

.. code-block:: coq

    bs' : list nat

**Why does Coq aggressively rewrite all function application styled
expression into my customized** ``>>`` **representation?** How can I
restore everything back to normal, I mean I want to see ``a >> b`` be
interpreted as ``b a`` and ``list nat`` will not be represented as
``nat >> list``?
|*)

(*|
Answer (Gilles 'SO- stop being evil')
*************************************

By default, Coq assumes that if you define a notation, you want to it
for pretty-printing. If you want the notation to never appear in
pretty-printing, declare it as ``only parsing``.
|*)

Notation "a >> b" := (b a) (at level 50, only parsing).

(*|
If you want ``a >> b`` to be displayed sometimes, you can restrict it
to a scope and associate a type to this scope; then the notation will
only be applied when the result type is that type.

There's no way to tell Coq "use the notation only where I used it in
my source code", because a term written with a notation is exactly the
same as the term written in any other way: the notation used
originally is not part of the term.
|*)

(*|
Answer (gallais)
****************

You could use a definition instead. This way only things you tag as
``followedBy`` would be reified this way. Otherwise there's no way for
the machine to know when to use a space vs. ``>>``...
|*)

Reset Initial. (* .none *)
Definition followedBy {A B : Type} (a : A) (b : A -> B) := b a.

Notation "a >> b" := (followedBy a b) (at level 50).
