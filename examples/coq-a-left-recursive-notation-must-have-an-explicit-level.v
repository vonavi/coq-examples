(*|
##########################################################
Coq: a left-recursive notation must have an explicit level
##########################################################

:Link: https://stackoverflow.com/q/33929265
|*)

(*|
Question
********

I have seen a Coq notation definition for "evaluates to" as follows:

.. coq:: none
|*)

Parameter aexp : Type.
Parameter aevalR : aexp -> nat -> Prop.

(*||*)

Notation "e '||' n" := (aevalR e n) : type_scope.

(*|
I am trying to change the symbol ``'||'`` to something else as ``||``
is often times used for logical ``or``. However, I always get an error
|*)

Fail Notation "e '|.|' n" := (aevalR e n) : type_scope. (* .unfold .messages *)

(*|
For example, this happens when I change ``'||'`` to:

``'\|/'``, ``'\||/'``, ``'|_|'``, ``'|.|'``, ``'|v|'``, or ``'|_'``.

Is there something special about ``||`` here? and how should I fix it
to make these other notations work (if possible)?
|*)

(*|
Answer
******

If I am right, if you overload a notation, Coq uses the properties of
the first definition. The notation ``_ '||' _`` has already a level,
so Coq uses this level for your definition.

But with new symbols, Coq cannot do that, and you have to specify the
level:
|*)

Notation "e '|.|' n" := (aevalR e n) (at level 50) : type_scope.

(*|
For already defined notations, this is even stronger than what I wrote
above. You cannot redefine the level of a notation. Try for example:

.. coq:: none
|*)

Reset Initial.
Parameter aexp : Type.
Parameter aevalR : aexp -> nat -> Prop.

(*||*)

Fail Notation "e '||' n" := (aevalR e n) (at level 20) : type_scope. (* .fails *)
