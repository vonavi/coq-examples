(*|
#####################
What ``<>`` is in Coq
#####################

:Link:
|*)

(*|
Question
********

It's difficult to search for but wondering what ``<>`` means as in
`here
<https://stackoverflow.com/questions/54937970/how-to-define-axiom-of-a-line-as-two-points-in-coq/54938069#54938069>`__:
|*)

Axiom point : Type.
Axiom line : Type.
Axiom lies_in : point -> line -> Prop.
Axiom ax : forall (p1 p2 : point),
    p1 <> p2 -> exists! l : line, lies_in p1 l /\ lies_in p2 l.

(*|
Answer
******

``x <> y`` is a notation for ``~(x = y)`` (which itself is a notation
for ``(x = y) -> False``). It's possible to search for notations with
the ``Locate`` vernacular command, which is used like ``Locate "<>".``
and gives output like
|*)

Locate "<>". (* .unfold .no-in *)
