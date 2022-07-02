(*|
##########################################################
How to name the assumption when remembering an expression?
##########################################################

:Link: https://stackoverflow.com/q/11504064
|*)

(*|
Question
********

The documentation for Coq carries the general admonition *not* to rely
on the builtin naming mechanism, but select one's own names, lest the
changes in the naming mechanism render past proofs invalid.

When considering expressions of the form ``remember Expr as v``, we
set the variable ``v`` to the expression ``Expr``. But the name of the
assumption is selected automatically, and is something like ``Heqv``,
so we have:

.. code-block:: coq

    Heqv: v = Expr

How can I select my own name instead of ``Heqv``? I can always rename
it to whatever I like using the ``rename`` command, but that doesn't
keep my proofs independent of the hypothetical future changes in the
builtin naming mechanism in Coq.
|*)

(*|
Answer
******

If you may get rid of the separate equality, try ``set (name :=
val)``. Use ``unfold`` instead of ``rewrite`` to get the value back in
place.

If you need the equality for more than the ``rewrite <-``, I know of
no built in tactic that does this. You can do it manually, though, or
build a tactic / notation. I just threw this together. (Note: I'm not
an expert, this might be done more easily.)
|*)

Tactic Notation "remember_as_eq" constr(expr) ident(vname) ident(eqname) :=
  let v     := fresh in
  let HHelp := fresh in
  set (v := expr);
  assert (HHelp : sigT (fun x => x = v)) by (apply (existT _ v); reflexivity);
  inversion HHelp as [vname eqname];
  unfold v in *; clear v HHelp;
  rewrite <- eqname in *.

(*|
Use as ``remember_as_eq (2 + 2) four Heqfour`` to get the same result
as with ``remember (2 + 2) as four``.

----

**A:** Note that you can also define it as ``Tactic Notation
"remember" constr(expr) "as" ident(vname) "withEq" ident(eqname)`` if
you prefer using it as ``remember (2 + 2) as four withEq Heqfour``,
but this will bork the parser and shadow the builtin ``remember _ as
_.``. If you use ``Tactic Notation "remember" constr(expr) "with"
ident(eqname) "as" ident(vname)`` (or ``withEq`` instead of ``with``
or ...), the ordering is weird but the old ``remember`` will still be
accessible.
|*)
