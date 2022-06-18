(*|
#############################
Redundant clause in ``match``
#############################

:Link: https://stackoverflow.com/q/27028360
|*)

(*|
Question
********

When I run the following script:
|*)

Fail Definition inv (a : Prop) : Prop :=
  match a with
  | False => True
  | True => False
  end. (* .fails .unfold *)

(*| Any idea why this happens? |*)

(*|
Answer
******

There are quite a few wrong things about this.

``False`` is not a data constructor, and since there is no syntactic
difference between data constructors and variable names in Coq, it
understands your ``| False =>`` as a pattern matching anything and
giving it the name ``False``, in the same way as you could have
written:
|*)

Fail Definition inv (a : Prop) : Prop :=
  match a with
  | x => True
  | y => False
  end. (* .fails *)

(*|
This is why it tells you that the second clause is redundant (since
the first pattern matches everything).

Now another thing you should know is that the type ``Prop`` is not
inductively-defined, and therefore values of type ``Prop`` cannot be
matched against anything: in fact it would not make sense, since it is
an open type that you keep expanding everytime you define a new
inductive property.

So there is no way to write a function ``inv`` the way you write it.

----

**A:** You can, however, write
|*)

Definition inv (a : Prop) : Prop := a -> False.

(*| which has a similar meaning. |*)
