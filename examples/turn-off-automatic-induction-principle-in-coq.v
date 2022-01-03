(*|
#############################################
Turn off automatic induction principle in Coq
#############################################

:Link: https://stackoverflow.com/q/51699205
|*)

(*|
Question
********

I have defined a nested inductive data type and have defined a custom
inductive principle for it. However, automated tactics from a library
I'm using (specifically, DBLib for de Bruijn indices) expects
induction is on the usual inductive principle. Since I never intend to
use the originally-generated inductive principle, is there any way to
either replace the automatically-generated principle? Or, if not, is
there a way to temporarily turn off this automatic generation?
|*)

(*|
Answer
******

You can do it using `Elimination Schemes
<https://coq.inria.fr/refman/user-extensions/proof-schemes.html#coq:opt.elimination-schemes>`__
option. For instance,
|*)

Unset Elimination Schemes.
Inductive nat_tree : Set :=
| NNode' : nat -> list nat_tree -> nat_tree.
Set Elimination Schemes.

(*|
In addition, if you had a simpler (non-recursive) inductive type, you
could have used the `Variant
<https://coq.inria.fr/refman/language/gallina-specification-language.html#coq:cmd.variant>`__
keyword to make Coq not generate the induction principles:
|*)

Variant foo : Type := Foo.
