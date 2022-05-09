(*|
############################################
Using typeclass instances within typeclasses
############################################

:Link: https://stackoverflow.com/q/44638611
|*)

(*|
Question
********

I am trying to define two instances of a type class, one of which will
use the other's instance. However, unless I bind the function's name
outside of the second definition Coq is unable to determine it should
use the type class instance from ``bexp`` (take a look at the comment
for dirty hack). Is there a way to avoid this sort of hack in Coq?
|*)

Class Compilable (A : Type) := { compile : A -> bool }.

Definition bexp := False. (* .none *)
Inductive cexp : Type :=
| CAnd :  cexp -> cexp -> cexp
| COr  :  cexp -> cexp -> cexp
| CProp : bexp -> cexp.

Instance : Compilable bexp :=
  { compile :=
    fix compile b :=
      match b with
        (* elided *)
      end
  }.

Definition compile2 := compile.

Require Import Coq.Bool.Bool. (* .none *)
Instance: Compilable cexp :=
  { compile :=
    fix compile c :=
      match c with
      | CAnd x y => compile x && compile y
      | COr x y => compile x || compile y
      | CProp e => compile2 e (* <-- dirty hack *)
      end
  }.

(*|
Answer
******

This can be fixed if we replace ``compile`` with some other name
(``rec``) like so:
|*)

Instance : Compilable cexp :=
  { compile :=
    fix rec c :=
      match c with
      | CAnd x y => rec x && rec y
      | COr x y => rec x || rec y
      | CProp e => compile e
      end
  }.

(*|
In this comment the OP pointed out that Haskell easily deals with this
situation. To understand the reason why Coq does not do it let us take
a look at the type of ``compile``:
|*)

About compile. (* .unfold *)

(*|
We can see that Coq is more explicit about how typeclasses work. When
you call ``compile e`` Coq sort of inserts placeholders standing for
the implicit arguments like so ``@compile _ _ e`` (see `these slides
<https://www.cis.upenn.edu/~bcpierce/courses/670Fall12/slides.pdf>`__,
pages 21-25 for more detail). But with ``fix compile c`` you shadowed
the previous binding, hence the type error.
|*)
