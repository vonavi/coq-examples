(*|
#################################################
mutual recursion on an inductive type and ``nat``
#################################################

:Link: https://stackoverflow.com/q/50477918
|*)

(*|
Question
********

Consider this example:
|*)

Inductive T :=
| foo : T
| bar : nat -> T -> T.

Fail Fixpoint evalT (t : T) {struct t} : nat :=
  match t with
  | foo => 1
  | bar n x => evalBar x n
  end
with
evalBar (x : T) (n : nat) {struct n} : nat :=
  match n with
  | O => 0
  | S n' => evalT x + evalBar x n'
  end. (* .fails .unfold *)

(*|
Coq rejects it.

I understand that termination checker got confused by two unrelated
inductive types (``T`` and ``nat``). However, it looks like the
function I am trying to define will indeed terminate. How can I make
Coq accept it?
|*)

(*|
Answer (eponier)
****************

Another solution is to use a nested fixpoint.
|*)

Fixpoint evalT (t : T) {struct t} : nat :=
  match t with
  | foo => 1
  | bar n x => let fix evalBar n {struct n} :=
                   match n with
                   | 0 => 0
                   | S n' => evalT x + evalBar n'
                   end
               in evalBar n
  end.

(*|
The important point is to remove the argument ``x`` from ``evalBar``.
Thus the recursive call to ``evalT`` is done on the ``x`` from ``bar n
x``, not the ``x`` given as an argument to ``evalBar``, and thus the
termination checker can validate the definition of ``evalT``.

This is the same idea that makes the version with ``nat_rec`` proposed
in another answer work.
|*)

(*|
Answer (krokodil)
*****************

One solution I found is to use ``nat_rec`` instead of ``evalBar``:
|*)

Reset evalT. (* .none *)
Fixpoint evalT (t : T) {struct t} : nat :=
  match t with
  | foo => 1
  | bar n x => @nat_rec _ 0 (fun n' t' => evalT x + t') n
  end.

(*|
It works but I wish I could hide ``nat_rec`` under ``evalBar``
definition to hide details. In my real project, such construct is used
several times.
|*)
