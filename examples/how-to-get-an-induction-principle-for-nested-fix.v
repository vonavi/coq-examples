(*|
####################################################
How to get an induction principle for nested ``fix``
####################################################

:Link: https://stackoverflow.com/q/19205839
|*)

(*|
Question
********

I am working with a function that searches through a range of values.
|*)

Require Import List.
Require Import FunInd.

(* Implementation of ListTest omitted. *)
Definition ListTest (l : list nat) := false.

Definition SearchCountList n :=
  (fix f i l := match i with
                | 0 => ListTest (rev l)
                | S i1 =>
                    (fix g j l1 := match j with
                                   | 0 => false
                                   | S j1 =>
                                       if f i1 (j :: l1)
                                       then true
                                       else g j1 l1
                                   end) (n + n) (i :: l)
                end) n nil.

(*|
I want to be able to reason about this function.

However, I can't seem to get Coq's built-in induction principle
facilities to work.
|*)

Fail Functional Scheme SearchCountList := Induction for SearchCountList Sort Prop.
(* .fails .unfold *)

(*|
It looks like Coq is set up for handling mutual recursion, not nested
recursion. In this case, I have essentially 2 nested for loops.

However, translating to mutual recursion isn't so easy either:
|*)

Fail Definition SearchCountList_Loop :=
  fix outer n i l {struct i} :=
    match i with
    | 0 => ListTest (rev l)
    | S i1 => inner n i1 (n + n) (i :: l)
    end
      with inner n i j l {struct j} :=
      match j with
      | 0 => false
      | S j1 =>
          if outer n i (j :: l)
          then true
          else inner n i j1 l
      end
        for outer. (* .fails .unfold *)

(*|
So, it looks like I would need to use measure to get it to accept the
definition directly. It is confused that I reset j sometimes. But, in
a nested set up, that makes sense, since i has decreased, and i is the
outer loop.

So, is there a standard way of handling nested recursion, as opposed
to mutual recursion? Are there easier ways to reason about the cases,
not involving making separate induction theorems? Since I haven't
found a way to generate it automatically, I guess I'm stuck with
writing the induction principle directly.
|*)

(*|
Answer
******

There's a trick for avoiding mutual recursion in this case: you can
compute ``f i1`` inside ``f`` and pass the result to ``g``.

.. coq:: none
|*)

Reset Initial.

Require Import List.

(* Implementation of ListTest omitted. *)
Definition ListTest (l : list nat) := false.

(*||*)

Fixpoint g (f_n_i1 : list nat -> bool) (j : nat) (l1 : list nat) : bool :=
  match j with
  | 0 => false
  | S j1 => if f_n_i1 (j :: l1) then true else g f_n_i1 j1 l1
  end.

Fixpoint f (n i : nat) (l : list nat) : bool :=
  match i with
  | 0 => ListTest (rev l)
  | S i1 => g (f n i1) (n + n) (i :: l)
  end.

Definition SearchCountList (n : nat) : bool := f n n nil.

(*|
Are you sure simple induction wouldn't have been enough in the
original code? What about well founded induction?

----

**A:** This construction should work. Flipping it around by turning
the captured variables into curried arguments is a good idea. Now, I
have separate functions, and probably can just use plain induction
without extra fuss. Ideally I'd want to be able to say something like:
``induction n``, ``SearchCountList n`` and have all of the extra
premises and loop invariant, etc. But, with this hint, I should be
able to get there more easily and directly.
|*)
