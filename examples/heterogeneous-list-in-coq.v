(*|
#########################
Heterogeneous list in Coq
#########################

:Link: https://stackoverflow.com/q/29404082
|*)

(*|
Question
********

I'm considering writing a Coq program to verify certain properties of
`relational algebra
<http://en.wikipedia.org/wiki/Relational_algebra>`__. I've got some of
the basic data types working, but concatenating tuples is giving me
some trouble.

Here's the relevant section of code:
|*)

Require Import List.
Require Import String.

(* An enum representing SQL types *)
Inductive sqlType : Set := Nat | Bool.

(* Defines a map from SQL types (which are just enum values) to Coq types. *)
Fixpoint toType (t : sqlType) : Set :=
  match t with
  | Nat => nat
  | Bool => bool
  end.

(* A column consists of a name and a type. *)
Inductive column : Set :=
| Col : string -> sqlType -> column.

(* A schema is a list of columns. *)
Definition schema : Set := list column.

(* Concatenates two schema together. *)
Definition concatSchema (r : schema) (s : schema) : schema := app r s.

(* Sends a schema to the corresponding Coq type. *)
Fixpoint tuple (s : schema) : Set :=
  match s with
  | nil => unit
  | cons (Col str t) sch => prod (toType t) (tuple sch)
  end.

Fail Fixpoint concatTuples {r : schema} {s : schema}
         (a : tuple r) (b : tuple s) : tuple (concatSchema r s) :=
  match r with
  | nil => b
  | cons _ _ => (fst a, concatTuples (snd a) b)
  end. (* .fails .unfold *)

(*|
I think I understand what's happening there; the type checker can't
figure out that ``s`` and ``concatSchema nil s`` are equal. But what I
find weirder is that when I add the following line:
|*)

Definition stupid {s : schema} (b : tuple s) : tuple (concatSchema nil s) := b.

(*|
and change the case to ``nil => stupid b``, it works. (Well, it still
complains at the cons case, but I think that means it's accepting the
``nil`` case.)

I have three questions about this:

1. Is there a way to eliminate ``stupid``? It seems like Coq knows the
   types are equal, it just needs some kind of hint.
2. How on earth can I do the cons case? I'm having lots of trouble
   writing a ``stupid``-like function.
3. Is this even the right approach to heterogeneous lists? It seems
   like the most straightforward one to me, but I have a very loose
   grasp of Curry-Howard, and what Coq code actually means.
|*)

(*|
Answer
******

This is one of the most recurrent problems for newcomers in Coq: not
being able to show Coq how to use the additional information one gains
in the branches of a ``match`` statement.

The solution is to use the so-called `convoy pattern
<http://adam.chlipala.net/cpdt/html/MoreDep.html>`__, re-abstracting
the arguments that depend on your scrutinee and making your ``match``
return a function:
|*)

Fixpoint concatTuples {r : schema} {s : schema} :
  tuple r -> tuple s -> tuple (concatSchema r s) :=
  match r return tuple r -> tuple s -> tuple (concatSchema r s) with
  | nil => fun a b => b
  | cons (Col _ t) _ => fun a b => (fst a, concatTuples (snd a) b)
  end.

(*|
In this particular case, the ``return`` annotation is not actually
needed, as Coq can infer it. However, omitting it can often lead to
incomprehensible error messages when things go a bit wrong, so it's a
nice idea to leave them in. Notice that we had to also include a
nested match on the first element of our list (the ``Col _ t``
pattern), in order to mimic the pattern in the definition of
``tuple``. Once again, `CPDT
<http://adam.chlipala.net/cpdt/html/MoreDep.html>`__ explains in great
detail what is going on here and how to write this sort of function in
Coq.

To answer your last question, many developments to heterogeneous lists
more or less in the same way you're doing here (I for instance have
`one development
<https://github.com/arthuraa/coq-utils/blob/master/theories/hseq.v>`__
that is pretty similar to this one). If I had to change anything, I
would remove the nested pattern in the definition of ``tuple``, which
allows you do write this sort of code while using less ``match``\ es
and annotations. Compare:
|*)

Reset tuple. (* .none *)
Definition typeOfCol c :=
  match c with
  | Col _ t => t
  end.

(* Sends a schema to the corresponding Coq type. *)
Fixpoint tuple (s : schema) : Set :=
  match s with
  | nil => unit
  | cons col sch => prod (toType (typeOfCol col)) (tuple sch)
  end.

Fixpoint concatTuples {r : schema} {s : schema} :
  tuple r -> tuple s -> tuple (concatSchema r s) :=
  match r return tuple r -> tuple s -> tuple (concatSchema r s) with
  | nil => fun a b => b
  | cons _ _ => fun a b => (fst a, concatTuples (snd a) b)
  end.

(*|
You can find other examples of this issue `here
<https://stackoverflow.com/questions/16952524/structural-recursion-on-a-dependent-parameter>`__
and `here
<https://stackoverflow.com/questions/28487158/implementing-vector-addition-in-coq>`__.
|*)
