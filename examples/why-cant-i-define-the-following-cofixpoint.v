(*|
################################################
Why can't I define the following ``CoFixpoint``?
################################################

:Link: https://stackoverflow.com/q/30023530
|*)

(*|
Question
********

I defined the following ``CoInductive`` type, ``stream``:
|*)

CoInductive stream (A : Type) : Type :=
| Cons : A -> stream A -> stream A.

Check stream. (* .unfold *)

Check Cons. (* .unfold *)

(*|
Then, I tried to define the following ``CoFixpoint`` definition, ``zeros``:
|*)

Fail CoFixpoint zeros : stream nat := Cons 0 zeros. (* .fails *)

(*|
I figured out that I have to explicitly instantiate the variable A:
|*)

CoFixpoint zeros : stream nat := Cons nat 0 zeros.

(*|
Why doesn't the Coq infer the type of ``A`` by itself? How do I make
it infer the type of ``A``?
|*)

(*|
Answer
******

You need to declare ``A`` as implicit to ask Coq to infer it for you.
There are a few ways of doing it:

1. Add the following declaration to your file: ``Set Implicit
   Arguments.``. This will cause Coq to turn on automatic inference
   for arguments such as ``A`` for ``Cons``, allowing you to write
   ``Cons 0 zeros``.

2. Turn on implicit arguments just for ``Cons``, without affecting the
   rest of the file:
|*)

Arguments Cons {A} _ _.

(*|
   This declaration marks ``A`` as implicit and leaves the other two
   arguments as explicit.

3. Mark ``A`` as implicit in the definition of ``stream``:

   .. coq::
|*)

Reset Initial. (* .none *)
CoInductive stream {A : Type} : Type :=
| Cons : A -> stream -> stream.

(*|
   I personally do not recommend doing this, however, as it will mark
   ``A`` as implicit for ``stream`` as well.

You can find more information about implicit arguments in the
`reference manual
<https://coq.inria.fr/distrib/current/refman/Reference-Manual004.html#sec100>`__

----

**A:** Side note: items 2. and 3. declare ``A`` as a
`maximally-inserted
<https://coq.inria.fr/refman/Reference-Manual004.html#Implicit%20Arguments>`__
argument. Implicit arguments inferred with the ``Set Implicit
Arguments`` directive are not declared to be insertable maximally. So,
when applicable, one might want to add ``Set Maximal Implicit
Insertion.``.
|*)
