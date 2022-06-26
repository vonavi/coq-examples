(*|
############################################
Proofs about constructors matched with ``_``
############################################

:Link: https://stackoverflow.com/q/19277175
|*)

(*|
Question
********

Assume I have the following ``Set``:
|*)

Inductive Many : Set :=
| aa : Many
| bb : Many
| cc : Many
(* | ... many more constructors *)
.

(*|
How can I proof in the ``_`` match, that ``y <> aa``?

.. code-block:: coq

    match x with
    | aa     => true
    | _ as y => (* how can I proof that y <> aa ? *)
|*)

(*|
Answer
******

Unfortunately, it does not seem possible to get such a proof without
some more work in pure Gallina. What you would like to write is:
|*)

Definition foo (x : Many) : bool :=
  match x with
  | aa => true
  | y =>
      let yNOTaa : y <> aa :=
        fun yaa =>
          eq_ind y (fun e => match e with aa => False | _ => True end) I aa yaa
      in false
  end.

(*|
But that does not work quite well in Gallina, as it does not expand
the wildcard into all possible cases, leaving ``y`` abstract in the
``eq_ind`` invocation. It does however work in tactic mode:
|*)

Reset foo. (* .none *)
Definition foo (x : Many) : bool.
  refine (
      match x with
      | aa => true
      | y =>
          let yNOTaa : y <> aa :=
            fun yaa =>
              eq_ind y (fun e => match e with aa => False | _ => True end) I aa yaa
          in false
      end).

(*|
But it actually builds the expanded term with all the branches.

----

I just found out that there is a way to have the Vernacular build the
same term that the refine tactic would build. To do so, you have to
force a return annotation mentioning the discriminee, like so:
|*)

Reset foo. (* .none *)
Definition foo (x : Many) : bool :=
  match x return (fun _ => bool) x with
  | aa => true
  | y =>
      let yNOTaa : y <> aa :=
        fun yaa : y = aa =>
          @eq_ind Many y (fun e => match e with aa => False | _ => True end) I aa yaa
      in false
  end.

(*|
My guess is that the term elaboration differs whether the match is
dependent or not...
|*)
