(*|
########################################################################################
All-quantified type variable in (value) constructor cannot be explicitly typed as wanted
########################################################################################

:Link: https://stackoverflow.com/q/41104527
|*)

(*|
Question
********

I have the following GADT.
|*)

Inductive GADT : Type -> Type :=
| A : forall A, GADT A
| B : GADT bool.

(*|
And the following data type that has one constructor with an
all-qualified type variable.
|*)

Inductive Wrap A :=
| wrap : GADT A -> Wrap A
| unwrap : forall X, GADT X -> (X -> Wrap A) -> Wrap A.

(*|
Then I want to define a recursive function that uses the function
within ``unwrap``.
|*)

Fail Fixpoint wrappedGADT {A} (xs : Wrap A) : option (GADT A) :=
  match xs with
  | wrap _ x => Some x
  | unwrap _ _ fx k => match fx with
                       | A _ => None
                       | B => wrappedGADT (k true)
                       end
  end. (* .unfold *)

(*|
I was assuming that when I inspect ``fx`` and get case ``B``, the
parameter ``fx`` has type ``GADT bool``, thus, the all-quantified type
variable ``X`` is ``bool`` as well. Is this assumption wrong?

Next, I tried to explicitly type ``unwrap`` as follows.
|*)

Fail Fixpoint wrappedGADT {A} (xs : Wrap A) : option (GADT A) :=
  match xs with
  | wrap _ x => Some x
  | @unwrap _ bool fx k => match fx with
                           | A _ => None
                           | B => wrappedGADT (k true)
                           end
  end. (* .unfold *)

(*| Can anybody give any pointers to the origin of this problem? |*)

(*|
Answer (Daniel Schepler)
************************

Unfortunately, raw match statements in Coq aren't always very smart
about the kind of reasoning you're applying here. The "convoy pattern"
(see CPDT for more information about it) is usually the answer for
resolving this type of problem. The immediate application here would
look something like:
|*)

Fixpoint wrappedGADT {A} (xs : Wrap A) {struct xs} : option (GADT A) :=
  match xs with
  | wrap _ x => Some x
  | unwrap _ _ fx k => match fx in (GADT T)
                             return ((T -> Wrap A) -> option (GADT A)) with
                       | A _ => fun k0 => None
                       | B => fun k0 => wrappedGADT (k0 true)
                       end k
  end.

(*|
However, this runs into another issue, that Coq isn't able to verify
the termination condition after passing the function through the
"convoy". It seems that to work around that, it suffices to first
define the function of recursive calls on values of ``k`` and then
convoy that instead:
|*)

Reset wrappedGADT. (* .none *)
Fixpoint wrappedGADT {A} (xs : Wrap A) {struct xs} : option (GADT A) :=
  match xs with
  | wrap _ x => Some x
  | unwrap _ _ fx k =>
      let r := fun x => wrappedGADT (k x) in
      match fx in (GADT T)
            return ((T -> option (GADT A)) -> option (GADT A)) with
      | A _ => fun _ => None
      | B => fun r' => r' true
      end r
  end.

(*|
For your second code attempt, you're creating a local variable
``bool`` to hold the type called ``X`` in the ``unwrap`` constructor,
which is then shadowing the ``Datatypes.bool`` definition. In general,
there's no way to match only on one specific type in the Coq kernel
language (although typeclasses provide a way to simulate that,
somewhat).
|*)

(*|
Answer (Anton Trunov)
*********************

Here is an alternative implementation, which constructs
``wrappedGADT``'s body using tactics. It has one advantage that it
doesn't require manual ``return`` annotations from the user. The
overall structure closely resembles your original code with the
``match`` expression.

It is crucial to use ``induction xs`` as opposed to ``destruct xs``
here, because the ``Wrap`` type is recursive.
|*)

Fixpoint wrappedGADT' {A} (xs : Wrap A) : option (GADT A).
  induction xs as [x | ? fx k r].
  - exact (Some x).
  - destruct fx as [T | ].
    + exact None.
    + exact (r true).
Defined.

(*|
Here is a proof that the two implementations are extensionally equal.
|*)

Goal forall (A : Type) (xs : Wrap A),
    wrappedGADT xs = wrappedGADT' xs.
Proof with auto.
  intros A xs.
  induction xs...
  destruct g...
  simpl; rewrite H; destruct (w true)...
Qed.

(*|
----

If we look at the term generated for ``wrappedGADT'`` (using ``Print
wrappedGADT'.``), we'll be able to construct one more solution using
the ``Wrap_rect`` induction principle generated for the ``Wrap``
datatype (I just removed unused variable ``k`` from the ``match``
expression in ``wrappedGADT'``):
|*)

Definition wrappedGADT'' {A} (xs : Wrap A) : option (GADT A) :=
  Wrap_rect _
            _
            (fun t => Some t)
            (fun _ fx k r =>
               match fx in (GADT T)
                     return ((T -> option (GADT A)) -> option (GADT A)) with
               | A _ => fun _ => None
               | B => fun r' => r' true
               end r)
            xs.

(*|
This solution can then lead to a solution a-la `Daniel's
<https://stackoverflow.com/a/41111181/2747511>`__, if we unfold
``Wrap_rect``, implemented as ``Fixpoint`` itself.
|*)
