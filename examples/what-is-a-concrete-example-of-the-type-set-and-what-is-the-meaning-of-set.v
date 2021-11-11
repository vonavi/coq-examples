(*|
What is a concrete example of the type `Set` and what is the meaning of `Set`?
==============================================================================

https://stackoverflow.com/questions/68056978/what-is-a-concrete-example-of-the-type-set-and-what-is-the-meaning-of-set
|*)

(*|
Question
--------

I've been trying to understand what `Set` is after encountering it in
Adam Chlipala's book in addition to `this great discussion in SO
<https://stackoverflow.com/questions/39601502/what-exactly-is-a-set-in-coq>`_.
His first example definition binary ops using `Set`:
|*)

Inductive binop : Set := Plus | Times.

(*| in that book he says:

    Second, there is the : Set fragment, which declares that we are
    defining a datatype that should be thought of as a constituent of
    programs.

Which confuses me. What does Adam mean here?

In addition, I thought that some additional concrete examples would
help my understanding. I am not an expert of Coq so I am not sure what
type of examples would help but something simple and very
concrete/grounded might be useful.

Note, I have seen that `Set` is the first "type set" in a the type
hierarchy e.g. `Set = Type(0) <= Type = Type(1) <= Type(2) <= ...`. I
guess this sort of makes sense intuitively like I'd assume `nat \in
Type` and all usual programming types to be in it but not sure what
would be in `Type` that wouldn't be in `Set`. Perhaps recursive types?
Not sure if that is the right example but I am trying to wrap my head
around what this concept means and it's conceptual (& practical)
usefulness.
|*)

(*|
Answer
------

Though `Set` and `Type` are different in Coq, this is mostly due to
historical reasons. Nowadays, most developments do not rely on `Set`
being different from `Type`. In particular, Adam's comment would also
make sense if you replace `Set` by `Type` everywhere. The main point
is that, when you want to define a datatype that you can compute with
during execution (e.g. a number), you want to put it in `Set` or
`Type` *rather than* `Prop`. This is because things that live in
`Prop` are erased when you extract programs from Coq, so something
defined in `Prop` would end up not computing anything.

As for your second question: `Set` is something that lives in `Type`,
but not in `Set`, as the following snippet shows.
|*)

Check Set : Type. (* This works *)
Fail Check Set : Set.
(* The command has indeed failed with message: *)
(* The term "Set" has type "Type" while it is expected to have type  *)
(* "Set" (universe inconsistency: Cannot enforce Set+1 <= Set). *)

(*|
This restriction is in place to prevent paradoxes in the theory. This
is pretty much the only difference you see between `Set` and `Type` by
default. You can also make them more different by invoking Coq with
the `-impredicative-set` option:
|*)

(* Needs -impredicative-set; otherwise, the first line will also fail.*)
Fail Check (forall A : Set, A -> A) : Set.
Universe u.
Fail Check (forall A : Type@{u}, A -> A) : Type@{u}.
(* The command has indeed failed with message: *)
(* The term "forall A : Type, A -> A" has type "Type@{u+1}" *)
(* while it is expected to have type "Type@{u}" (universe inconsistency: Cannot enforce *)
(* u < u because u = u). *)

(*|
Note that I had to add the `Universe u`. declaration to force the two
occurrences of `Type` to be at the same level. Without this
declaration, Coq would silently put the two `Type`'s at different
universe levels, and the command would be accepted. (This would not
mean that `Type` would have the same behavior as `Set` in this
example, since `Type@{u}` and `Type@{v}` are different things when `u`
and `v` are different!)

If you're wondering why this feature is useful, it is not by chance.
The overwhelming majority of Coq developments does not rely on it. It
is turned off by default because it is incompatible with a few axioms
that are generally considered more useful in Coq developments, such as
the strong law of the excluded middle:
|*)

Axiom excluded_middle : forall A : Prop, {A} + {~ A}.

(*|
With `-impredicative-set` turned on, this axiom yields a paradox,
while it is safe to use by default.
|*)
