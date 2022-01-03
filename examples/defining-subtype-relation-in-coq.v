(*|
################################
Defining subtype relation in Coq
################################

:Link: https://stackoverflow.com/q/51406616
|*)

(*|
Question
********

Is there a way to define subtype relationship in Coq?

I read about subset typing, in which a predicate is used to determine
what goes into the subtype, but this is not what I am aiming for. I
just want to define a theory in which there is a type (U) and another
type (I), which is subtype of (U).
|*)

(*|
Answer
******

There is no true subtyping in Coq (except for universe subtyping,
which is probably not what you want). The closest alternative is to
use coercions, which are functions that the Coq type checker inserts
automatically whenever it is expecting an element of one type but
finds an element of another type instead. For instance, consider the
following coercion from booleans to natural numbers:
|*)

Definition nat_of_bool (b : bool) : nat :=
  if b then 1 else 0.

Coercion nat_of_bool : bool >-> nat.

(*|
After running this snippet, Coq uses ``nat_of_bool`` to convert
``bool`` to ``nat``, as shown here:
|*)

Check true + 3. (* .unfold *)

(*|
Thus, ``bool`` starts behaving almost as if it were a subtype of ``nat``.

Though ``nat_of_bool`` does not appear here, it is just being hidden
by Coq's printer. This term is actually the same thing as
``nat_of_bool true + 3``, as we can see by asking Coq to print all
coercions:
|*)

Set Printing Coercions.
Check true + 3. (* .unfold *)

(*|
The ``:>`` symbol `you had asked about earlier
<https://stackoverflow.com/questions/51404367/the-coq-symbol>`__, when
used in a record declaration, is doing the same thing. For instance,
the code
|*)

Record foo := Foo {
                  sort :> Type
                }.

(*| is equivalent to |*)

Reset foo. (* .none *)
Record foo := Foo {
                  sort : Type
                }.

Coercion sort : foo >-> Sortclass.

(*|
where ``Sortclass`` is a special coercion target for ``Type``,
``Prop`` and ``Set``.

The `Coq user manual
<https://coq.inria.fr/refman/addendum/implicit-coercions.html>`__
describes coercions in more detail.
|*)
