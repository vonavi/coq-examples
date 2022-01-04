(*|
#########################################################
In Coq, "if then else" allows non-boolean first argument?
#########################################################

:Link: https://stackoverflow.com/q/47965062
|*)

(*|
Question
********

I read in a few tutorials that ``if a then b else c`` stands for
``match a with true => b | false => c end``. However the former very
strangely does not check the type of ``a``, while the latter of course
makes sure that ``a`` is a boolean. For instance,
|*)

Check if nil then 1 else 2. (* .unfold *)

Fail Check match nil with true => 1 | false => 2 end. (* .fails .unfold *)

(*|
Why is ``if ... then ... else ...`` allowing its first argument to be
anything else than a non-boolean? Is there some overloading going on?
(``Locate "if".`` gives no result.)
|*)

(*|
Answer
******

Let me quote the `Coq Reference manual
<https://coq.inria.fr/distrib/current/refman/language/gallina-extensions.html#if-then-else>`__:

    For inductive types with exactly two constructors and for
    pattern-matchings expressions which do not depend on the arguments
    of the constructors, it is possible to use a ``if ... then ...
    else ...`` notation. More generally, for an inductive type with
    constructors ``C1`` and ``C2``, we have the following equivalence:

    .. code-block:: coq

        if term [dep_ret_type] then term1 else term2

    is equivalent to

    .. code-block:: coq

        match term [dep_ret_type] with
        | C1 _ ... _ => term1           (* we cannot bind the arguments *)
        | C2 _ ... _ => term2
        end

As you can see, the first constructor is treated as ``true`` value.
Here is an example:
|*)

Definition is_empty {A : Type} (xs : list A) : bool :=
  if xs then true else false.
