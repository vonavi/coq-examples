(*|
###################################################
Coq: coercion/subtyping between complex expressions
###################################################

:Link: https://stackoverflow.com/q/38416025
|*)

(*|
Question
********

I've got an impression that it's impossible in Coq. For example

.. code-block:: coq

    Parameter Arg : Type.
    Parameter F X XP : Arg.
    Parameter S P I PLS PI : Arg -> Type.
    Parameter tree car : P X.
    Parameter mary john : PLS XP.
    Parameter c : PLS XP -> P XP.
    Coercion c : PLS XP >-> P XP.
    (* Syntax error: '>->' expected after [vernac:class_rawexpr] (in
       [vernac:gallina_ext]). *)

So not only must the types of the expressions next to ``>->`` be
``Set``, ``Type`` or ``Prop``, the expressions themselves must also be
syntactically elementary ("rawexpressions" in Gallina?)? How to bypass
this; can I form a coercion between complex expression? Is there
another way to define a subtype in Coq, one which would work w/
complex expressions? Can I do better than

.. code-block:: coq

    Let nui := PLS XP.
    Let hui := P XP.
    Parameter c : nui -> hui.
    Coercion c : nui >-> hui.
    Parameter st : P XP -> Type.
    Check st (c mary). (* st mary : Type *)
    Check st mary.
    (* Error: The term "mary" has type "PLS XP" while it is expected
       to have type "P XP".*)
|*)

(*|
Answer (ejgallego)
******************

IMVHO, the setup of the problem is looking very complicated; I am not
sure this modeling method will be effective (in the sense of
efficient).

If you really want to go that route, note that Coercions have very
particular rules; if you want to use them you'll have to get familiar
with `chapter 18
<https://coq.inria.fr/refman/Reference-Manual021.html>`__ of the
manual. In particular, I think that parameters cannot be made a source
class so you will have to add some wrapping:
|*)

Parameter Arg : Type.
Parameter F X XP : Arg.
Parameter S P I PLS PI : Arg -> Type.
Parameter tree car : P X.
Parameter mary john : PLS XP.
Parameter c : PLS XP -> P XP.

Inductive p_wrap := p_wrap_C : PLS XP -> p_wrap.
Coercion u_cast x := match x with | p_wrap_C u => u   end.
Coercion c_cast x := match x with | p_wrap_C u => c u end.

Parameter st: P XP -> Type.
Definition Mary := p_wrap_C mary.
Check st (c Mary).
Check st Mary.

(*|
YMMV. Note that the general ``subType`` class in ssreflect `doc
<http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.eqtype.html>`__
may provide some help on how to make a generic coercion framework.

----

**Q:** Good! I didn't know you can define coercions without a prior
function declaration. All this is indeed complex (it's mostly my and
the manual's fault). I tried something under `chapter 18; Examples
<https://coq.inria.fr/refman/Reference-Manual021.html#sec674>`__ (will
probably make it into an answer after some sleep)

**Q:** It's very confusing that you can define a coercion:
|*)

Reset c. (* .none *)
Parameter c : PLS XP -> P XP.
Coercion c: PLS >-> P. (* .unfold *)
Print Coercions. (* .unfold *)
Print Graph. (* .unfold *)

(*|
and yet there's no coercion:

.. code-block:: coq

    Check mary : P XP.
    (* Error: The term "mary" has type "PLS XP" while it is expected
       to have type "P XP". *)

So the real problem is fulfilling the uniform inheritance condition.
``P x`` is a superset of ``PLS x``, which is an intersection of ``P
x``, ``L x`` and ``S x``. So I might even pretend that ``c`` is "a
coercion which must be explicitly specified"

**A:** I agree is very confusing; in practice it seems that "does not
respect the uniform inheritance" means "your coercion will never be
considered for application".
|*)

(*|
Answer (jaam)
*************

After trying this, that and whatnot, the solution was surprisingly
easy. There were two steps my question was missing:

1. You can coerce *functions* towards one another, i.e. ``Coercion c :
   PLS >-> P`` works
2. To avoid breaking the `"uniform inheritance condition"
   <https://coq.inria.fr/refman/Reference-Manual021.html#sec657>`__,
   you must define the function you want to make into a coercion in
   its general (``forall``) form

In sum:
|*)

Reset Initial. (* .none *)
Parameter Arg : Type.
Parameter F X XP : Arg.
Parameter S P I PLS PI : Arg -> Type.
Parameter tree car : P X.
Parameter mary john : PLS XP.
Parameter c : forall x : Arg, PLS x -> P x.
Coercion c : PLS >-> P.
Check mary : P XP.
