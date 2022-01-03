(*|
########################################################
use module signature definition in module implementation
########################################################

:Link: https://stackoverflow.com/q/49310103
|*)

(*|
Question
********

I'm not very familiar with modules in Coq, but it was brought up in a
recent question I asked. I have the following code.
|*)

Module Type Sig.
  Parameter n : nat.
  Definition n_plus_1 := n + 1.
End Sig.

Module ModuleInstance <: Sig.
  Definition n := 3.
Fail End ModuleInstance. (* .fails *)

(*|
Coq complains about the definition of ``n_plus_1`` when I try to run
``End ModuleInstance``. I'm not sure if this is a correct way to use
modules, but I want it to just use the definition in the signature,
it's a complete definition that doesn't need any additional
information. Is it possible to do it?
|*)

(*|
Answer (Tej Chajed)
*******************

You'll need to put your definitions into a separate "module functor"
(basically a module-level function: these are modules that takes other
modules as parameters) so that ``Sig`` contains only parameters:
|*)

Reset Initial. (* .none *)
Module Type Sig.
  Parameter n : nat.
End Sig.

(* this is the module functor *)
Module SigUtils (S : Sig).
  Definition n_plus_1 := S.n + 1.
End SigUtils.

Module ModuleInstance <: Sig.
  Definition n := 3.
End ModuleInstance.

Module ModuleInstanceUtils := SigUtils ModuleInstance.

(*|
It's not terribly hard but there is one big limitations: you can't use
any of your utilities as part of the signature (eg, to make type
signatures shorter). Another limitation is that your basic definitions
and derived definitions/properties are in separate modules, so if you
qualify your references you'll have to use the right name. This is
irrelevant if you import the modules, though.

This is the pattern the standard library follows in a few places; for
example, the ``FSetFacts`` and ``FSetProperties`` functors.
|*)

(*|
Answer (Blaisorblade)
*********************

As an alternative to https://stackoverflow.com/a/49322214/53974, one
can sometimes use ``Include``, which supports a very limited special
case of recursive linking. Like in that answer, you should put your
definitions in a module functor, but then you can ``Include`` that,
both in the rest of your signature, and in the implementing module.
That allows to reuse your definitions to shorten the declarations, and
to have them as part of the same module.
|*)

Reset Initial. (* .none *)
Require Import Lia.

Module Type Sig.
  Parameter n : nat.
End Sig.

(* this is the module functor *)
Module SigUtils (S : Sig).
  Definition n_plus_1 := S.n + 1.
End SigUtils.

Module ModuleInstance <: Sig.
  Definition n := 3.
  Include SigUtils.
End ModuleInstance.

Module Type Sig2 <: Sig.
  Include Sig.
  Include SigUtils.
  Parameter n_plus_1_eq: n_plus_1 = 1 + n.
End Sig2.

Module ModuleInstance2 <: Sig2.
  Include ModuleInstance.

  Lemma n_plus_1_eq: n_plus_1 = 1 + n.
  Proof. unfold n_plus_1. lia. Qed.

  Lemma n_plus_1_neq: n_plus_1 <> 2 + n.
  Proof. unfold n_plus_1. lia. Qed.
End ModuleInstance2.

(*|
However, you'll want to beware the semantics of ``Include`` (see e.g.
https://stackoverflow.com/a/49717951/53974). In particular, should you
include a module in two different modules, you'll get distinct
definitions. Above, ``SigUtils`` is included once in a ``Module Type``
and once in an implementing ``Module``, which is allowed.

EDIT: I found a big application of this pattern in the Coq standard
library. Lots of properties of numbers are proved generically and
collected in various module types (such as ``NExtraProp`` `here
<https://github.com/coq/coq/blob/6d6b2d7132bc768783bad6738d778519c28c8f08/theories/Numbers/Natural/Abstract/NProperties.v#L27-L30>`__),
and then used in concrete definitions through ``Include``, such as
`here
<https://github.com/coq/coq/blob/6d6b2d7132bc768783bad6738d778519c28c8f08/theories/Arith/PeanoNat.v#L727>`__.
|*)
