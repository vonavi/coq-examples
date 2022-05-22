(*|
########################################################
How to import the library ``Coq.Arith.PeanoNat`` in Coq?
########################################################

:Link: https://stackoverflow.com/q/36621752
|*)

(*|
Question
********

I need to use the part of the standard library called
``Coq.Arith.PeanoNat``
(https://coq.inria.fr/library/Coq.Arith.PeanoNat.html).

I've tried either importing the entire Arith library or just this
module, but I can't use it either way.

Every other library I've tried works just fine. When I do ``Require
Import Bool.`` I compile and I can use it correctly. Upon ``Print
Bool.`` I can take a look at all the functions inside in the next
format:

.. code-block::

    Module
    Bool
    := Struct
    Definition...
    .
    .
    .
    End

When I do either ``Require Import Arith.PeanoNat.`` or ``Require
Import Arith.`` I get this as immediate output:

.. code-block::

    [Loading ML file z_syntax_plugin.cmxs ... done]
    [Loading ML file quote_plugin.cmxs ... done]
    [Loading ML file newring_plugin.cmxs ... done]
    <W> Grammar extension: in [tactic:simple_tactic], some rule has been masked
    <W> Grammar extension: in [tactic:simple_tactic], some rule has been masked
    <W> Grammar extension: in [tactic:simple_tactic], some rule has been masked
    <W> Grammar extension: in [tactic:simple_tactic], some rule has been masked
    <W> Grammar extension: in [tactic:simple_tactic], some rule has been masked

When I ask Coq ``Print Arith.PeanoNat`` it outputs: ``Module Arith :=
Struct End``, it seems to be empty. When I try to use anything from
the library, for example ``le_le`` under boolean comparisons, I get
the standard ``Error: leb_le not a defined object.`` I have updated
Coq and the libraries, and I have no idea of what might be going on
here. I'd appreciate your input in fixing this library problem.
|*)

(*|
Answer
******

If I am not mistaken, ``Require`` is the keyword to load a file.
``Import`` has to do with managing name spaces. Often they are used
together, as in ``Require Import PeanoNat.``, but they are really
doing two different things.

When coq files (``DirName/FileName.vo``) are loaded with ``Require``,
it is as if the contents of ``FileName.vo`` is wrapped in ``Module
DirName.FileName ... End.`` Everyting defined in the file is then
accessed with ``DirName.FileName.Name``.

The file can itself have modules ``M`` inside of it, and to get to
``M``'s contents, one has to type
``DirName.FileName.ModuleName.Name1`` etc.

``Import`` is used to get all the definitions up to the top level. By
doing ``Import DirName.FileName.ModuleName`` the module ``Name1`` is
now imported to the top level, and can be referenced without the long
path.

In your example above, the file ``Arith/PeanoNat.vo`` defines the
module ``Nat``. Actually, that is all it defines. So if you do
``Require Import Arith.PeanoNat`` you get ``PeanoNat.Nat`` at the top
level. And then ``Import PeanoNat.Nat`` will bring ``Nat`` to the top
level. Note that you can't do ``Require Import PeanoNat.Nat`` because
it is no ``.vo`` file.

Coq can sometimes find a ``.vo`` file without you having to specify
the whole path, so you can also do ``Require Import PeanoNat.`` and
coq will find the file. If you wonder where it found it, do ``Locate
PeanoNat``.
|*)

Require Import PeanoNat.
Locate PeanoNat. (* .unfold *)

(*|
Another ``Nat`` is also available from another place than
``PeanoNat``.
|*)

Reset Initial. (* .none *)
Require Import Nat.
Locate Nat. (* .unfold *)

(*|
So, you don't ``Import`` a library, you ``Require`` it. You use
``Import`` to not have to use the full path name. I hope this helps
you debug what is happening.
|*)
