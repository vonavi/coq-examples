(** *** Reducto ad absurdium *)
(**
   Below is another staple of logic: reduction to absurdity. If a
   proposition has a proof and you prove that it cannot have a proof,
   then you can conclude anything.
*)

Theorem absurd2 : forall A B : Prop, A -> ~ A -> B.
Proof.
  intros A B Ht Hf. specialize (Hf Ht). case Hf.
Qed.
