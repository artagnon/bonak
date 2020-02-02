Section Basics.
  Theorem FalseImpliesAnything : forall A, False -> A.
  Proof.
    intros A.
    exact (fun x : False => match x with end).
  Qed.

  Theorem TrueDoesNotImplyFalse : True -> False.
  Proof.
    (* Due to enforced exhaustive pattern-matching on inhabitants of the LHS,
    * we'd need to match up an inhabitant of True (there is only I)
    * to some inhabitant of False, but there are no inhabitants of False.
    *)
  Abort.
  Theorem f : nat -> unit.
  Proof.
    intros x.
    exact tt.
  Qed.

  Definition f' : nat -> unit := fun _ => tt.
End Basics.
