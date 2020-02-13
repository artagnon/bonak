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

  (* Any inhabitated type implies unit *)
  Theorem f : nat -> unit.
  Proof.
    intros x.
    exact tt.
  Qed.

  (* The Curry-Howard correspondence applies to f *)
  Definition f' : nat -> unit := fun _ => tt.

  (* This is equivalent to (True -> False) -> False.
   * As both True -> False and False are equally false, this is provable.
   *)
  Definition Equiconsistent_with_empty : ~True -> False := fun (k : ~True) => k I.

  (* Peano naturals *)
  Inductive nat : Set := O : nat | S : nat -> nat.
End Basics.
