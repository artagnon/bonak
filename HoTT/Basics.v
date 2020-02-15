From Coq Require Import ssreflect.

Section Logic.
  Theorem FalseImpliesAnything : forall A, False -> A.
  Proof.
    by intros A; exact (fun x : False => match x with end).
  Qed.

  Theorem TrueDoesNotImplyFalse : True -> False.
  Proof.
    (* Due to enforced exhaustive pattern-matching on inhabitants of the LHS,
     * we'd need to match up an inhabitant of True (there is only I)
     * to some inhabitant of False, but there are no inhabitants of False. *)
  Abort.

  (* Any inhabitated type implies unit. *)
  Theorem f : nat -> unit.
  Proof.
    by intros x; exact tt.
  Qed.

  (* The Curry-Howard correspondence applies to f *)
  Definition f' : nat -> unit := fun _ => tt.

  (* This is equivalent to (True -> False) -> False.
   * As both True -> False and False are equally false, this is provable. *)
  Definition Equiconsistent_with_empty : ~True -> False := fun (k : ~True) => k I.
End Logic.

Section Inductives.
  (* Peano naturals *)
  (* How computations on Peano naturals actually works:
   * Compute 2+2.
   * Nat.add (S (S O)) (S (S O)).
   * Nat.add (S (S (S O))) (S O).
   * Nat.add (S (S (S (S O)))) O.
   * Nat.add A (S B) := S (Nat.add A B).
   *)

  (* How proof obligations related to Peano naturals works: *)
  Goal 2+2=4.
  reflexivity.
  Qed.

  Inductive nat : Set := O : nat | S : nat -> nat.
End Inductives.
