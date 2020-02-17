Require Import HoTT Coq.Init.Peano.

Definition Book_1_1 := (fun (A B C : Type) (f : A -> B) (g : B -> C) => g o f).

Theorem Book_1_1_refl : forall (A B C D : Type) (f : A -> B) (g : B -> C) (h : C -> D),
                          h o (g o f) = (h o g) o f.
Proof.
  reflexivity.
Defined.

Definition Book_1_2_prod_lib := @HoTT.Types.Prod.equiv_uncurry.
Section Book_1_2_prod.
  Variable A B : Type.

  (** Recursor with projection functions instead of pattern-matching. *)
  Let prod_rec_proj C (g : A -> B -> C) (p : A * B) : C :=
    g (fst p) (snd p).
  Definition Book_1_2_prod := prod_rec_proj.

  Proposition Book_1_2_prod_fst : fst = prod_rec_proj A (fun a b => a).
  Proof.
    reflexivity.
  Defined.

  Proposition Book_1_2_prod_snd : snd = prod_rec_proj B (fun a b => b).
  Proof.
    reflexivity.
  Defined.
End Book_1_2_prod.