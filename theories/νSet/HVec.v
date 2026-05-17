Set Warnings "-stdlib-vector".
From Stdlib Require Import Vectors.Fin.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet.

(** Finite dependent tuples over [Fin.t n]. *)

Fixpoint hvec (n: nat): (Fin.t n -> HSet) -> HSet :=
  match n with
  | 0 => fun _ => hunit
  | S n => fun B => { x: B Fin.F1 & hvec n (fun i => B (Fin.FS i)) }
  end.

Fixpoint hvec_nth {n: nat}:
  forall {B: Fin.t n -> HSet}, hvec n B -> forall i: Fin.t n, B i :=
  match n return forall {B: Fin.t n -> HSet},
    hvec n B -> forall i: Fin.t n, B i with
  | 0 => fun B _ i => Fin.case0 (fun i => B i) i
  | S n => fun B xs i =>
      Fin.caseS' i (fun i => B i) xs.1 (fun i => hvec_nth xs.2 i)
  end.

Fixpoint hvec_map {n: nat}:
  forall {B C: Fin.t n -> HSet},
  (forall i, B i -> C i) -> hvec n B -> hvec n C :=
  match n return forall {B C: Fin.t n -> HSet},
    (forall i, B i -> C i) -> hvec n B -> hvec n C with
  | 0 => fun _ _ _ _ => tt
  | S n => fun B C f xs =>
      (f Fin.F1 xs.1; hvec_map (fun i => f (Fin.FS i)) xs.2)
  end.

Lemma hvec_nth_map {n: nat} {B C: Fin.t n -> HSet}
  (f: forall i, B i -> C i) (xs: hvec n B) (i: Fin.t n):
  hvec_nth (hvec_map f xs) i = f i (hvec_nth xs i).
Proof.
  revert B C f xs i. induction n as [|n IH].
  - intros B C f xs i. now apply Fin.case0 with (p := i).
  - intros B C f xs i.
    apply (Fin.caseS' i (fun i =>
      hvec_nth (hvec_map f xs) i = f i (hvec_nth xs i))).
    + now reflexivity.
    + intro j. cbn.
      now exact (IH _ _ (fun i => f (Fin.FS i)) xs.2 j).
Defined.

Lemma hvec_ext {n: nat} {B: Fin.t n -> HSet} (xs ys: hvec n B):
  (forall i, hvec_nth xs i = hvec_nth ys i) -> xs = ys.
Proof.
  revert B xs ys. induction n as [|n IH].
  - intros B xs ys _. now destruct xs, ys.
  - intros B [x xs] [y ys] H. simpl in H.
    specialize (H Fin.F1) as Hx. simpl in Hx. destruct Hx.
    f_equal. apply IH. intro i. now exact (H (Fin.FS i)).
Defined.
