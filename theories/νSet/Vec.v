Set Warnings "-stdlib-vector".
From Stdlib Require Import Vectors.Fin.

Module Type FiniteProductSig.
  Parameter Obj : Type.
  Parameter El : Obj -> Type.
  Coercion El : Obj >-> Sortclass.

  Parameter unit_obj : Obj.
  Parameter unit_intro : unit_obj.
  Parameter unit_ext : forall x y: unit_obj, x = y.

  Parameter prod_obj : Obj -> Obj -> Obj.
  Parameter pair : forall {A B: Obj}, A -> B -> prod_obj A B.
  Parameter fst : forall {A B: Obj}, prod_obj A B -> A.
  Parameter snd : forall {A B: Obj}, prod_obj A B -> B.
  Parameter fst_pair : forall {A B: Obj} (x: A) (y: B), fst (pair x y) = x.
  Parameter snd_pair : forall {A B: Obj} (x: A) (y: B), snd (pair x y) = y.
  Parameter prod_ext : forall {A B: Obj} (x y: prod_obj A B),
    fst x = fst y -> snd x = snd y -> x = y.
End FiniteProductSig.

Module FiniteVector (P: FiniteProductSig).
Import P.

(** Finite dependent tuples over [Fin.t n]. *)

Fixpoint vec (n: nat): (Fin.t n -> Obj) -> Obj :=
  match n with
  | 0 => fun _ => unit_obj
  | S n => fun B => prod_obj (B Fin.F1) (vec n (fun i => B (Fin.FS i)))
  end.

Fixpoint vec_nth {n: nat}:
  forall {B: Fin.t n -> Obj}, vec n B -> forall i: Fin.t n, B i :=
  match n return forall {B: Fin.t n -> Obj},
    vec n B -> forall i: Fin.t n, B i with
  | 0 => fun B _ i => Fin.case0 (fun i => B i) i
  | S n => fun B xs i =>
      Fin.caseS' i (fun i => B i) (fst xs) (fun i => vec_nth (snd xs) i)
  end.

Fixpoint vec_map {n: nat}:
  forall {B C: Fin.t n -> Obj},
  (forall i, B i -> C i) -> vec n B -> vec n C :=
  match n return forall {B C: Fin.t n -> Obj},
    (forall i, B i -> C i) -> vec n B -> vec n C with
  | 0 => fun _ _ _ _ => unit_intro
  | S n => fun B C f xs =>
      pair (f Fin.F1 (fst xs)) (vec_map (fun i => f (Fin.FS i)) (snd xs))
  end.

Fixpoint vec_of_fun {n: nat}:
  forall {B: Fin.t n -> Obj}, (forall i, B i) -> vec n B :=
  match n return forall {B: Fin.t n -> Obj}, (forall i, B i) -> vec n B with
  | 0 => fun _ _ => unit_intro
  | S n => fun B f => pair (f Fin.F1) (vec_of_fun (fun i => f (Fin.FS i)))
  end.

Lemma vec_nth_map {n: nat} {B C: Fin.t n -> Obj}
  (f: forall i, B i -> C i) (xs: vec n B) (i: Fin.t n):
  vec_nth (vec_map f xs) i = f i (vec_nth xs i).
Proof.
  revert B C f xs i. induction n as [|n IH].
  - intros B C f xs i. now apply Fin.case0 with (p := i).
  - intros B C f xs i.
    apply (Fin.caseS' i (fun i =>
      vec_nth (vec_map f xs) i = f i (vec_nth xs i))).
    + cbn. now rewrite fst_pair.
    + intro j. cbn. rewrite snd_pair.
      now exact (IH _ _ (fun i => f (Fin.FS i)) (snd xs) j).
Defined.

Lemma vec_nth_of_fun {n: nat} {B: Fin.t n -> Obj}
  (f: forall i, B i) (i: Fin.t n):
  vec_nth (vec_of_fun f) i = f i.
Proof.
  revert B f i. induction n as [|n IH].
  - intros B f i. now apply Fin.case0 with (p := i).
  - intros B f i.
    apply (Fin.caseS' i (fun i => vec_nth (vec_of_fun f) i = f i)).
    + cbn. now rewrite fst_pair.
    + intro j. cbn. rewrite snd_pair.
      now exact (IH _ (fun i => f (Fin.FS i)) j).
Defined.

Lemma vec_ext {n: nat} {B: Fin.t n -> Obj} (xs ys: vec n B):
  (forall i, vec_nth xs i = vec_nth ys i) -> xs = ys.
Proof.
  revert B xs ys. induction n as [|n IH].
  - intros B xs ys _. now apply unit_ext.
  - intros B xs ys H. apply prod_ext.
    + now exact (H Fin.F1).
    + apply IH. intro i. now exact (H (Fin.FS i)).
Defined.

End FiniteVector.
