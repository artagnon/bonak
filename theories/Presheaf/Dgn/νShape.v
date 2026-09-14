(** Normal forms for the ν-shape category.

    A morphism from [p] to [n] first selects [k] input coordinates, then
    inserts labelled constants among those coordinates. The selection mask
    has length [p] and [k] retained positions; the face word has length [n]
    and [k] variable positions. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Notation NatLemmas.
From Bonak.Category Require Import Category.
From Bonak.Presheaf Require Export νSemiShape.
Set Primitive Projections.
Set Printing Projections.

Section Shape.
Context (A: HSet).

Definition Shape (p n: nat): Type :=
  {k: nat &T Word hunit k p * Word A k n}.

Definition shapeConst {p n} (a: A) (s: Shape p n): Shape p (S n) :=
  (s.1; (fst s.2, wskip a (snd s.2))).
Definition shapeDrop {p n} (s: Shape p n): Shape (S p) n :=
  (s.1; (wskip (A := hunit) tt (fst s.2), snd s.2)).
Definition shapeKeep {p n} (s: Shape p n): Shape (S p) (S n) :=
  (S s.1; (wkeep (fst s.2), wkeep (snd s.2))).

(** Move a coordinate selection past a labelled face word. A constant
    discarded by the selection disappears; a retained variable survives
    precisely when both words retain its position. *)

Fixpoint cross (m: nat): forall k l, Word A k m -> Word hunit l m -> Shape k l.
Proof.
  destruct m as [|m].
  - intros [|k] [|l] f d; try destruct f; try destruct d.
    exact (0; (wnil, wnil)).
  - intros k l f d.
    destruct f as [[a f]|f], d as [[[] d]|d].
    + exact (cross m k l f d).
    + destruct l as [|l]; [destruct d|].
      exact (shapeConst a (cross m k l f d)).
    + destruct k as [|k]; [destruct f|].
      exact (shapeDrop (cross m k l f d)).
    + destruct k as [|k], l as [|l]; try destruct f; try destruct d.
      exact (shapeKeep (cross m k l f d)).
Defined.

Arguments cross {m k l} f d.

Definition shapeId (n: nat): Shape n n := (n; (wid n, wid n)).
Definition shapeFace {p n} (f: Word A p n): Shape p n := (p; (wid p, f)).
Definition shapeMask {p n} (d: Word hunit n p): Shape p n := (n; (d, wid n)).

Definition shapeSandwich {p k l n} (r: Word hunit k p) (f: Word A l n)
  (s: Shape k l): Shape p n :=
  (s.1; (wcomp r (fst s.2), wcomp f (snd s.2))).

Definition shapeComp {p m n} (f: Shape p m) (g: Shape m n): Shape p n :=
  shapeSandwich (fst f.2) (snd g.2) (cross (snd f.2) (fst g.2)).

Lemma crossIdL (m: nat): forall k (d: Word hunit k m),
  cross (wid m) d = shapeMask d.
Proof.
  induction m as [|m IH]; intros k d.
  - destruct k as [|k]; [destruct d; reflexivity|destruct d].
  - destruct d as [[[] d]|d].
    + cbn [wid cross wkeep wskip]. rewrite IH. reflexivity.
    + destruct k as [|k]; [destruct d|].
      cbn [wid cross wkeep wskip]. rewrite IH. reflexivity.
Qed.

Lemma crossIdR (m: nat): forall k (f: Word A k m),
  cross f (wid m) = shapeFace f.
Proof.
  induction m as [|m IH]; intros k f.
  - destruct k as [|k]; [destruct f; reflexivity|destruct f].
  - destruct f as [[a f]|f].
    + cbn [wid cross wkeep wskip]. rewrite IH. reflexivity.
    + destruct k as [|k]; [destruct f|].
      cbn [wid cross wkeep wskip]. rewrite IH. reflexivity.
Qed.

Lemma shapeIdL {p n} (s: Shape p n): shapeComp (shapeId p) s = s.
Proof.
  destruct s as [k [r f]]. unfold shapeComp, shapeId; cbn.
  rewrite crossIdL. unfold shapeSandwich, shapeMask; cbn.
  rewrite wcompIdl, wcompIdr. reflexivity.
Qed.

Lemma shapeIdR {p n} (s: Shape p n): shapeComp s (shapeId n) = s.
Proof.
  destruct s as [k [r f]]. unfold shapeComp, shapeId; cbn.
  rewrite crossIdR. unfold shapeSandwich, shapeFace; cbn.
  rewrite wcompIdl, wcompIdr. reflexivity.
Qed.

(** Normalization commutes with composing face words. *)

Lemma crossCompFace (m: nat): forall k l n
  (g: Word A k m) (f: Word A l k) (d: Word hunit n m),
  cross (wcomp g f) d =
  let s := cross g d in
  shapeSandwich (wid l) (snd s.2) (cross f (fst s.2)).
Proof.
  induction m as [|m IH]; intros k l n g f d.
  - destruct k as [|k], n as [|n]; try destruct g; try destruct d.
    destruct l as [|l]; [destruct f; reflexivity|destruct f].
  - destruct g as [[a g]|g], d as [[[] d]|d].
    + exact (IH k l n g f d).
    + destruct n as [|n]; [destruct d|].
      cbn [wcomp cross wskip wkeep shapeConst shapeSandwich].
      rewrite IH. reflexivity.
    + destruct k as [|k]; [destruct g|].
      destruct f as [[a f]|f].
      * cbn [wcomp cross wskip wkeep shapeDrop shapeSandwich].
        exact (IH k l n g f d).
      * destruct l as [|l]; [destruct f|].
        cbn [wcomp cross wskip wkeep shapeDrop shapeSandwich wid].
        rewrite IH. reflexivity.
    + destruct k as [|k], n as [|n]; try destruct g; try destruct d.
      destruct f as [[a f]|f].
      * cbn [wcomp cross wskip wkeep shapeKeep shapeConst shapeSandwich].
        rewrite IH. reflexivity.
      * destruct l as [|l]; [destruct f|].
        cbn [wcomp cross wskip wkeep shapeKeep shapeSandwich wid].
        rewrite IH. reflexivity.
Qed.

(** Normalization commutes with composing selection masks. *)

Lemma crossCompMask (m: nat): forall k n l
  (f: Word A k m) (d: Word hunit n m) (e: Word hunit l n),
  cross f (wcomp d e) =
  let s := cross f d in
  shapeSandwich (fst s.2) (wid l) (cross (snd s.2) e).
Proof.
  induction m as [|m IH]; intros k n l f d e.
  - destruct k as [|k], n as [|n]; try destruct f; try destruct d.
    destruct l as [|l]; [destruct e; reflexivity|destruct e].
  - destruct f as [[a f]|f], d as [[[] d]|d].
    + exact (IH k n l f d e).
    + destruct n as [|n]; [destruct d|].
      destruct e as [[[] e]|e].
      * cbn [wcomp cross wskip wkeep shapeConst shapeSandwich].
        exact (IH k n l f d e).
      * destruct l as [|l]; [destruct e|].
        cbn [wcomp cross wskip wkeep shapeConst shapeSandwich wid].
        rewrite IH. reflexivity.
    + destruct k as [|k]; [destruct f|].
      cbn [wcomp cross wskip wkeep shapeDrop shapeSandwich].
      rewrite IH. reflexivity.
    + destruct k as [|k], n as [|n]; try destruct f; try destruct d.
      destruct e as [[[] e]|e].
      * cbn [wcomp cross wskip wkeep shapeKeep shapeDrop shapeSandwich].
        rewrite IH. reflexivity.
      * destruct l as [|l]; [destruct e|].
        cbn [wcomp cross wskip wkeep shapeKeep shapeSandwich wid].
        rewrite IH. reflexivity.
Qed.

Lemma shapeAssoc {p m n q} (f: Shape p m) (g: Shape m n) (h: Shape n q):
  shapeComp (shapeComp f g) h = shapeComp f (shapeComp g h).
Proof.
  destruct f as [i [r f]], g as [j [s g]], h as [k [t h]].
  unfold shapeComp; cbn.
  rewrite crossCompFace, crossCompMask.
  destruct (cross f s) as [l [u v]]; cbn.
  destruct (cross g t) as [o [w z]]; cbn.
  destruct (cross v w) as [a [b c]]; cbn.
  unfold shapeSandwich; cbn.
  repeat rewrite wcompIdl; repeat rewrite wcompIdr; repeat rewrite wcompAssoc. reflexivity.
Qed.

Definition shapeSet (p n: nat): HSet :=
  hsigT (A := {| Dom := nat; UIP := @natUIP |})
    (fun k => prodSet (wordSet (A := hunit) k p) (wordSet (A := A) k n)).

Definition νShape: Category := {|
  CObj := nat;
  CHom := shapeSet;
  cid := shapeId;
  ccomp p m n f g := shapeComp f g;
  cidl p n f := shapeIdL f;
  cidr p n f := shapeIdR f;
  cassoc p m n q f g h := shapeAssoc f g h;
|}.

End Shape.

Arguments shapeId {A} n.
Arguments shapeComp {A p m n} f g.
Arguments shapeConst {A p n} a s.
Arguments shapeDrop {A p n} s.
Arguments shapeKeep {A p n} s.
Arguments shapeFace {A p n} f.
Arguments shapeMask {A p n} d.
Arguments cross {A m k l} f d.
Arguments shapeSandwich {A p k l n} r f s.
