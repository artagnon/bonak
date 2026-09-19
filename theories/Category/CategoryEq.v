(** Extensionality for functors. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation.
From Bonak.Category Require Import Category.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

(** Extensionality for functors: the object and arrow parts determine the
    functor, because the two functoriality fields are equalities in
    hom-[HSet]s. *)

Lemma functorEq {C D} (F G: Functor C D) (Hobj: F.(fobj) = G.(fobj))
  (Hhom: forall a b (f: C.(CHom) a b),
     rew [fun o => D.(CHom) (o a) (o b)] Hobj in F.(fhom) f = G.(fhom) f):
  F = G.
Proof.
  destruct F as [Fo Fh Fi Fc], G as [Go Gh Gi Gc]; simpl in *.
  destruct Hobj; simpl in Hhom.
  assert (e: Fh = Gh).
  { apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro b.
    apply functional_extensionality_dep; intro f. now exact (Hhom a b f). }
  destruct e.
  assert (ei: Fi = Gi).
  { apply functional_extensionality_dep; intro a. now apply (D.(CHom)). }
  assert (ec: Fc = Gc).
  { apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro b.
    apply functional_extensionality_dep; intro c.
    apply functional_extensionality_dep; intro f.
    apply functional_extensionality_dep; intro g. now apply (D.(CHom)). }
  now destruct ei, ec.
Qed.

(** Functor data over a fixed map on objects. *)

Definition FunctorOn {C D: Category} (Fo: C.(CObj) -> D.(CObj)): Type :=
  {Fh: forall a b, C.(CHom) a b -> D.(CHom) (Fo a) (Fo b) &T
   {Fi: forall a, Fh a a (C.(cid) a) = D.(cid) (Fo a) &T
    forall a b c (f: C.(CHom) a b) (g: C.(CHom) b c),
      Fh a c (f ⨟ g) = Fh a b f ⨟ Fh b c g}}.

Definition ofFunctorOn {C D: Category} {Fo: C.(CObj) -> D.(CObj)}
  (z: FunctorOn Fo): Functor C D := {|
  fobj := Fo;
  fhom a b f := z.1 a b f;
  fid a := z.2.1 a;
  fcomp a b c f g := z.2.2 a b c f g;
|}.

Definition toFunctorOn {C D: Category} (F: Functor C D): FunctorOn F.(fobj) :=
  (fun a b f => F.(fhom) f;
   (fun a => F.(fid) a; fun a b c f g => F.(fcomp) f g)).
