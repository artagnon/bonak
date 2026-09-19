Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet.
From Bonak.Category Require Import Category.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

(** The category of h-sets and functions. Its hom-types are h-sets by
    [hpiT], which is where functional extensionality enters. *)

Definition HSetCat: Category := {|
  CObj := HSet;
  CHom A B := hpiT (fun _: A => B);
  cid A := fun x => x;
  ccomp A B C f g := fun x => g (f x);
  cidl A B f := eq_refl;
  cidr A B f := eq_refl;
  cassoc A B C D f g h := eq_refl;
|}.

(** Functor laws evaluated at an element of the source h-set. *)

Lemma fhomCompPt {C: Category} (F: Functor C HSetCat) {a b c}
  (f: C.(CHom) a b) (g: C.(CHom) b c) (x: F.(fobj) a):
  F.(fhom) g (F.(fhom) f x) = F.(fhom) (f ⨟ g) x.
Proof. exact (eq_sym (f_equal (fun h => h x) (F.(fcomp) f g))). Qed.

Lemma fhomIdPt {C: Category} (F: Functor C HSetCat) a (x: F.(fobj) a):
  F.(fhom) (C.(cid) a) x = x.
Proof. exact (f_equal (fun h => h x) (F.(fid) a)). Qed.
