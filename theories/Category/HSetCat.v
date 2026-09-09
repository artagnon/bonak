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

