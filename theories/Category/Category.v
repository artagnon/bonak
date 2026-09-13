(** Categories with a [Type] of objects and [HSet] hom-types.

    The three category laws are equalities in hom-h-sets, so any two proofs
    of them agree by [UIP]. Composition is written in diagrammatic order:
    [f ⨟ g] is [f] followed by [g]. *)

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation.
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Record Category := {
  CObj: Type;
  CHom: CObj -> CObj -> HSet;
  cid a: CHom a a;
  ccomp {a b c} (f: CHom a b) (g: CHom b c): CHom a c;
  cidl {a b} (f: CHom a b): ccomp (cid a) f = f;
  cidr {a b} (f: CHom a b): ccomp f (cid b) = f;
  cassoc {a b c d} (f: CHom a b) (g: CHom b c) (h: CHom c d):
    ccomp (ccomp f g) h = ccomp f (ccomp g h);
}.

Arguments ccomp {_ _ _ _} _ _.
Arguments cid {_} _.

Infix "⨟" := ccomp (at level 40, left associativity).

(** The opposite category *)

Definition Op (C: Category): Category := {|
  CObj := C.(CObj);
  CHom a b := C.(CHom) b a;
  cid a := C.(cid) a;
  ccomp a b c f g := C.(ccomp) g f;
  cidl a b f := C.(cidr) f;
  cidr a b f := C.(cidl) f;
  cassoc a b c d f g h := eq_sym (C.(cassoc) h g f);
|}.

(** Functors *)

Record Functor (C D: Category) := {
  fobj: C.(CObj) -> D.(CObj);
  fhom {a b} (f: C.(CHom) a b): D.(CHom) (fobj a) (fobj b);
  fid a: fhom (C.(cid) a) = D.(cid) (fobj a);
  fcomp {a b c} (f: C.(CHom) a b) (g: C.(CHom) b c):
    fhom (f ⨟ g) = fhom f ⨟ fhom g;
}.

Arguments fobj {C D} _ _.
Arguments fhom {C D} _ {a b} _.
Arguments fid {C D} _ _.
Arguments fcomp {C D} _ {a b c} _ _.

Definition compFunctor {C D E} (F: Functor C D) (G: Functor D E):
  Functor C E := {|
  fobj a := G.(fobj) (F.(fobj) a);
  fhom a b f := G.(fhom) (F.(fhom) f);
  fid a := f_equal G.(fhom) (F.(fid) a) • G.(fid) (F.(fobj) a);
  fcomp a b c f g :=
    f_equal G.(fhom) (F.(fcomp) f g) • G.(fcomp) (F.(fhom) f) (F.(fhom) g);
|}.
