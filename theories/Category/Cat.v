From Coq.Relations Require Import Relation_Definitions.
From Coq.Classes Require Import RelationClasses Morphisms.
From Coq Require Import Setoid.
From Coq Require Import ssreflect.

Set Primitive Projections.
Set Universe Polymorphism.

Section Category.
  Reserved Notation "A ~> B" (at level 60).
  Reserved Notation "f ∼ g" (at level 65).
  Reserved Notation "f ∙ g" (at level 55).
  Reserved Notation "f × g" (at level 52).

  Record Category : Type := mkCat {
    Obj :> Type;
    Hom : Obj -> Obj -> Type
    where "A ~> B" := (Hom A B);
    Id : forall A, A ~> A;
    sim : forall {A B}, (A ~> B) -> (A ~> B) -> Prop
    where "f ∼ g" := (sim f g);
    sim_equiv : forall {A B}, Equivalence (@sim A B);
    composite : forall {A B C}, (A ~> B) -> (B ~> C) -> A ~> C
    where "g ∙ f" := (composite f g);
    composite_prop : forall {A B C}, Proper (@sim A B ==> @sim B C ==> @sim A C) composite;
    id_left : forall {A B} (f : A ~> B), Id B ∙ f ∼ f;
    id_right : forall {A B} (f : A ~> B), f ∙ Id A ∼ f;
    associativity : forall {A B C D} (f : A ~> B) (g : B ~> C) (h : C ~> D), h ∙ (g ∙ f) ∼ (h ∙ g) ∙ f
  }.

  Definition Monoid := { C : Category & { A : Obj C & forall B : Obj C, A = B } }.

  Record Monoid' := mkMonoid' {
    dom :> Type;
    Unit : dom;
    Multiplication : dom -> dom -> dom
    where "A × B" := (Multiplication A B);
    MunitL : forall x, Unit × x = x;
    MunitR : forall x, x × Unit = x;
    Massoc : forall x y z, x × (y × z) = (x × y) × z }.

  Record Equivalence A B := mkEquiv {
    f : A -> B;
    g : B -> A;
    Idfg : forall y, f (g y) = y;
    Idgf : forall x, g (f x) = x;
    Coh : forall x, Idfg (f x) = f_equal f (Idgf x)
  }.

  Lemma equiv_monoid : Equivalence Monoid Monoid'.
  Proof.
  simple refine (mkEquiv _ _ _ _ _ _ _).
  simple refine (fun m => mkMonoid' (Hom _ _ _) _ _ _ _ _).
  all: try destruct m.
  exact x.
  Abort.

  Global Existing Instance sim_equiv.
  Global Existing Instance composite_prop.
End Category.

Notation "A ~> B" := (Hom _ A B) (at level 60).
Notation "f ∼ g" := (sim _ f g) (at level 65).
Notation "f ∙ g" := (composite _ f g) (at level 55).
Arguments Id {_} _.

Section Functor.
  Context (C D : Category).

  Record Functor : Type :=
    mkFunctor
      { F :> C -> D
        ; fmap : forall {A B}, A ~> B -> F A ~> F B
        ; fmap_prop : forall {A B}, Proper (@sim C A B ==> @sim D _ _) fmap
        ; fmap_id : forall {A}, fmap (Id A) ∼ Id _
        ; fmap_composite : forall {X Y Z} (g : X ~> Y) (f: Y ~> Z),
            fmap (g ∙ f) ∼ fmap g ∙ fmap f
      }.

  Global Existing Instance fmap_prop.
End Functor.

Arguments mkFunctor {_ _} _ _ _ _ _.
Arguments fmap {_ _} _ {_ _} _.

Section FunctorComposition.
  Context {C D E : Category} (F : Functor C D) (G : Functor D E).
  Program Definition functor_composite : Functor C E :=
    mkFunctor (fun A => G (F A)) (fun A B f => fmap G (fmap F f)) _ _ _.
  Next Obligation. solve_proper. Qed.
  Next Obligation. do 2 setoid_rewrite fmap_id; reflexivity. Qed.
  Next Obligation. do 2 setoid_rewrite fmap_composite; reflexivity. Qed.
End FunctorComposition.

Notation "f ∘ g" := (functor_composite f g) (at level 55).
Reserved Notation "f × g" (at level 52).

Section NaturalIsomorphism.
  Context {C D : Category} (F G : Functor C D).

  Record NaturalIsomorphism :=
    mkNatIso
      { ni_map :> forall {A}, F A ~> G A
      ; ni_inv : forall {A}, G A ~> F A
      ; ni_natural : forall {A B} (f : A ~> B), fmap F f ∙ ni_map ∼ ni_map ∙ fmap G f
      ; ni_rightinv : forall {A}, ni_inv ∙ ni_map ∼ Id (G A)
      ; ni_leftinv : forall {A}, ni_map ∙ ni_inv ∼ Id (F A)
      }.
End NaturalIsomorphism.

Arguments ni_inv {_ _ _ _} _ _.
