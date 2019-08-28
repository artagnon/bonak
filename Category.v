From Coq Require FunctionalExtensionality.
From Coq.Relations Require Import Relation_Definitions.
From Coq.Classes Require Import RelationClasses Morphisms.

Set Primitive Projections.
Set Universe Polymorphism.

(*********************************************************)
(**       Category (using setoids on hom-sets)          **)
(*********************************************************)

Section Category.
  Reserved Notation "A ~> B" (at level 60).
  Reserved Notation "f ∼ g" (at level 65).
  Reserved Notation "f ∙ g" (at level 55).

  Record Category : Type :=
    mkCategory
      { Obj :> Type
        ; Hom : Obj -> Obj -> Type
          where "A ~> B" := (Hom A B)
        ; Id : forall A, A ~> A
        ; sim : forall {A B}, (A ~> B) -> (A ~> B) -> Prop
          where "f ∼ g" := (sim f g)
        ; sim_equiv : forall {A B}, Equivalence (@sim A B)
        ; composite : forall {A B C}, (A ~> B) -> (B ~> C) -> A ~> C
          where "f ∙ g" := (composite f g)
        ; composite_prop : forall {A B C},
            Proper (@sim A B ==> @sim B C ==> @sim A C) composite
        ; id_left : forall {A B} (f : A ~> B), Id A ∙ f ∼ f
        ; id_right : forall {A B} (f : A ~> B), f ∙ Id B ∼ f
        ; associativity : forall {A B C D} (f : A ~> B) (g : B ~> C) (h : C ~> D),
            f ∙ (g ∙ h) ∼ (f ∙ g) ∙ h
      }.
End Category.

Notation "A ~> B" := (Hom _ A B) (at level 60).
Notation "f ∼ g" := (sim _ f g) (at level 65).
Notation "f ∙ g" := (composite _ f g) (at level 55).
Arguments Id {_} _.

(*********************************************************)
(** Monoids                                             **)
(*********************************************************)
Section Monoid.
  Context (C: Category).
  Reserved Notation "x × y" (at level 55).

  Record Monoid :=
    mkMonoid
      { e :> C
        (* Bifunctor needed to define monoidal categories *)
      ; monoid_mult : C -> C -> C
        where "x × y" := (monoid_mult x y)
      ; monoid_law1 : forall m, e × m = m
      ; monoid_law2 : forall m, m × e = m
      ; monoid_law3 : forall m1 m2 m3,
          (m1 × m2) × m3 = m1 × (m2 × m3)
      }.
End Monoid.

Notation "x × y" := (monoid_mult x y) (at level 55).

(*********************************************************)
(**       Functor, identity, composition                **)
(*********************************************************)

Section Functor.
  Context (C D : Category).

  Record Functor : Type :=
      { F : C -> D
        ; fmap : forall {A B}, A ~> B -> F A ~> F B
        ; fmap_proper : forall {A B}, Proper (@sim C A B ==> @sim D _ _) fmap
        ; fmap_id : forall {A}, fmap (Id A) ∼ Id _
        ; fmap_composition : forall {X Y Z} (g : X ~> Y) (f: Y ~> Z),
            fmap (g ∙ f) ∼ fmap g ∙ fmap f
      }.
End Functor.

(*********************************************************)
(** Monads, in Kleisli triple form                      **)
(*********************************************************)

Section Monad.
  Reserved Notation "c >>= f" (at level 65).

  Record Monad : Type :=
    mkMonad
      { M :> Type -> Type
        ; η : forall {A}, A -> M A
        ; bind : forall {A B}, M A -> (A -> M B) -> M B
          where "c >>= f" := (bind c f)
        ; μ : forall {A}, M (M A) -> M A
        ; monad_law1 : forall {A B} a (f : A -> M B), (η a) >>= f = f a
        ; monad_law2 : forall {A} c, c >>= (@η A) = c
        ; monad_law3 : forall {A B D} c (f : A -> M B) (g : B -> M D),
            c >>= f >>= g = c >>= (fun a => (f a) >>= g)
      }.
End Monad.

Notation "c >>= f" := (bind c f) (at level 65).
Notation "f >=> g" := (composite _ (composite _ μ (fmap g)) f) (at level 65).
