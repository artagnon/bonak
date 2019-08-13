From Coq Require FunctionalExtensionality.
From Coq.Relations Require Import Relation_Definitions.
From Coq.Classes Require Import RelationClasses Morphisms.

Set Primitive Projections.
Set Universe Polymorphism.

(*********************************************************)
(**       Category (using setoids on hom-sets)          **)
(*********************************************************)

Section Category.
  Reserved Notation "f ∼ g" (at level 65).
  Reserved Notation "f ∙ g" (at level 55).

  Record Category : Type :=
    mkCategory
      { Obj : Type
        ; Hom : Obj -> Obj -> Type
        ; sim : forall {A B}, relation (Hom A B)
          where "f ∼ g" := (sim f g)
        ; sim_equiv : forall A B, Equivalence (@sim A B)
        ; Id : forall {A}, Hom A A
        ; Comp : forall {A B C}, Hom B C -> Hom A B -> Hom A C
          where "f ∙ g" := (Comp f g)
        ; Comp_proper : forall {A B C},
            Proper (@sim B C ==> @sim A B ==> @sim A C) Comp
        ; cat_law1 : forall {A B} (f : Hom A B), Id ∙ f ∼ f
        ; cat_law2 : forall {A B} (f : Hom A B), f ∙ Id ∼ f
        ; cat_law3 : forall {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D),
            h ∙ (g ∙ f) ∼ (h ∙ g) ∙ f
      }.

  Global Existing Instance sim_equiv.
  Global Existing Instance Comp_proper.
End Category.

Notation "C ⦅ A ; B ⦆" := (Hom C A B) (at level 60).
Notation "f ∙ g" := (Comp _ f g) (at level 55).
Notation "f ∼ g" := (sim _ f g) (at level 65).
Arguments Id {_} _.

(*********************************************************)
(**       Functor, identity, composition                **)
(*********************************************************)

Section Functor.
  Context (C D : Category).

  Record Functor : Type :=
    mkFunctor
      { F :> Obj C -> Obj D
        ; fmap : forall {A B}, C⦅A;B⦆ -> D⦅F A;F B⦆
        ; fmap_proper : forall {A B}, Proper (@sim C A B ==> @sim D _ _) fmap
        ; functor_law1 : forall {A}, fmap (Id A) ∼ Id _
        ; functor_law2 : forall {X Y Z: Obj C} (g : C⦅X;Y⦆) (f:C⦅Y;Z⦆),
            fmap (f ∙ g) ∼ (fmap f) ∙ (fmap g)
      }.

  Global Existing Instance fmap_proper.
End Functor.

(*********************************************************)
(** Monoids                                             **)
(*********************************************************)
Section Monoid.
  Reserved Notation "x ⋅ y" (at level 55).
  Record Monoid :=
    mkMonoid
      { monoid_carrier :> Type
      ; monoid_unit : monoid_carrier
      ; monoid_mult : monoid_carrier -> monoid_carrier -> monoid_carrier
        where "x ⋅ y" := (monoid_mult x y)
      ; monoid_law1 : forall m, monoid_unit ⋅ m = m
      ; monoid_law2 : forall m, m ⋅ monoid_unit = m
      ; monoid_law3 : forall m1 m2 m3,
          (m1 ⋅ m2) ⋅ m3 = m1 ⋅ (m2 ⋅ m3)
      }.

  Definition e := monoid_unit.
End Monoid.

Notation "x ⋅ y" := (monoid_mult x y) (at level 55).

(*********************************************************)
(** Monads, in Kleisli triple form                      **)
(*********************************************************)

Section Monad.
  Context (C: Category).
  Reserved Notation "A >>= f" (at level 65).

  Record Monad : Type :=
    mkMonad
      { monad_ty :> Type -> Type
        ; ret  : forall {A : Type}, A -> monad_ty A
        ; bind : forall {A B},
            monad_ty A -> (A -> monad_ty B) -> monad_ty B
          where "A >>= f" := (bind A f)
        ; join : forall {A},
            monad_ty (monad_ty A) -> monad_ty A
        ; monad_law1 : forall {A B} a (f : A -> monad_ty B), (ret a) >>= f = f a
        ; monad_law2 : forall {A} c, c >>= (@ret A) = c
        ; monad_law3 : forall {A B C} c (f : A -> monad_ty B) (g : B -> monad_ty C),
            c >>= f >>= g = c >>= (fun a => (f a) >>= g)
      }.
End Monad.

Notation "A >>= f" := (bind A f) (at level 65).
Notation "f >=> g" := join ∙ fmap g ∙ f (at level 65).
