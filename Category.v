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
          where "g ∙ f" := (composite f g)
        ; composite_prop : forall {A B C},
            Proper (@sim A B ==> @sim B C ==> @sim A C) composite
        ; id_left : forall {A B} (f : A ~> B), Id B ∙ f ∼ f
        ; id_right : forall {A B} (f : A ~> B), f ∙ Id A ∼ f
        ; associativity : forall {A B C D} (f : A ~> B) (g : B ~> C) (h : C ~> D),
            h ∙ (g ∙ f) ∼ (h ∙ g) ∙ f
      }.
End Category.

Notation "A ~> B" := (Hom _ A B) (at level 60).
Notation "f ∼ g" := (sim _ f g) (at level 65).
Notation "f ∙ g" := (composite _ f g) (at level 55).
Arguments Id {_} _.

(* TODO? Bifunctor needed to define monoidal categories *)
Section Monoid.
  Reserved Notation "x × y" (at level 55).

  Record Monoid :=
    mkMonoid
      { monoid_carrier :> Type
        ; monoid_unit : monoid_carrier
        ; monoid_mult : monoid_carrier -> monoid_carrier -> monoid_carrier
          where "x × y" := (monoid_mult x y)
        ; monoid_law1 : forall m, monoid_unit × m = m
        ; monoid_law2 : forall m, m × monoid_unit = m
        ; monoid_law3 : forall m1 m2 m3, (m1 × m2) × m3 = m1 × (m2 × m3)
      }.
End Monoid.

Notation "x × y" := (monoid_mult x y) (at level 55).

Section Functor.
  Context (C D : Category).

  Record Functor : Type :=
    mkFunctor
      { F :> C -> D
        ; fmap : forall {A B}, A ~> B -> F A ~> F B
        ; fmap_proper : forall {A B}, Proper (@sim C A B ==> @sim D _ _) fmap
        ; fmap_id : forall {A}, fmap (Id A) ∼ Id _
        ; fmap_composition : forall {X Y Z} (g : X ~> Y) (f: Y ~> Z),
            fmap (g ∙ f) ∼ fmap g ∙ fmap f
      }.
End Functor.

(* TODO *)
Section NaturalTransformation.
  Context {C D : Category} {FObj1 FObj2 : C -> D} {S T : Functor C D}.

  Record NaturalTransformation : Type :=
    { NT: C -> D
      ; nt_component : forall {c : C}, FObj1 c ~> FObj2 c
    }.
End NaturalTransformation.

Section Monad.
  Context {C : Category} {J : Functor C C}.
  Reserved Notation "c >>= f" (at level 65).

  (* A monad over the category of Types and functions *)
  Record Monad : Type :=
    mkMonad
      { M :> Type -> Type
        ; η : forall {A}, A -> M A
        ; bind : forall {A B}, M A -> (A -> M B) -> M B
          where "c >>= f" := (bind c f)
        ; μ : forall {A}, M (M A) -> M A
        ; mon_law1 : forall {A B} a (f : A -> M B), (η a) >>= f = f a
        ; mon_law2 : forall {A} c, c >>= (@η A) = c
        ; mon_law3 : forall {A B D} c (f : A -> M B) (g : B -> M D),
            c >>= f >>= g = c >>= (fun a => (f a) >>= g)
      }.

  (* A more general monad *)
  Record CMonad :=
    mkCMonad
      { CM :> C -> C
        ; cmon_unit : forall A, J A ~> CM A
        ; cmon_bind : forall {A B}, J A ~> CM B -> CM A ~> CM B
        ; cmon_bind_proper : forall A B,
            Proper (@sim C (J A) (CM B) ==> sim C) cmon_bind
        ; cmon_law1 : forall A, cmon_bind (cmon_unit A) ∼ Id _
        ; cmon_law2 : forall A B (f : J A ~> CM B),
            cmon_unit A ∙ cmon_bind f ∼ f
        ; cmon_law3 : forall A B C (f : J B ~> CM C) (g: J A ~> CM B),
            cmon_bind (g ∙ cmon_bind f) ∼ cmon_bind g ∙ cmon_bind f
      }.
End Monad.

Notation "c >>= f" := (bind c f) (at level 65).
Notation "f >=> g" := (composite _ (composite _ μ (fmap g)) f) (at level 65).

(* ref: Monads Need Not Be Endofunctors *)
Section RelativeMonad.
  Context {C D : Category} {J : Functor C D}.

  Record RelativeMonad :=
    mkRelativeMonad
      { RM :> C -> D
        ; relmon_unit : forall A, J A ~> RM A
        ; relmon_bind : forall {A B}, J A ~> RM B -> RM A ~> RM B
        ; relmon_bind_proper : forall A B,
            Proper (@sim D (J A) (RM B) ==> sim D) relmon_bind
        ; relmon_law1 : forall A, relmon_bind (relmon_unit A) ∼ Id _
        ; relmon_law2 : forall A B (f : J A ~> RM B),
            relmon_unit A ∙ relmon_bind f ∼ f
        ; relmon_law3 : forall A B C (f : J B ~> RM C) (g: J A ~> RM B),
            relmon_bind (g ∙ relmon_bind f) ∼ relmon_bind g ∙ relmon_bind f
      }.
End RelativeMonad.
