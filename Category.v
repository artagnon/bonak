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

Arguments mkFunctor {_ _} _ _ _ _ _.
Arguments fmap {_ _} _ {_ _} _.

(* ref: Monads Need Not Be Endofunctors *)
Section RelativeMonad.
  Context {C D : Category} {J : Functor C D}.

  Record RelativeMonad :=
    mkRelativeMonad
      { RM :> C -> D
        ; η : forall A, J A ~> RM A
        ; relmon_bind : forall {A B}, J A ~> RM B -> RM A ~> RM B
        ; relmon_bind_proper : forall A B,
            Proper (@sim D (J A) (RM B) ==> sim D) relmon_bind
        ; relmon_law1 : forall A, relmon_bind (η A) ∼ Id _
        ; relmon_law2 : forall A B (f : J A ~> RM B),
            η A ∙ relmon_bind f ∼ f
        ; relmon_law3 : forall A B C (f : J B ~> RM C) (g: J A ~> RM B),
            relmon_bind (g ∙ relmon_bind f) ∼ relmon_bind g ∙ relmon_bind f
      }.
End RelativeMonad.

Arguments RelativeMonad {_ _} J.

Section NaturalIsomorphism.
  Context {C D : Category} (F G : Functor C D).

  Record NatIso :=
    mkNatIso
      { ni_map :> forall {A}, F A ~> G A
      ; ni_inv : forall {A}, G A ~> F A
      ; ni_natural : forall {A B} (f : A ~> B), fmap F f ∙ ni_map ∼ ni_map ∙ fmap G f
      ; ni_rightinv : forall {A}, ni_inv ∙ ni_map ∼ Id (G A)
      ; ni_leftinv : forall {A}, ni_map ∙ ni_inv ∼ Id (F A)
      }.
End NaturalIsomorphism.

Arguments ni_inv {_ _ _ _} _ _.

Section FunctorComposition.
  Context {C D E : Category} (F : Functor C D) (G : Functor D E).
  Program Definition functor_comp : Functor C E :=
    mkFunctor (fun A => G (F A)) (fun A B f => fmap G (fmap F f)) _ _ _.
  Next Obligation. cbv; intuition; do 2 apply fmap_proper => //. Qed.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
End FunctorComposition.

Section RelativeMonadMorphism.
  Context {C D1 D2 : Category} {J1 : Functor C D1} (J12 : Functor D1 D2)
          {J2 : Functor C D2} (ϕ : NatIso J2 (functor_comp J1 J12))
          (ψ := ni_inv ϕ) (M1 : RelativeMonad J1) (M2: RelativeMonad J2).

  Notation rbind := relmon_bind.

  Record RelativeMonadMorphism :=
    mkRelMonMorph
      { rmm_map :> forall {A}, J12 (M1 A) ~> M2 A
        ; rmm_law1 : forall A, fmap J12 (η M1 A) ∙ rmm_map ∼ ψ _ ∙ η M2 A
        ; rmm_law2 : forall A B (f : J1 A ~> M1 B),
            fmap J12 (rbind M1 f) ∙ rmm_map ∼
                    rmm_map ∙ rbind M2 (ϕ _ ∙ fmap J12 f ∙ rmm_map)
      }.
End RelativeMonadMorphism.
