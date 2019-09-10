From Bonak Require Import Category.
From Coq Require Import ssreflect.

Section Definitions.
  (* Specification Monads *)
  Definition W1 = RelativeMonad.
  Definition W2 = RealtiveMonad.
  Definition W_Rel = RelativeMonad.

  (* Effect Observations *)
  Definition θ1 = RelativeMonadMorphism.
  Definition θ2 = RelativeMonadMorphism.
  Definition θ_Rel = RelativeMonadMorphism.
End Definitions.

