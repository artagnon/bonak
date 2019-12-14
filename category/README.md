# Formalization of n-categories in Coq

## Notation
```coq
Notation "A ~> B" := (Hom _ A B) (at level 60).
Notation "f ∼ g" := (sim _ f g) (at level 65).
Notation "f ∙ g" := (composite _ f g) (at level 55).
Notation "f ∘ g" := (functor_composite f g) (at level 55).
```
