(* n-categories:
   ≈ : Equality, up to weak homotopy equivalence
   ~> : Morphism always takes ∞-categories as objects
   ∘ : Composition of ∞-categories
 *)

Set Universe Polymorphism.

Notation "( a ; b )" := (existT _ a b) (at level 0).
Notation "'dfst' a" := (projT1 a) (at level 10).
Notation "'dsnd' a" := (projT2 a) (at level 10).

Record NCat :=
mkNCat {
  Arity : Type;
  Sign : Arity -> Type
}.

Fixpoint CatOp n : NCat :=
  match n with
  | O => {| Arity := unit ; Sign := (fun _ => unit) |}
  | S n' => {| Arity := { A: (CatOp n').(Arity) &
                            (CatOp n').(Sign) A -> Type };
              Sign := (fun '(A ; M) =>
                         { s: (CatOp n').(Sign) A & (M s * M s)%type }) |}
  end.

Reserved Notation "f ∘ g" (at level 55).

Inductive Monoid isa Category 0 [rename ~> to \times] :=
  | Unit : Set -> Monoid.
  | Multiplication : forall {M : Monoid}, M x M -> M
  | Munit : forall {M : Monoid}, (Unit x M -> M) and (M x Unit -> M).

Inductive Group isa Monoid := forall A, A -> A. (* Inverse *)
Inductive AbelianGroup isa Group := forall {F G}, F + G = G + F.

Inductive Ring isa Category [1, Set] [(copy -> to +) and (copy + to *)].
Laws Ring := Madd : + isa Monoid
           | Mmult : * isa AbelianGroup
           | MDist : forall A B C, (A + B) * C = (A * C) + (B * C).

Inductive Ideal.
Inductive MaximalIdeal isa Ideal.
Inductive PrimeIdeal isa Ideal.
