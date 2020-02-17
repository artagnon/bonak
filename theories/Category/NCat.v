(* n-categories:
   ≈ : Equality, up to weak homotopy equivalence
   ~> : Morphism always takes ∞-categories as objects
   ∘ : Composition of ∞-categories
 *)

Require Import HoTT.

Set Universe Polymorphism.

Record NCat :=
mkNCat {
  Arity : Type;
  Sign : Arity -> Type
}.

Fixpoint CatOp n : NCat :=
  match n with
  | O => {| Arity := Unit ; Sign := (fun _ => Unit) |}
  | S n' => {| Arity := { A: (CatOp n').(Arity) &
                            (CatOp n').(Sign) A -> Type };
              Sign := (fun '(A ; M) =>
                         { s: (CatOp n').(Sign) A & (M s * M s)%type }) |}
  end.

Inductive Monoid isa Category 1 [rename ~> to ×] :=
  { Unit : Set -> Monoid;
    Multiplication : forall {M : Monoid}, M × M -> M;
    Munit : forall {M : Monoid}, (Unit × M -> M) and (M × Unit -> M).

Inductive Group isa Monoid := forall A, A -> A. (* Inverse *)
Inductive AbelianGroup isa Group := forall {F G}, F + G = G + F.

Inductive Ring isa Category [1, Set] [(copy -> to +) and (copy + to *)].
Laws Ring := Madd : + isa Monoid
           | Mmult : * isa AbelianGroup
           | MDist : forall A B C, (A + B) * C = (A * C) + (B * C).

Inductive Ideal.
Inductive MaximalIdeal isa Ideal.
Inductive PrimeIdeal isa Ideal.
