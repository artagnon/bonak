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

Reserved Notation "f ∘ g" (at level 55).

Reserved Notation "f × g" (at level 52).

Definition Monoid := { C : Category 1 | exists A : Ob C, forall B : Ob C, A = B }.

Record Monoid' :=
  { dom : Type;
    Unit : dom; }
    Multiplication : dom -> dom -> dom
    where "A × B" := (Multiplication A B);
    MunitL : forall x, Multiplication Unit × x = x;
    MunitR : forall x, Multiplication x × Unit = x;
    Massoc : forall x y z, x × (y × z) = (x × y) × z }.

Record Equivalence A B := {
   f : A -> B;
   g : B -> A;
   Idgf : forall x, g (f x) = x;
   Idfg : forall y, f (g y) = y;
   Coh : forall x, Idfg (f x) = f_equal f (Idgf x)
}

Lemma : Equivalence Monoid Monoid'.
Proof.


Inductive Monoid isa Category 1 [rename ~> to \times] :=
  { Unit : Set -> Monoid.
    Multiplication : forall {M : Monoid}, M x M -> M
    Munit : forall {M : Monoid}, (Unit x M -> M) and (M x Unit -> M).

Inductive Group isa Monoid := forall A, A -> A. (* Inverse *)
Inductive AbelianGroup isa Group := forall {F G}, F + G = G + F.

Inductive Ring isa Category [1, Set] [(copy -> to +) and (copy + to *)].
Laws Ring := Madd : + isa Monoid
           | Mmult : * isa AbelianGroup
           | MDist : forall A B C, (A + B) * C = (A * C) + (B * C).

Inductive Ideal.
Inductive MaximalIdeal isa Ideal.
Inductive PrimeIdeal isa Ideal.
