(* Category Theory in valis:
   \approx : Equality, up to weak homotopy equivalence
   ~> : Morphism always takes ∞-categories as objects
   \bullet : Composition of ∞-categories
 *)

Set Universe Polymorphism.

Reserved Notation "a ~> b" (at level 80).

Inductive Carrier : nat -> Type :=
  | CNil : Carrier O
  | CAppend : forall {n : nat}, Type -> Carrier n -> Carrier (S n).

Inductive Morphism : forall {n : nat}, Carrier n -> Carrier n -> Type :=
  | MorphS : forall {n : nat} {A B : Carrier n} {A' B' : Carrier (S n)}, (A ~> B) -> (A' ~> B')
where "a ~> b" := (Morphism a b).

Notation "( a ; b )" := (existT _ a b) (at level 0).

Fixpoint Arity n : Type :=
  match n with
  | 0 => Type
  | S n' => { A : Arity n' & Mor n' A 0 tt }
  end

with Sign n (A:Arity n) : Type :=
  match n, S with
  | 0, tt => Type
  | S n', (A;P) => { s : Sign n' A & app n A P s }
  end

with app n (A:Arity n) (P:Mor n S 0) (s:Sign n A) : Type :=
  match n, S with
  | 0, tt => Type
  | S n', (A;P) =>
  end

with Mor n (A:Arity n) p (s:Sign p (down n p A)): Type :=
  match n, S with
  | 0, CNil => Type
  | S n', CAppend T S' => forall A:T, make_arity n' S'
  end.



Reserved Notation "f ∙ g" (at level 55).

(* Definition of an n-Category *)
Record Category {n : nat} : Type :=
  {
    Obj : Carrier n
  ; Id : Obj ~> Obj
  ; Comp : forall {A B C}, (B ~> C) -> (A ~> B) -> (A ~> C)
    where "f ∙ g" := (Comp f g)
  ; Assoc : forall {A B C} (f : C ~> A) (g : B ~> C) (h : A ~> B), (f ∙ g) ∙ h = f ∙ (g ∙ h)
  ; IdLaw : forall A B (f : A ~> B), (Id B ∙ f = f) /\ (f ∙ Id A = f)
  }.

Type Functor : Category 2.
Type NaturalTrans : Category 3.

Inductive Monoid isa Category 0 [rename ~> to \times] :=
  | Unit : Set -> Monoid.
  | Multiplication : forall {M : Monoid}, M x M -> M
  | Munit : forall {M : Monoid}, (Unit x M -> M) and (M x Unit -> M).

Inductive Group isa Monoid := forall A, A -> A. # Inverse
Inductive AbelianGroup isa Group := forall {F G}, F + G = G + F.

Inductive Ring isa Category [1, Set] [(copy -> to +) and (copy + to *)].
Laws Ring := Madd : + isa Monoid
           | Mmult : * isa AbelianGroup
           | MDist : forall A B C, (A + B) * C = (A * C) + (B * C).

Inductive Ideal.
Inductive MaximalIdeal isa Ideal.
Inductive PrimeIdeal isa Ideal.
