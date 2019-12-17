(* n-categories:
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
Notation "'dfst' a" := (projT1 a) (at level 10).
Notation "'dsnd' a" := (projT2 a) (at level 10).

Record NCat :=
  mkNCat {
      A : Type
      ; M : A -> Type
    }.

Fixpoint ArityAndSign n : { A : Type & A -> Type }  :=
  match n with
  | O => (existT (fun A => A -> Type) unit (fun _ => unit))
  | S n' => existT (fun A => A -> Type) ({A: dfst (ArityAndSign n') &
                                         (dsnd (ArityAndSign n')) A -> Type})
                                     (fun '(A ; M) => {s: (dsnd (ArityAndSign n')) A & (M s * M s)%type})
  end.

(* Two n-functions. The first creates an n-morphism along with arity info;
   The second creates an (n - 1)-morphism along with arity info *)
with make_arity {n} (A : Arity n) (M : Mor n _) : Type := { A & M }
with arity_down {n} '(A ; M) : Type := A

(* Given the dpair version, this function creates a curried version *)
with app {n} {A : Arity n} (M : Mor n s) (s : Sign n A) : Type :=
  match n, s with
  | O, tt => Type
  | _, (A ; M') => M' -> M
  end

(* An n-Morphism is a collection of n morphisms, all the way down to tt *)
with Mor n {A : Arity n} (s : Sign n (arity_down A)) : Type :=
  match n, s with
  | O, tt => Type
  | _, (T ; M) => forall A : T, make_arity A M
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
