# Category Theory in valis:
# \approx : Equality, up to homotopy equivalence
# ~> : Morphism always takes ∞-categories as objects
# \circ : Composition of ∞-categories

Inductive Carrier {n : Nat} : Set :=
  match n with
  | O => Carrier O                                                    (* The base case *)
  | S n => forall Carrier n, Carrier (S n)                            (* The objects of an n-Category are mapped to a Higher Category *)
  end.

Inductive Morphism {n : Nat} (a b : Carrier n) [~>] : Set :=
  match n with
  | O => a -> b -> (a ~> b)
  | S n => forall (Carrier n ~> Carrier n), (a ~> b)                 (* The morphisms of the n-Category are also mapped *)
  end.

(* Definition of an n-Category *)
Inductive Category {n : Nat} :=
  | Obj : Carrier n
  | ~> : Obj ~> Obj
  | Id : forall A : Obj, A ~> A                                       (* Identity morphism *)
  | . : forall (A B C : Obj), (B ~> C) ~> (A ~> B) ~> (A ~> C).       (* Composition *)
  | Assoc : forall (A B C : Obj) (f : C ~> A) (g : B ~> C) (h : A ~> B), (f . g) . h = f . (g . h)
  | IdLaw : forall A B (f : A ~> B), (Id B . f = f) and (f . Id A = f).

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