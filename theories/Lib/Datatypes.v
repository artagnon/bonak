From Corelib.Init Require Export Notations Ltac.

Set Implicit Arguments.

#[export] Unset Cumulativity Weak Constraints.

Create HintDb core.
#[global] Hint Variables Opaque: core.
#[global] Hint Constants Opaque: core.

Inductive Empty_set: Set :=.

Register Empty_set as core.Empty_set.type.
Register Empty_set as core.False.type.

Inductive unit: Set := tt: unit.

Register unit as core.unit.type.
Register tt as core.unit.tt.
Register unit as core.True.type.
Register tt as core.True.I.

Inductive bool: Set := true: bool | false: bool.

Declare Scope bool_scope.
Delimit Scope bool_scope with bool.
Bind Scope bool_scope with bool.

Register bool as core.bool.type.
Register true as core.bool.true.
Register false as core.bool.false.

Inductive nat: Set := O: nat | S: nat -> nat.

Declare Scope nat_scope.
Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%_nat.

Register nat as num.nat.type.
Register O as num.nat.O.
Register S as num.nat.S.

Inductive sum (A B: Type): Type := inl: A -> sum A B | inr: B -> sum A B.

Notation "x + y" := (sum x y): type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

Register sum as core.sum.type.
Register inl as core.sum.inl.
Register inr as core.sum.inr.

Set Primitive Projections.
Set Printing Projections.

Polymorphic Cumulative Record sigT {A: Type} (P: A -> Type): Type :=
  existT { projT1: A; projT2: P projT1 }.

Arguments sigT {A} P.
Arguments projT1 {A P} _.
Arguments projT2 {A P} _.
Arguments existT {A} P _ _.

Register sigT as core.sigT.type.
Register existT as core.sigT.intro.
Register projT1 as core.sigT.proj1.
Register projT2 as core.sigT.proj2.

Polymorphic Definition sigT_rect (A: Type) (P: A -> Type)
  (Q: @sigT A P -> Type) (f: forall a b, Q (@existT A P a b))
  (p: @sigT A P): Q p := f (projT1 p) (projT2 p).
Register sigT_rect as core.sigT.rect.

Notation "{ x &T P }" := (sigT (fun x => P%type))
  (x at level 99, format "{ '[ ' x  &T  '/' P ']' }"): type_scope.
Notation "{ x : A &T P }" := (sigT (A := A) (fun x => P%type))
  (x at level 99, format "{ '[ ' '[' x  :  A ']'  &T  '/' P ']' }"): type_scope.
Notation "( x 'as' z 'in' T ; y 'in' P )" := (existT (fun z: T => P%type) x y)
  (at level 0, only parsing).
Notation "( x ; y )" := (existT _ x y)
  (at level 0, format "'[' ( x ;  '/ ' y ) ']'").
Notation "x .1" := (projT1 x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (projT2 x) (at level 1, left associativity, format "x .2").

Definition prod (A B: Type): Type := @sigT A (fun _ => B).
Definition pair {A B: Type} (a: A) (b: B): prod A B := existT _ a b.
Arguments pair {A B} _ _.
Notation "x * y" := (prod x y): type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z): core_scope.
Definition fst {A B: Type} (p: prod A B): A := projT1 p.
Definition snd {A B: Type} (p: prod A B): B := projT2 p.

#[global] Hint Resolve tt pair inl inr: core.

Definition id {A: Type} (x: A): A := x.
