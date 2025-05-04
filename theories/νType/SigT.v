Set Primitive Projections.
Set Printing Projections.

Record sigT {A: Type} (P: A -> Type) : Type :=
    existT { projT1: A; projT2: P projT1 }.

Arguments sigT {A}%_type P.
Arguments projT1 {A P}%_type _.
Arguments projT2 {A P}%_type _.
Arguments existT {A}%_type P _ _.

Set Warnings "-notation-overridden".

Notation "{ x & P }" := (sigT (fun x => P)) : type_scope.
Notation "{ x : A & P }" := (sigT (A := A) (fun x => P)) : type_scope.
Notation "( x 'as' z 'in' T ; y 'in' P )" := (existT (fun z : T => P) x y)
  (at level 0, only parsing).
Notation "( x ; y )" := (existT _ x y)
  (at level 0, format "'[' ( x ;  '/ ' y ) ']'").
Notation "x .1" := (projT1 x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (projT2 x) (at level 1, left associativity, format "x .2").

Import EqNotations.

Definition eq_existT_uncurried {A : Type} {P : A -> Type} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
             (pq : { p : u1 = v1 & rew p in u2 = v2 })
    : (u1; u2) = (v1; v2).
  Proof.
    destruct pq as [p q].
    destruct q; simpl in *.
    destruct p; reflexivity.
  Defined.

Definition eq_sigT_uncurried {A : Type} {P : A -> Type} (u v : { a : A & P a })
             (pq : { p : u.1 = v.1 & rew p in u.2 = v.2 })
    : u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; simpl in *.
    apply eq_existT_uncurried; exact pq.
  Defined.

Lemma eq_existT_curried {A : Type} {P : A -> Type} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
             (p : u1 = v1) (q : rew p in u2 = v2) : (u1; u2) = (v1; v2).
  Proof.
    apply eq_sigT_uncurried; exists p; exact q.
  Defined.

Notation "(= u ; v )" := (eq_existT_curried u v)
(at level 0, format "(= u ;  '/  ' v )").

Definition projT1_eq {A} {P : A -> Type} {u v : { a : A & P a }} (p : u = v)
    : u.1 = v.1
    := f_equal (fun x => x.1) p.

Definition projT2_eq {A} {P : A -> Type} {u v : { a : A & P a }} (p : u = v)
    : rew projT1_eq p in u.2 = v.2
    := rew dependent p in eq_refl.
