Require Import Notation.

(** An inductive definition of le *)
Reserved Infix "<~" (at level 70).
Inductive leI : nat -> nat -> Type :=
| leI_refl n : n <~ n
| leI_down {n p} : p.+1 <~ n -> p <~ n
where "n <~ m" := (leI n m) : nat_scope.

Lemma leI_up {n p : nat} : n <~ p -> n <~ p.+1.
  induction 1. constructor. now constructor. now constructor.
Defined.

Lemma leI_0 {p}: O <~ p.
  induction p. now constructor. now apply leI_up.
Defined.

Lemma leI_lower_both {n p}: p.+1 <~ n.+1 -> p <~ n.
  induction 1 using leI_rec with (P := fun p n _ => pred p <~ pred n).
  now constructor. destruct p0. now apply leI_0. now constructor.
Defined.

Lemma leI_raise_both {n p}: p <~ n -> p.+1 <~ n.+1.
  induction 1. now constructor. now constructor.
Defined.
