(** The interpretation of dependent streams as a coinductive type in Coq *)

Section DepStream.

Context {A} (B: A -> Type) (f: forall a, B a -> A).

CoInductive DepStream (a: A): Type :=
  { this : B a ; next : DepStream (f a this) }.

Check this: forall a, DepStream a -> B a.
Check next: forall a (x: DepStream a), DepStream (f a x.(this a)).

Context (D: A -> Type) (v: forall a, D a -> B a)
        (s: forall a d, D (f a (v a d))).

CoFixpoint make a (d: D a) : DepStream a :=
  {| this := v a d; next := make (f a (v a d)) (s a d) |}.

Check fun a d => eq_refl: (make a d).(this a) = v a d.
Check fun a d => eq_refl: (make a d).(next a) =
  make (f a (make a d).(this a)) (s a d).

End DepStream.

(** Over propositions, we can also give a second-order interpretation *)

Section DepStreamProp.

Context {A: Prop} (B: A->Prop) (f: forall a, B a -> A).

Definition DepStreamProp (a: A): Prop :=
  exists D: A -> Prop, (D a /\ exists (v: forall a, D a -> B a),
    (forall a d, D (f a (v a d)))).

Definition this_prop a (x: DepStreamProp a): B a :=
  let '(ex_intro _ D (conj d (ex_intro _ v s))) := x in v a d.

Definition next_prop a (x: DepStreamProp a):
  DepStreamProp (f a (this_prop a x)) :=
  let '(ex_intro _ D (conj d (ex_intro _ v s))) := x in
  ex_intro _ D (conj (s a d) (ex_intro _ v s)).

Context (D: A -> Prop) (v: forall a, D a -> B a)
  (s: forall a d, D (f a (v a d))).

Definition make_prop a (d: D a): DepStreamProp a :=
  ex_intro _ D (conj d (ex_intro _ v s)).

Check fun a d => eq_refl: this_prop a (make_prop a d) = v a d.
Check fun a d => eq_refl: next_prop a (make_prop a d) =
  make_prop (f a (this_prop a (make_prop a d))) (s a d).

End DepStreamProp.
