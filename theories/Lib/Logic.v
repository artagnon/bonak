From Bonak.Lib Require Export Datatypes.

Set Implicit Arguments.

Polymorphic Definition not (A: Type): Type := A -> Empty_set.

Notation "~ x" := (not x): type_scope.

Register not as core.not.type.

#[global] Hint Unfold not: core.

Polymorphic Definition iff (A B: Type): Type := (A -> B) * (B -> A).

Notation "A <-> B" := (iff A B): type_scope.

(** * Equality *)

Unset Elimination Schemes.

Polymorphic Cumulative Inductive eq@{u} (A: Type@{u}) (x: A): A -> Type@{u} :=
  eq_refl: x = x :> A

where "x = y :> A" := (@eq A x y): type_scope.

Set Elimination Schemes.

Arguments eq {A} x _.
Arguments eq_refl {A x} , [A] x.

Notation "x = y" := (eq x y): type_scope.
Notation "x <> y :> T" := (~ x = y :> T): type_scope.
Notation "x <> y" := (~ (x = y)): type_scope.

#[global] Hint Resolve eq_refl: core.

Definition eq_rect (A: Type) (x: A) (P: A -> Type) (f: P x) (y: A)
  (e: x = y): P y :=
  match e in _ = a return P a with eq_refl => f end.

Definition eq_sind (A: Type) (x: A) (P: A -> SProp) (f: P x) (y: A)
  (e: x = y): P y :=
  match e in _ = a return P a with eq_refl => f end.

Definition eq_rect_dep (A: Type) (x: A) (P: forall a, x = a -> Type)
  (f: P x eq_refl) (y: A) (e: x = y): P y e :=
  match e as e0 in _ = a return P a e0 with eq_refl => f end.

Definition eq_sind_dep (A: Type) (x: A) (P: forall a, x = a -> SProp)
  (f: P x eq_refl) (y: A) (e: x = y): P y e :=
  match e as e0 in _ = a return P a e0 with eq_refl => f end.

Definition eq_ind := eq_rect.
Definition eq_rec := eq_rect.

Arguments eq_rect [A] x P _ y _.
Arguments eq_ind [A] x P _ y _.
Arguments eq_rec [A] x P _ y _.
Arguments eq_sind [A x] P _ [y] _.
Arguments eq_rect_dep [A x] P _ [y] e.
Arguments eq_sind_dep [A x] P _ [y] e.

Register Scheme eq_rect as rect_nodep for eq.
Register Scheme eq_rect as rec_nodep for eq.
Register Scheme eq_rect as ind_nodep for eq.
Register Scheme eq_sind as sind_nodep for eq.
Register Scheme eq_rect_dep as rect_dep for eq.
Register Scheme eq_rect_dep as rec_dep for eq.
Register Scheme eq_rect_dep as ind_dep for eq.
Register Scheme eq_sind_dep as sind_dep for eq.

Register eq as core.eq.type.
Register eq_refl as core.eq.refl.
Register eq_ind as core.eq.ind.
Register eq_sind as core.eq.sind.
Register eq_rect as core.eq.rect.
Register eq_rec as core.eq.rec.

Section equality.
  Variables A B: Type.
  Variable f: A -> B.
  Variables x y z: A.

  Definition eq_sym (H: x = y): y = x :=
    match H in _ = a return a = x with eq_refl => eq_refl end.

  Definition eq_trans (H: x = y) (H0: y = z): x = z :=
    match H0 in _ = a return x = a with eq_refl => H end.

  Definition f_equal (H: x = y): f x = f y :=
    match H in _ = a return f x = f a with eq_refl => eq_refl end.

End equality.

Register eq_sym as core.eq.sym.
Register eq_trans as core.eq.trans.
Register f_equal as core.eq.congr.

Definition eq_sind_r (A: Type) (x: A) (P: A -> SProp) (H: P x) (y: A)
  (H0: y = x): P y :=
  eq_sind (fun y0 => P y0) H (eq_sym H0).

Definition eq_rect_r (A: Type) (x: A) (P: A -> Type) (H: P x) (y: A)
  (H0: y = x): P y :=
  eq_rect x (fun y0 => P y0) H y (eq_sym H0).

Definition eq_ind_r := eq_rect_r.
Definition eq_rec_r := eq_rect_r.

Arguments eq_ind_r [A x] P _ [y] _.
Arguments eq_rec_r [A x] P _ [y] _.

Register eq_ind_r as core.eq.ind_r.
Register eq_sind_r as core.eq.sind_r.
Register eq_rect_r as core.eq.rect_r.
Register eq_rec_r as core.eq.rec_r.

Register eq as core.identity.type.
Register eq_refl as core.identity.refl.
Register eq_ind as core.identity.ind.
Register eq_sym as core.identity.sym.
Register eq_trans as core.identity.trans.
Register f_equal as core.identity.congr.

#[global] Hint Immediate eq_sym: core.

Definition eq_sym_involutive (A: Type) (x y: A) (H: x = y):
  eq_sym (eq_sym H) = H :=
  match H as H0 in _ = a return eq_sym (eq_sym H0) = H0 with
  | eq_refl => eq_refl
  end.

Definition eq_rew (A: Type) (x: A) (P: A -> Type) (f: P x) (y: A)
  (e: x = y): P y :=
  match e in _ = a return P a with eq_refl => f end.

Definition eq_rew_r (A: Type) (x y: A) (P: A -> Type) (HC: P y) (H: x = y):
  P x :=
  match H in _ = a return P a -> P x with eq_refl => fun HC0 => HC0 end HC.

Definition eq_rew_dep (A: Type) (x: A) (P: forall a, x = a -> Type)
  (f: P x eq_refl) (y: A) (e: x = y): P y e :=
  match e as e0 in _ = a return P a e0 with eq_refl => f end.

Definition eq_rew_r_dep (A: Type) (x y: A) (P: forall a, a = y -> Type)
  (HC: P y eq_refl) (H: x = y): P x H :=
  match eq_sym_involutive H in _ = H0 return P x H0 with
  | eq_refl =>
    match eq_sym H as H0 in _ = a return P a (eq_sym H0) with
    | eq_refl => HC
    end
  end.

Definition eq_rew_fwd_dep (A: Type) (x y: A) (H: x = y)
  (P: forall a, x = a -> Type) (HC: P y H): P x eq_refl :=
  match H as H0 in _ = a return P a H0 -> P x eq_refl with
  | eq_refl => fun HC0 => HC0
  end HC.

Definition eq_rew_fwd_r_dep (A: Type) (x y: A) (H: x = y):
  forall P: forall a, a = y -> Type, P x H -> P y eq_refl :=
  match H as H0 in _ = a
    return forall P: forall b, b = a -> Type, P x H0 -> P a eq_refl with
  | eq_refl => fun P HC => HC
  end.

Arguments eq_rew [A x] P _ [y] _.
Arguments eq_rew_dep [A x] P _ [y] e.

Register Scheme eq_sym as sym for eq.
Register Scheme eq_sym_involutive as sym_involutive for eq.
Register Scheme eq_rew as rew for eq.
Register Scheme eq_rew_r as rew_r for eq.
Register Scheme eq_rew_dep as rew_dep for eq.
Register Scheme eq_rew_r_dep as rew_r_dep for eq.
Register Scheme eq_rew_fwd_dep as rew_fwd_dep for eq.
Register Scheme eq_rew_fwd_r_dep as rew_fwd_r_dep for eq.

Module EqNotations.
  Notation "'rew' H 'in' H'" := (eq_rect _ _ H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  H  in  '/' H' ']'").
  Notation "'rew' [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' <- H 'in' H'" := (eq_rect_r _ H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  H  in  '/' H' ']'").
  Notation "'rew' <- [ P ] H 'in' H'" := (eq_rect_r P H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' -> H 'in' H'" := (eq_rect _ _ H' _ H)
    (at level 10, H' at level 10, only parsing).
  Notation "'rew' -> [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10, only parsing).

  Notation "'rew' 'dependent' H 'in' H'" :=
    (match H with
     | eq_refl => H'
     end)
    (at level 10, H' at level 10,
     format "'[' 'rew'  'dependent'  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> H 'in' H'" :=
    (match H with
     | eq_refl => H'
     end)
    (at level 10, H' at level 10, only parsing).
  Notation "'rew' 'dependent' <- H 'in' H'" :=
    (match eq_sym H with
     | eq_refl => H'
     end)
    (at level 10, H' at level 10,
     format "'[' 'rew'  'dependent'  <-  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' [ 'fun' y p => P ] H 'in' H'" :=
    (match H as p in (_ = y) return P with
     | eq_refl => H'
     end)
    (at level 10, H' at level 10, y name, p name,
     format "'[' 'rew'  'dependent'  [ 'fun'  y  p  =>  P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' [ P ] H 'in' H'" :=
    (match H as p in (_ = y) return P y p with
     | eq_refl => H'
     end)
    (at level 10, H' at level 10,
     format "'[' 'rew'  'dependent'  [ P ]  '/    ' H  in  '/' H' ']'").
End EqNotations.

Export EqNotations.

Infix "•" := eq_trans (at level 65, left associativity).

Definition f_equal_dep (A: Type) (B: A -> Type) (f: forall x, B x) (x y: A)
  (H: x = y): rew H in f x = f y :=
  match H as e in _ = a return rew e in f x = f a with eq_refl => eq_refl end.

Lemma rew_opp_r A (P: A -> Type) (x y: A) (H: x = y) (a: P y):
  rew H in rew <- H in a = a.
Proof.
  destruct H. reflexivity.
Defined.

Lemma rew_opp_l A (P: A -> Type) (x y: A) (H: x = y) (a: P x):
  rew <- H in rew H in a = a.
Proof.
  destruct H. reflexivity.
Defined.

Lemma f_equal_compose A B C (a b: A) (f: A -> B) (g: B -> C) (e: a = b):
  f_equal g (f_equal f e) = f_equal (fun a => g (f a)) e.
Proof.
  destruct e. reflexivity.
Defined.

Lemma eq_trans_refl_l A (x y: A) (e: x = y): eq_trans eq_refl e = e.
Proof.
  destruct e. reflexivity.
Defined.

Lemma eq_trans_refl_r A (x y: A) (e: x = y): eq_trans e eq_refl = e.
Proof.
  destruct e. reflexivity.
Defined.

Lemma eq_trans_sym_inv_l A (x y: A) (e: x = y):
  eq_trans (eq_sym e) e = eq_refl.
Proof.
  destruct e. reflexivity.
Defined.

Lemma eq_trans_sym_inv_r A (x y: A) (e: x = y):
  eq_trans e (eq_sym e) = eq_refl.
Proof.
  destruct e. reflexivity.
Defined.

Lemma eq_trans_assoc A (x y z t: A) (e: x = y) (e': y = z) (e'': z = t):
  eq_trans e (eq_trans e' e'') = eq_trans (eq_trans e e') e''.
Proof.
  destruct e''. reflexivity.
Defined.

Lemma rew_map A B (P: B -> Type) (f: A -> B) x1 x2 (H: x1 = x2)
  (y: P (f x1)):
  rew [fun x => P (f x)] H in y = rew f_equal f H in y.
Proof.
  destruct H. reflexivity.
Defined.

Lemma map_subst {A} {P Q: A -> Type} (f: forall x, P x -> Q x) {x y}
  (H: x = y) (z: P x):
  rew H in f x z = f y (rew H in z).
Proof.
  destruct H. reflexivity.
Defined.

Lemma rew_compose A (P: A -> Type) x1 x2 x3 (H1: x1 = x2) (H2: x2 = x3)
  (y: P x1):
  rew H2 in rew H1 in y = rew (eq_trans H1 H2) in y.
Proof.
  destruct H2. reflexivity.
Defined.

Lemma eq_id_comm_l A (f: A -> A) (Hf: forall a, a = f a) a:
  f_equal f (Hf a) = Hf (f a).
Proof.
  unfold f_equal.
  rewrite <- (eq_trans_sym_inv_l (Hf a)).
  destruct (Hf a) at 1 2.
  destruct (Hf a).
  reflexivity.
Defined.

Lemma eq_id_comm_r A (f: A -> A) (Hf: forall a, f a = a) a:
  f_equal f (Hf a) = Hf (f a).
Proof.
  unfold f_equal.
  rewrite <- (eq_trans_sym_inv_l (Hf (f (f a)))).
  set (Hfsymf := fun a => eq_sym (Hf a)).
  change (eq_sym (Hf (f (f a)))) with (Hfsymf (f (f a))).
  pattern (Hfsymf (f (f a))).
  destruct (eq_id_comm_l f Hfsymf (f a)).
  destruct (eq_id_comm_l f Hfsymf a).
  unfold Hfsymf.
  destruct (Hf a). simpl.
  rewrite eq_trans_refl_l.
  reflexivity.
Defined.

Lemma eq_trans_map_distr A B x y z (f: A -> B) (e: x = y) (e': y = z):
  f_equal f (eq_trans e e') = eq_trans (f_equal f e) (f_equal f e').
Proof.
  destruct e'. reflexivity.
Defined.

Lemma eq_sym_map_distr A B (x y: A) (f: A -> B) (e: x = y):
  eq_sym (f_equal f e) = f_equal f (eq_sym e).
Proof.
  destruct e. reflexivity.
Defined.

Lemma eq_trans_sym_distr A (x y z: A) (e: x = y) (e': y = z):
  eq_sym (eq_trans e e') = eq_trans (eq_sym e') (eq_sym e).
Proof.
  destruct e, e'. reflexivity.
Defined.

Lemma rew_const A P (x y: A) (e: x = y) (k: P):
  rew [fun _ => P] e in k = k.
Proof.
  destruct e. reflexivity.
Qed.

(** Transport along a pointwise equality commutes with transport in the
    indexing type, for any family [El] over the common codomain. *)
Lemma rew_permute_ll {S: Type} (El: S -> Type)
  (A: Type) (P Q: A -> S) (x y: A)
  (H: forall z: A, P z = Q z) (H': x = y) (a: El (P x)):
  rew [El] H y in rew [fun z => El (P z)] H' in a =
  rew [fun z => El (Q z)] H' in rew [El] H x in a.
Proof.
  destruct H'; reflexivity.
Defined.

(** Transport along [p • (h • eq_sym q)] is equivalent to transporting
    both endpoints along [p] and [q] before comparing them over [h]. *)
Lemma rew_conjugate {A: Type} (P: A -> Type)
  {x x' y y': A} (p: x = x') (h: x' = y') (q: y = y')
  (u: P x) (v: P y):
  rew [P] (p • (h • eq_sym q)) in u = v ->
  rew [P] h in rew [P] p in u = rew [P] q in v.
Proof.
  intro H; rewrite <- 2 rew_compose in H.
  refine (eq_sym (rew_opp_r P q _) • _).
  exact (f_equal (fun v => rew [P] q in v) H).
Defined.

Lemma rew_swap: forall A (P: A -> Type) a b (H: a = b) (x: P a) (y: P b),
  x = rew <- H in y <-> rew H in x = y.
Proof.
  destruct H; split; intro e; exact e.
Defined.

Lemma rew_app_rl A (P: A -> Type) (x y: A) (H H': x = y) (a: P x):
  H = H' -> rew <- [P] H in rew [P] H' in a = a.
Proof.
  intros * ->. destruct H'; reflexivity.
Defined.

Lemma map_subst_app {A B} {x y} {θ: A} (H: x = y :> B) (P: A -> B -> Type)
  (f: forall θ, P θ x):
  rew [P θ] H in f θ = (rew [fun x => forall θ, P θ x] H in f) θ.
Proof.
  destruct H; reflexivity.
Defined.

Lemma f_equal_id {A} {x y: A} (e: x = y): f_equal (fun x => x) e = e.
Proof.
  destruct e; reflexivity.
Defined.

Lemma eq_trans_sym_cancel_l {A: Type} {x y z: A} (e: x = y) (h: y = z):
  eq_sym e • (e • h) = h.
Proof.
  destruct e, h; reflexivity.
Defined.

Lemma eq_trans_shift_l {A} {x y z: A} (p: x = y) (q: y = z) (r: x = z):
  p • q = r -> q = eq_sym p • r.
Proof.
  destruct p, q. intro H. destruct H; reflexivity.
Qed.

(** Cancelling a common prefix under an inversion *)
Lemma eq_trans_sym_cancel_common {A: Type} {x y z w: A} (a: x = y) (o: y = z)
  (p: y = w):
  eq_sym (a • o) • (a • p) = eq_sym o • p.
Proof.
  destruct a, o, p; reflexivity.
Qed.

(** Conjugating by a composite is conjugating twice: writing [c u v r] for
    [eq_sym u • (r • v)], this states [c aA aB P • sB = sA • c (aA • sA)
    (aB • sB) P], the form in which the two halves are met. *)
Lemma eq_trans_conj_comp {A: Type} {x0 x1 x2 y0 y1 y2: A}
  (aA: x0 = x1) (sA: x1 = x2) (P: x0 = y0) (aB: y0 = y1) (sB: y1 = y2):
  (eq_sym aA • (P • aB)) • sB = sA • (eq_sym (aA • sA) • (P • (aB • sB))).
Proof.
  destruct aA, sA, P, aB, sB; reflexivity.
Qed.

Lemma eq_trans_nat_id {A} {f: A -> A} (α: forall a, f a = a) {x y: A}
  (p: x = y): α x • p = f_equal f p • α y.
Proof.
  destruct p. symmetry. apply eq_trans_refl_l.
Qed.

Lemma rew_align {A: Type} {P: A -> Type} {x x' y: A}
  {e: x = y} {e': x' = y} (b: x = x') {v: P x} {v': P x'}
  (Hv: rew [P] b in v = v') (Hcoh: e = b • e'):
  rew [P] e in v = rew [P] e' in v'.
Proof.
  destruct Hv, b. rewrite Hcoh, eq_trans_refl_l. reflexivity.
Qed.

Lemma rew_sym_cancel {A: Type} {P: A -> Type} {x y: A} (e: x = y) (a: P x):
  rew [P] (eq_sym e) in rew [P] e in a = a.
Proof.
  exact (rew_opp_l P e a).
Qed.

Lemma rew_sym_cancel_r {A: Type} {P: A -> Type} {x y: A} (e: x = y)
  (b: P y): rew [P] e in rew [P] (eq_sym e) in b = b.
Proof.
  exact (rew_opp_r P e b).
Qed.

Lemma eq_sym_f_equal {A B: Type} (f: A -> B) {x y: A} (e: x = y):
  eq_sym (f_equal f e) = f_equal f (eq_sym e).
Proof.
  exact (eq_sym_map_distr _ _).
Qed.

(** Transport in a family of path types between two maps: the
    transported path is the conjugate by the images of the base path. *)
Lemma rew_between {T U: Type} (f g: T -> U) {x y: T} (e: x = y)
  (q: f x = g x):
  rew [fun a => f a = g a] e in q =
  eq_sym (f_equal f e) • (q • f_equal g e).
Proof.
  destruct e; cbn. rewrite eq_trans_refl_l. reflexivity.
Qed.

(** The case of [rew_between] where the right map is constant, so only the
    left image contributes. *)
Lemma rew_between_const_r {T U: Type} (f: T -> U) {x y: T} (e: x = y) {u: U}
  (q: f x = u):
  rew [fun a => f a = u] e in q = eq_sym (f_equal f e) • q.
Proof.
  destruct e; cbn. rewrite eq_trans_refl_l. reflexivity.
Qed.
