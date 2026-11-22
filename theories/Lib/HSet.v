Set Warnings "-notation-overridden".
From Bonak.Lib Require Import Logic Tactics Funext SigT EqDec Equiv Univalence.

Import Logic.EqNotations.

Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Record HSet := {
  Dom:> Type;
  UIP {x y: Dom} {h g: x = y}: h = g;
}.

(** [unit] seen as an [HSet] *)

Lemma unit_UIP (x y: unit) (h g: x = y): h = g.
Proof.
  destruct g, x; now apply UIP_refl_unit.
Defined.

Lemma bool_UIP (x y: bool) (h g: x = y): h = g.
Proof.
  destruct g, x; now apply UIP_refl_bool.
Defined.

Definition hunit@{m}: HSet@{m} := {|
  Dom := unit;
  UIP := unit_UIP;
|}.

Lemma hunit_ext (x y: hunit): x = y.
Proof.
  now destruct x, y.
Defined.

Definition hbool@{m}: HSet@{m} := {|
  Dom := bool;
  UIP := bool_UIP;
|}.

(** [sigT] seen as a type constructor on [HSet] *)

Lemma sigT_eq {A: Type} {B} {x y: {a: A &T B a}}:
  (x.1; x.2) = (y.1; y.2) -> x = y.
Proof.
  now easy.
Defined.

Lemma sigT_decompose_eq {A: Type} {B} {x y: {a: A &T B a}} {p: x = y}:
  p = (= projT1_eq p; projT2_eq p).
Proof.
  now destruct p, x.
Defined.

Lemma sigT_decompose {A: Type} {B: A -> Type} {u v: {a: A &T B a}} {p q: u = v}
  {alpha: projT1_eq p = projT1_eq q}
  {beta: rew [fun r => rew [fun b: A => B b] r in u.2 = v.2] alpha in
   projT2_eq p = projT2_eq q}: p = q.
Proof.
  rewrite (sigT_decompose_eq (p := q)), (sigT_decompose_eq (p := p)).
  destruct u, v; simpl. now destruct beta, alpha.
Defined.

Lemma sigT_UIP {A: HSet} {B: A -> HSet} (x y: {a: A &T B a}) (p q: x = y):
  p = q.
Proof.
  unshelve eapply sigT_decompose. now apply A. now apply (B y.1).
Defined.

Definition hsigT {A: HSet} (B: A -> HSet): HSet := {|
  Dom := {a: A &T B a};
  UIP := sigT_UIP;
|}.

Set Warnings "-notation-overridden".

Notation "{ x & P }" := (hsigT (fun x => P%type)): type_scope.
Notation "{ x : A & P }" := (hsigT (A := A) (fun x => P%type)): type_scope.

(** [forall] defined over an [HSet] codomain *)

Lemma hpiT_decompose {A: Type} (B: A -> HSet)
  (f g: forall a: A, B a) (p: f = g):
  functional_extensionality_dep_good _ _
    (fun x => f_equal (fun H => H x) p) = p.
Proof.
  destruct p; now apply functional_extensionality_dep_good_refl.
Qed.

Definition hpiT_UIP {A: Type} (B: A -> HSet) (f g: forall a: A, B a)
  (p q: f = g): p = q.
Proof.
  rewrite <- hpiT_decompose with (p := p),
          <- hpiT_decompose with (p := q).
  f_equal.
  apply functional_extensionality_dep_good; intro a. now apply (B a).
Qed.

Definition hpiT {A: Type} (B: A -> HSet): HSet.
Proof.
  exists (forall a: A, B a). now apply hpiT_UIP.
Defined.

Notation "'hforall' x .. y , P" :=
  (hpiT (fun x => .. (hpiT (fun y => P%type)) ..))
  (at level 10, x binder, y binder, P at level 200,
  format "'[  ' '[  ' 'hforall'  x  ..  y ']' ,  '/' P ']'"): type_scope.

(** [eq] over an [HSet], as an [HSet]  *)

Definition eq_hprop_UIP {A: Type} (h: forall x y: A, x = y) {x y: A}
  (p q: x = y): p = q :=
  eq_proofs_unicity_on (fun y => inl (h x y)) p q.

Definition hEq {A: HSet} (x y: A): HSet := {|
  Dom := x = y;
  UIP := fun p q α β => eq_hprop_UIP (fun p q => A.(UIP)) α β;
|}.

(** Retracts of h-sets. *)

Lemma retract_eq {A B: Type} (f: A -> B) (g: B -> A)
  (H: forall x, g (f x) = x) {x y: A} (p: x = y):
  p = eq_trans (eq_sym (H x)) (eq_trans (f_equal g (f_equal f p)) (H y)).
Proof.
  destruct p; simpl. destruct (H x). reflexivity.
Defined.

Lemma retract_UIP {A: Type} {B: HSet} (f: A -> B) (g: B -> A)
  (H: forall x, g (f x) = x) (x y: A) (p q: x = y): p = q.
Proof.
  rewrite (retract_eq f g H p).
  rewrite (retract_eq f g H q).
  now rewrite (@UIP B (f x) (f y) (f_equal f p) (f_equal f q)).
Defined.

(** The empty type, products and sums. *)

Unset Universe Minimization ToSet.

Definition hEmpty: HSet := {|
  Dom := Empty_set;
  UIP x y h g := match x with end;
|}.

Lemma prodUIP {X Y: HSet} (x y: X * Y) (h g: x = y): h = g.
Proof.
  unshelve eapply (retract_UIP (B := hsigT (A := X) (fun _ => Y))).
  - intro s. now exact (fst s; snd s).
  - intro s. now exact (s.1, s.2).
  - now intros [a b].
Defined.

Lemma sumUIP {X Y: HSet} (x y: X + Y) (h g: x = y): h = g.
Proof.
  unshelve eapply (retract_UIP
    (B := hsigT (A := hbool) (fun b: hbool => if b then X else Y))).
  - intros [a|b]. now exact (true; a). now exact (false; b).
  - intro s. now exact (match s.1 as b return (if b then X else Y) -> X + Y
                        with true => fun a => inl a | false => fun b => inr b
                        end s.2).
  - now intros [a|b].
Defined.

Definition prodSet (X Y: HSet): HSet :=
  {| Dom := X * Y; UIP := prodUIP |}.


(** All path types in HSets are propositions, so an equivalence between
    them needs only the two maps *)

Definition pathEquiv {A: HSet} {x y x' y': A}
  (f: x = y -> x' = y') (g: x' = y' -> x = y):
  Equiv (x = y) (x' = y') :=
  qinvEquiv f g (fun p => A.(UIP)) (fun q => A.(UIP)).

Definition pathEquiv2 {A B: HSet} {x y: A} {x' y': B}
  (f: x = y -> x' = y') (g: x' = y' -> x = y):
  Equiv (x = y) (x' = y') :=
  qinvEquiv f g (fun p => A.(UIP)) (fun q => B.(UIP)).

(** The based-pair space over a fixed point of an HSet contracts onto the
    fibre *)

Definition baseContract {FrB: HSet} (E: FrB -> HSet) (D: FrB):
  Equiv {t: {D0: FrB &T E D0} &T D = t.1} (E D).
Proof.
  unshelve refine (qinvEquiv
    (fun x => rew [fun D0 => E D0] (eq_sym x.2) in x.1.2)
    (fun c => ((D; c); eq_refl)) _ _).
  - intros ((D0, c0), e). cbn in e. now destruct e.
  - intros c. now reflexivity.
Defined.

(** The contraction of a candidate total space: pairs of a point [D] of an
    HSet with a cell whose canonical image is identified with [D] project
    equivalently onto the cells (the fibres are singletons; [UIP] of the
    HSet collapses the identification component). *)

Lemma fillerContract {A B: HSet} (F: A -> B)
  (x: {D: B &T {d': A &T D = F d'}}):
  ((F x.2.1; (x.2.1; eq_refl)): {D: B &T {d': A &T D = F d'}}) = x.
Proof.
  destruct x as (D, (d', e)). cbn.
  refine (eq_existT_curried (eq_sym e) _).
  etransitivity.
  { now exact (rew_sigT_fst_const (eq_sym e) d' eq_refl). }
  now exact (f_equal (fun h => (d'; h)) (B.(UIP))).
Qed.

Definition fillerEquiv {A B: HSet} (F: A -> B):
  Equiv {D: B &T {d': A &T D = F d'}} A :=
  qinvEquiv (fun x => x.2.1) (fun a => (F a; (a; eq_refl)))
    (fillerContract F) (fun a => eq_refl).

(** Equality of HSets from equivalence of their carriers.

    From univalence, [hsetEq] turns an equivalence of the carriers of two HSets
    into an equality of the HSets: the [Dom] path comes from univalence, and the
    [UIP] field is proof-irrelevant ([eq_hprop_UIP]); functional
    extensionality proves equality of the transported fields. *)

Definition hsetEqIntro (h1 h2: HSet) (p: h1.(Dom) = h2.(Dom)): h1 = h2.
Proof.
  destruct h1 as [d1 u1], h2 as [d2 u2]; cbn in p; destruct p.
  apply (f_equal (fun u => {| Dom := d1; UIP := u |})).
  apply functional_extensionality_dep_good; intro x.
  apply functional_extensionality_dep_good; intro y.
  apply functional_extensionality_dep_good; intro a.
  apply functional_extensionality_dep_good; intro b.
  now apply (eq_hprop_UIP (u1 x y)).
Defined.

Definition hsetEq {h1 h2: HSet} (e: Equiv h1 h2): h1 = h2 :=
  hsetEqIntro h1 h2 (ua e).

Lemma hsetEqIntroRew (h1 h2: HSet) (p: h1.(Dom) = h2.(Dom)) (x: h1):
  rew [Dom] (hsetEqIntro h1 h2 p) in x = rew [fun T: Type => T] p in x.
Proof.
  destruct h1 as [d1 u1], h2 as [d2 u2]; cbn in p; destruct p; cbn.
  rewrite <- (rew_map Dom (fun u => {| Dom := d1; UIP := u |})).
  now apply rew_const.
Qed.

Lemma hsetEqRew {h1 h2: HSet} (e: Equiv h1 h2) (x: h1):
  rew [Dom] (hsetEq e) in x = e x.
Proof.
  unfold hsetEq. rewrite hsetEqIntroRew. now apply uaRew.
Qed.

Lemma hsetEqRewSym {h1 h2: HSet} (e: Equiv h1 h2) (x: h2):
  rew [Dom] (eq_sym (hsetEq e)) in x = invEq e x.
Proof.
  apply (eqvInj e).
  now exact (eq_sym (hsetEqRew e _)
    • (rew_sym_cancel_r (P := Dom) (hsetEq e) x • eq_sym (secEq e x))).
Qed.
