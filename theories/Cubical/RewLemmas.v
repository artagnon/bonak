Import Logic.EqNotations.
Require Import Aux.

Lemma rew_rew {A} {x y: A} (H : x = y) P {a: P x} :
rew <- [P] H in rew [P] H in a = a.
  now destruct H.
Qed.

Lemma rew_rew_opp {A} {x y: A} (H : x = y) P {a: P y} :
rew [P] H in rew <- [P] H in a = a.
  now destruct H.
Qed.

Lemma rew_context {A} {x y : A} (eq: x = y) {P} {a: P x}
{Q : forall a, P a -> Type} : Q y (rew eq in a) = Q x a.
  now destruct eq.
Qed.

Theorem rew_map_top A (P:A->Type) x1 x2 (H: x1 = x2) (y: P x1) :
  rew [P] H in y = rew [id] f_equal P H in y.
Proof.
  now destruct H.
Qed.

Theorem rew_map_opp_top A (P:A->Type) x1 x2 (H: x2 = x1) (y: P x1) :
  rew <- [P] H in y = rew <- [id] f_equal P H in y.
Proof.
  now destruct H.
Qed.

Lemma rew_opp_extrude A (P: A -> Type) x1 x2 (H: x2 = x1) (y: P x1) :
  rew <- [P] H in y = rew [P] (eq_sym H) in y.
Proof.
  now destruct H.
Qed.

Lemma eq_over_rew {A A'} {a: A} {a': A'} {H} (H0: a =_{H} a') : rew H in a = a'.
Proof.
  now destruct H, H0.
Qed.

Lemma rew_over: forall {T U} {t u} {H: T = U} (P: T -> Type) (Q: U -> Type)
  (H': forall x y (H'': x =_{H} y), P x = Q y), t =_{H} u -> P t -> Q u.
Proof.
  intros; now destruct H0, (H' t t).
Qed.

Lemma rew_over_rl: forall {T U t u} {H: T = U} (P: T -> Type),
  t =_{H} u -> P (rew <- H in u) -> P t.
Proof.
  intros; now destruct H, H0.
Qed.

Lemma rew_over_rl': forall {T U t u} {H: T = U} (P: U -> Type),
  t =_{H} u -> P u -> P (rew H in t).
Proof.
  intros; now destruct H0.
Qed.

Lemma rew_over_lr: forall {T U t u} {H: T = U} (P: T -> Type),
  t =_{H} u -> P t -> P (rew <- H in u).
Proof.
  intros; now destruct H, H0.
Qed.

Lemma rew_over_lr': forall {T U t u} {H: T = U} (P: U -> Type),
  t =_{H} u -> P (rew H in t) -> P u.
Proof.
  intros; now destruct H0.
Qed.

Lemma rew_pair : forall A {a} (P Q: A -> Type) (x: P a) (y: Q a)
  {b} (H: a = b), (rew H in x, rew H in y) =
                   rew [fun a => (P a * Q a)%type] H in (x, y).
Proof.
  now destruct H.
Qed.

Lemma rew_sigT {A x} {P : A -> Type} (Q : forall a, P a -> Type)
  (u : { p : P x & Q x p }) {y} (H: x = y)
    : rew [fun x => { p : P x & Q x p }] H in u
      = existT (Q y) (rew H in u.1) (rew dependent H in u.2).
Proof.
  now destruct H, u.
Qed.

Lemma rew_triple {A x} {P P': A -> Type}
  (Q: forall a, (P a * P' a)%type -> Type)
  (u: { p: (P x * P' x)%type & Q x p }) {y} (H: x = y)
    : rew [fun x => { p : (P x * P' x)%type & Q x p }] H in u
      = existT (Q y) (rew [fun x => (P x * P' x)%type] H in u.1)
        (rew dependent H in u.2).
Proof.
  now destruct H, u.
Qed.

Lemma rew_existT_curried {A x} {P : A -> Type} {Q: {a & P a} -> Type}
   {y} {H : x = y}
   {u : P x} {v : Q (x; u)}
   {u': P y} {v': Q (y; u')}
   {Hu : rew H in u = u'} {Hv : rew (=H; Hu) in v = v'}:
   rew [fun x => {a: P x & Q (x; a)}] H in (u; v) = (u'; v').
Proof.
   now destruct Hu, Hv, H.
Qed.

Theorem rew_permute A (P Q: A -> Type) (x y: A) (H: forall z, Q z = P z)
  (H': x = y) (a: P x) :
  rew <- [id] H y in rew H' in a =
  rew [Q] H' in rew <- [id] H x in a.
Proof.
  now destruct H'.
Qed.

Theorem rew_permute' A (P Q: A -> Type) (x y: A) (H: forall z, P z = Q z)
  (H': x = y) (a: P x) :
  rew [id] H y in rew H' in a =
  rew [Q] H' in rew [id] H x in a.
Proof.
  now destruct H'.
Qed.

Lemma rew_swap : forall A (P : A -> Type) a b (H: a = b) (x : P a) (y : P b),
  x = rew <- H in y <-> rew H in x = y.
Proof.
  now destruct H.
Qed.

Lemma rew_app A (P : A -> Type) (x y : A) (H H' : x = y) (a : P x) :
  H = H' -> rew <- [P] H in rew [P] H' in a = a.
Proof.
  intros * ->. now destruct H'.
Qed.

Lemma eq_ind_r_refl {A} {x y: A} {H: x = y} :
  eq_ind_r (fun x => eq x y) eq_refl H = H.
Proof.
  now destruct H.
Qed.

Lemma map_subst_app {A B} {x y} (a: A) (H: x = y :> B) (C: A -> B -> Type)
  (f: forall a, C a x):
  rew [C a] H in f a = (rew [fun x => forall a, C a x] H in f) a.
Proof.
  now destruct H.
Defined.
