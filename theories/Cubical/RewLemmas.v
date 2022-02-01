From Coq Require Import Arith.
Import Logic.EqNotations.
Require Import Aux.
Import Aux.

Module RewLemmas.
Lemma rew_rew {A} {x y: A} (H : x = y) P {a: P x} :
rew <- [P] H in rew [P] H in a = a.
  now destruct H.
Defined.

Lemma rew_rew_opp {A} {x y: A} (H : x = y) P {a: P y} :
rew [P] H in rew <- [P] H in a = a.
  now destruct H.
Defined.

Lemma rew_context {A} {x y : A} (eq: x = y) {P} {a: P x}
{Q : forall a, P a -> Type} : Q y (rew eq in a) = Q x a.
  now destruct eq.
Defined.

Theorem rew_map_top A (P:A->Type) x1 x2 (H: x1 = x2) (y: P x1) :
rew [P] H in y = rew [fun x => x] f_equal P H in y.
Proof.
  now destruct H.
Defined.

Theorem rew_map_opp_top A (P:A->Type) x1 x2 (H: x2 = x1) (y: P x1) :
rew <- [P] H in y = rew <- [fun x => x] f_equal P H in y.
Proof.
  now destruct H.
Defined.

Lemma rew_opp_extrude A (P: A -> Type) x1 x2 (H: x2 = x1) (y: P x1) :
rew <- [P] H in y = rew [P] (eq_sym H) in y.
Proof.
  now destruct H.
Defined.

Lemma eq_over_rew {A A'} {a: A} {a': A'} {H} (H0: a =_{H} a') : rew H in a = a'.
Proof.
  now destruct H, H0.
Defined.

Lemma rew_over: forall {T U} {t u} {H: T = U} (P: T -> Type) (Q: U -> Type) (H': forall x y (H'': x =_{H} y), P x = Q y), t =_{H} u -> P t -> Q u.
Proof.
  intros; now destruct H0, (H' t t).
Defined.

Lemma rew_over_rl: forall {T U t u} {H: T = U} (P: T -> Type), t =_{H} u -> P (rew <- H in u) -> P t.
Proof.
  intros; now destruct H, H0.
Defined.

Lemma rew_over_rl': forall {T U t u} {H: T = U} (P: U -> Type), t =_{H} u -> P u -> P (rew H in t).
Proof.
  intros; now destruct H0.
Defined.

Lemma rew_over_lr: forall {T U t u} {H: T = U} (P: T -> Type), t =_{H} u -> P t -> P (rew <- H in u).
Proof.
  intros; now destruct H, H0.
Defined.

Lemma rew_over_lr': forall {T U t u} {H: T = U} (P: U -> Type), t =_{H} u -> P (rew H in t) -> P u.
Proof.
  intros; now destruct H0.
Defined.

Lemma rew_pair : forall A (P Q: A -> Type) a b (x: P a) (y: Q a) (H: a = b),
  (rew H in x, rew H in y) = rew [fun a => (P a * Q a)%type] H in (x, y).
Proof.
  now destruct H.
Defined.

Lemma rew_sigT {A x} {P : A -> Type} (Q : forall a, P a -> Type)
  (u : { p : P x & Q x p }) {y} (H : x = y)
    : rew [fun x => { p : P x & Q x p }] H in u
      = existT (Q y) (rew H in u.1) (rew dependent H in u.2).
Proof.
  now destruct H, u.
Defined.

Theorem rew_permute A (P Q: A -> Type) (x y: A) (H: forall z, Q z = P z)
  (H': x = y) (a: P x) :
  rew <- [fun x => x] H y in rew H' in a =
  rew [Q] H' in rew <- [fun x => x] H x in a.
now destruct H'.
Defined.

Lemma rew_swap : forall A (P : A -> Type) a b (H: a = b) (x : P a) (y : P b),
x = rew <- H in y -> rew H in x = y.
Proof.
  now destruct H.
Defined.

Lemma rew_app A (P : A -> Type) (x y : A) (H H' : x = y) (a : P x) :
H = H' -> rew <- [P] H in rew [P] H' in a = a.
Proof.
  intros * ->. now destruct H'.
Defined.
End RewLemmas.
