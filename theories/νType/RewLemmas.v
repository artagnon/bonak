(** A few rewriting lemmas not in the standard library *)

Import Logic.EqNotations.
From Bonak Require Import Notation.

Lemma rew_rew {A} {x y: A} (H : x = y) P {a: P x} :
rew <- [P] H in rew [P] H in a = a.
  now destruct H.
Qed.

Lemma rew_rew' {A} {x y: A} (H: x = y) P {a: P y} :
rew [P] H in rew <- [P] H in a = a.
  now destruct H.
Qed.

Lemma rew_context {A} {x y: A} (eq: x = y) {P} {a: P x}
{Q: forall a, P a -> Type}: Q y (rew eq in a) = Q x a.
  now destruct eq.
Qed.

Lemma rew_pair: forall A {a} (P Q: A -> Type) (x: P a) (y: Q a)
  {b} (H: a = b), (rew H in x, rew H in y) =
                   rew [fun a => (P a * Q a)%type] H in (x, y).
Proof.
  now destruct H.
Qed.

Lemma rew_sigT {A x} {P: A -> Type} (Q: forall a, P a -> Type)
  (u: { p: P x & Q x p }) {y} (H: x = y)
    : rew [fun x => { p : P x & Q x p }] H in u
      = (rew H in u.1; rew dependent [fun x H => Q x (rew H in u.1)] H in u.2).
Proof.
  now destruct H, u.
Qed.

Lemma rew_existT_curried {A x} {P: A -> Type} {Q: {a & P a} -> Type}
   {y} {H: x = y}
   {u: P x} {v: Q (x; u)}
   {u': P y} {v': Q (y; u')}
   {Hu: rew H in u = u'} {Hv: rew (=H; Hu) in v = v'}:
   rew [fun x => {a: P x & Q (x; a)}] H in (u; v) = (u'; v').
Proof.
   now destruct Hu, Hv, H.
Qed.

Theorem rew_permute_rl A (P Q: A -> Type) (x y: A) (H: forall z, Q z = P z)
  (H': x = y) (a: P x) :
  rew <- [id] H y in rew [P] H' in a =
  rew [Q] H' in rew <- [id] H x in a.
Proof.
  now destruct H'.
Qed.

Theorem rew_permute_ll A (P Q: A -> Type) (x y: A) (H: forall z, P z = Q z)
  (H': x = y) (a: P x) :
  rew [id] H y in rew [P] H' in a =
  rew [Q] H' in rew [id] H x in a.
Proof.
  now destruct H'.
Qed.

Theorem rew_permute_rr A (P Q: A -> Type) (x y: A) (H: forall z, Q z = P z)
  (H': y = x) (a: P x) :
  rew <- [id] H y in rew <- [P] H' in a =
  rew <- [Q] H' in rew <- [id] H x in a.
Proof.
  now destruct H'.
Qed.

Lemma rew_swap : forall A (P : A -> Type) a b (H: a = b) (x : P a) (y : P b),
  x = rew <- H in y <-> rew H in x = y.
Proof.
  now destruct H.
Qed.

Lemma rew_swap_rl : forall A (P : A -> Type) a b (H: a = b) (x : P a) (y : P b),
  x = rew <- H in y -> rew H in x = y.
Proof.
  now destruct H.
Qed.

Lemma rew_swap_lr : forall A (P : A -> Type) a b (H: a = b) (x : P b) (y : P a),
  x = rew H in y -> rew <- H in x = y.
Proof.
  now destruct H.
Qed.

Lemma rew_app_rl A (P : A -> Type) (x y : A) (H H' : x = y) (a : P x) :
  H = H' -> rew <- [P] H in rew [P] H' in a = a.
Proof.
  intros * ->. now destruct H'.
Qed.

Lemma rew_app_rl_opp A (P : A -> Type) (x y : A) (H H' : x = y) (a : P x) :
  H = H' -> a = rew <- [P] H in rew [P] H' in a.
Proof.
  intros * ->. now destruct H'.
Qed.

Lemma rew_app_lr A (P : A -> Type) (x y : A) (H H' : y = x) (a : P x) :
  H = H' -> rew [P] H in rew <- [P] H' in a = a.
Proof.
  intros * ->. now destruct H'.
Qed.

Lemma rew_app_lr_opp A (P : A -> Type) (x y : A) (H H' : y = x) (a : P x) :
  H = H' -> a = rew [P] H in rew <- [P] H' in a.
Proof.
  intros * ->. now destruct H'.
Qed.

Lemma eq_ind_r_refl {A} {x y: A} {H: x = y} :
  eq_ind_r (fun x => eq x y) eq_refl H = H.
Proof.
  now destruct H.
Qed.

Lemma map_subst_app {A B} {x y} {𝛉: A} (H: x = y :> B) (P: A -> B -> Type)
  (f: forall 𝛉, P 𝛉 x):
  rew [P 𝛉] H in f 𝛉 = (rew [fun x => forall 𝛉, P 𝛉 x] H in f) 𝛉.
Proof.
  now destruct H.
Defined.

Lemma sigT_commute A (P : A -> Type) B (Q : B -> Type) C c
  (d : forall a, P a -> { b & Q b}) (e : forall b, Q b -> C) :
  match match c with (a; p) => d a p end with
  | (b; q) => e b q
  end =
  match c with
  | (a; p) => match d a p with (b; q) => e b q end
  end.
Proof.
  now destruct c.
Defined.
