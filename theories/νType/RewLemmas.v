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

Theorem rew_permute_lr A (P Q: A -> Type) (x y: A) (H: forall z, P z = Q z)
  (H': y = x) (a: P x) :
  rew [id] H y in rew <- [P] H' in a =
  rew <- [Q] H' in rew [id] H x in a.
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

Lemma rew_swap : forall A (P: A -> Type) a b (H: a = b) (x: P a) (y: P b),
  x = rew <- H in y <-> rew H in x = y.
Proof.
  now destruct H.
Qed.

Lemma rew_swap_rl : forall A (P: A -> Type) a b (H: a = b) (x: P a) (y: P b),
  x = rew <- H in y -> rew H in x = y.
Proof.
  now destruct H.
Qed.

Lemma rew_swap_lr : forall A (P: A -> Type) a b (H: a = b) (x: P b) (y: P a),
  x = rew H in y -> rew <- H in x = y.
Proof.
  now destruct H.
Defined.

Lemma rew_app_rl A (P : A -> Type) (x y: A) (H H': x = y) (a: P x) :
  H = H' -> rew <- [P] H in rew [P] H' in a = a.
Proof.
  intros * ->. now destruct H'.
Qed.

Lemma rew_app_rl_opp A (P : A -> Type) (x y: A) (H H': x = y) (a: P x) :
  H = H' -> a = rew <- [P] H in rew [P] H' in a.
Proof.
  intros * ->. now destruct H'.
Qed.

Lemma rew_app_lr A (P : A -> Type) (x y: A) (H H': y = x) (a: P x) :
  H = H' -> rew [P] H in rew <- [P] H' in a = a.
Proof.
  intros * ->. now destruct H'.
Qed.

Lemma rew_app_lr_opp A (P: A -> Type) (x y : A) (H H': y = x) (a: P x) :
  H = H' -> a = rew [P] H in rew <- [P] H' in a.
Proof.
  intros * ->. now destruct H'.
Qed.

Theorem rew_map' A B (P: B -> Type) (f: A -> B) x1 x2 (H: x1 = x2)
  (y: P (f x2)): rew <- [fun x => P (f x)] H in y = rew <- f_equal f H in y.
Proof.
  now destruct H.
Defined.

Lemma rew_compose_rl A (P: A -> Type) x1 x2 x3 (H1: x1 = x2) (H2: x3 = x2)
  (y: P x1): rew <- H2 in rew H1 in y = rew (eq_trans H1 (eq_sym H2)) in y.
Proof.
 now destruct H2.
Defined.

Lemma rew_compose_lr A (P: A -> Type) x1 x2 x3 (H1: x2 = x1) (H2: x2 = x3)
  (y: P x1) : rew H2 in rew <- H1 in y = rew (eq_trans (eq_sym H1) H2) in y.
Proof.
  now destruct H2.
Defined.

Lemma eq_ind_r_refl {A} {x y: A} {H: x = y} :
  eq_ind_r (fun x => x = y) eq_refl H = H.
Proof.
  now destruct H.
Qed.

Lemma map_subst_app {A B} {x y} {𝛉: A} (H: x = y :> B) (P: A -> B -> Type)
  (f: forall 𝛉, P 𝛉 x):
  rew [P 𝛉] H in f 𝛉 = (rew [fun x => forall 𝛉, P 𝛉 x] H in f) 𝛉.
Proof.
  now destruct H.
Defined.

Lemma rew_eq_refl : forall A B (x y: A) (f : A -> B) (H: x = y),
rew <- [fun x => f x = f y] H in eq_refl (f y) = f_equal f H.
now destruct H.
Defined.
