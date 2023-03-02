(** Two definitions of "less than or equal" in SProp:
    - Recursive definition
    - "Yoneda trick" *)

Require Import Notation.
Require Import LeInductive.

Set Warnings "-notation-overridden".

(** False and True in SProp *)
Inductive SFalse : SProp :=.
Inductive STrue : SProp := sI.

(** A recursive definition of le *)
Fixpoint leR (n m : nat) : SProp :=
  match n, m with
  | O, _ => STrue
  | S n, O => SFalse
  | S n, S m => leR n m
  end.

Lemma leR_refl {n} : leR n n.
Proof.
  now induction n.
Qed.

(** A Yoneda-style encoding of the recursive definition of le *)
Definition leY n m := forall p, leR p n -> leR p m.
Infix "<=" := leY: nat_scope.

(* Equality in SProp is =S *)
Inductive eqsprop {A: SProp} (x: A): A -> Prop := eqsprop_refl: eqsprop x x.
Infix "=S" := eqsprop (at level 70): type_scope.

Theorem leY_irrelevance: forall {n m} (H H': n <= m), H =S H'.
  now reflexivity.
Qed.

(** A simple contraction used in the next lemma *)
Lemma leR_contra {p}: leR p.+1 O -> SFalse.
  now auto.
Qed.

(** Contradiction of type n.+1 <= 0 *)
Theorem leY_contra {n}: n.+1 <= O -> False.
  intros. cut SFalse. intro Hn; elim Hn. unfold leY in H.
  specialize H with (p := 1); eapply leR_contra.
  apply H; clear H. now auto.
Qed.

Lemma leR_0 {n}: leR O n.
  destruct n. all: now auto.
Qed.

Lemma leY_0 {n}: O <= n.
  unfold leY. destruct p.
  - intros O. now apply leR_0.
  - intros H. now apply leR_contra in H.
Qed.

(** Reflexivity in leY *)
Definition leY_refl n: n <= n :=
  fun _ x => x. (* Coq bug! *)

Notation "♢" := leY_refl (at level 0).

(** Transitivity in leY *)
Definition leY_trans {n m p} (Hnm: n <= m) (Hmp: m <= p): n <= p :=
  fun q (Hqn: leR q n) => Hmp _ (Hnm _ Hqn).

Infix "↕" := leY_trans (at level 45).

(** Some trivial inequality proofs in leYoneda *)

Lemma leR_up {n m} (Hnm: leR n m): leR n m.+1.
  revert m Hnm. induction n. now auto. destruct m. intros H.
  now apply leR_contra in H. now apply IHn.
Qed.

Lemma leY_up {n m} (Hnm: n <= m): n <= m.+1.
  unfold "<=" in *. intros p Hpn. now apply leR_up, Hnm, Hpn.
Qed.

Notation "↑ h" := (leY_up h) (at level 40).

Lemma leR_down {n m} (Hnm: leR n.+1 m): leR n m.
  revert m Hnm. induction n. now auto. destruct m. intros H.
  now apply leR_contra in H. now apply IHn.
Qed.

Lemma leY_down {n m} (Hnm: n.+1 <= m): n <= m.
  unfold "<=" in *. intros p Hpn. now apply leR_down, Hnm.
Qed.

Notation "↓ p" := (leY_down p) (at level 40).

Lemma leR_lower_both {n m} (Hnm: leR n.+1 m.+1): leR n m.
  now auto.
Qed.

Lemma leY_lower_both {n m} (Hnm: n.+1 <= m.+1): n <= m.
  unfold "<=" in *. intros p Hpn. now apply leR_lower_both, Hnm.
Qed.

Notation "⇓ p" := (leY_lower_both p) (at level 40).

Lemma leR_raise_both {n m} (Hnm: leR n m): leR n.+1 m.+1.
  now auto.
Qed.

Lemma leY_raise_both {n m} (Hnm: n <= m): n.+1 <= m.+1.
  unfold "<=" in *. intros p Hpn. destruct p. now auto.
  now apply leR_raise_both, Hnm.
Qed.

Notation "⇑ p" := (leY_raise_both p) (at level 40).

(** A tactic to turn inequalities of the form p.+2 <= q.+1 into p.+2 <= q.+2;
    find_raise is a helper for the tactic *)

Ltac find_raise q :=
  match q with
  | ?q.+1 => find_raise q
  | _ => constr:(q)
  end.

Ltac invert_le Hpq :=
  match type of Hpq with
  | ?p.+1 <= ?q => let c := find_raise q in destruct c;
                   [exfalso; clear -Hpq; repeat apply leY_lower_both in Hpq;
                   now apply leY_contra in Hpq |]
  end.

(** Connecting leI with leY *)

Lemma leY_of_leI {n p}: p <~ n -> p <= n.
Proof.
  intros [refl | q r]. now apply leY_refl. apply leY_down. induction l.
  now apply leY_refl. now apply leY_down.
Qed.

Lemma leI_of_leY {n p}: p <= n -> p <~ n.
Proof.
  intros H. unfold "<=" in H. specialize H with (1 := leR_refl).
  revert n H. induction p, n. now constructor.
  intros _; now apply leI_0. intros H; now contradiction.
  intros H. simpl in H. apply IHp in H. now apply leI_raise_both.
Defined.

(** A couple of properties of the two connections, asserting the equality
    of morphisms *)

Lemma leI_refl_morphism n: leI_of_leY (♢ n) = leI_refl _.
Proof.
  induction n. now simpl.
  change (leI_refl n.+1) with (leI_raise_both (leI_refl n)). now rewrite <- IHn.
Qed.

Lemma leI_down_morphism {n p} (Hp: p.+1 <= n.+1):
  leI_of_leY (↓ Hp) = leI_down (leI_of_leY Hp).
Proof.
  revert n Hp. induction p, n.
  - unfold leI_of_leY at 1; now simpl.
  - unfold leI_of_leY; simpl. intros _. induction (leI_up leI_0). now auto.
    simpl. now rewrite IHl.
  - intros Hp. exfalso.
    now apply leY_lower_both, leY_contra in Hp.
  - intros Hp.
    change (leI_of_leY (↓ Hp)) with (leI_raise_both (leI_of_leY (↓ ⇓ Hp))).
    now rewrite IHp.
Defined.

(** An inductive on leY *)
Inductive leYind n : forall p, p <= n -> Type :=
| leYind_refl : leYind n n (♢ n)
| leYind_down p Hp : leYind n p.+1 Hp -> leYind n p (↓ Hp).

(** A constructor of leYind *)
Lemma leYind_construct {n p} Hp: leYind n p Hp.
Proof.
  intros; induction (leI_of_leY Hp).
  - rewrite (leY_irrelevance Hp (♢ n)). (* should not be needed *)
    exact (leYind_refl _).
  - rewrite (leY_irrelevance Hp (↓ (leY_of_leI l))).
    apply leYind_down, IHl.
Defined.

(** le_induction along with a couple of computational properties *)

Theorem le_induction {n p} (Hp: p <= n) (P: forall p (Hp: p <= n), Type)
  (H_base: P n (♢ n))
  (H_step: forall p (Hp: p.+1 <= n) (H: P p.+1 Hp), P p (↓ Hp)): P p Hp.
Proof.
  induction (leYind_construct Hp); now auto.
Defined.

Lemma le_induction_base_computes {n P H_base H_step}:
  le_induction (♢ n) P H_base H_step = H_base.
Proof.
  unfold le_induction, leYind_construct. rewrite leI_refl_morphism; simpl.
  now destruct leY_irrelevance.
Qed.

Lemma le_induction_step_computes {n p P H_base H_step} {Hp: p.+1 <= n}:
  le_induction (↓ Hp) P H_base H_step =
    H_step p Hp (le_induction Hp P H_base H_step).
Proof.
  invert_le Hp. unfold le_induction, leYind_construct.
  rewrite leI_down_morphism; simpl. now destruct leY_irrelevance.
Qed.

(** Some helper-abbreviations *)

Definition le_induction' {n p} (Hp: p.+1 <= n.+1)
  (P: forall p (Hp: p.+1 <= n.+1), Type)
  (H_base: P n (♢ n.+1))
  (H_step: forall p (H : p.+2 <= n.+1), P p.+1 H -> P p (↓ H)): P p Hp :=
  le_induction (⇓ Hp) (fun p Hp => P p (⇑ Hp)) H_base
    (fun q Hq => H_step q (⇑ Hq)).

Definition le_induction'' {n p} (Hp: p.+2 <= n.+2)
  (P : forall p (Hp: p.+2 <= n.+2), Type)
  (H_base: P n (♢ n.+2))
  (H_step: forall p (H : p.+3 <= n.+2), P p.+1 H -> P p (↓ H)): P p Hp :=
  le_induction' (⇓ Hp) (fun p Hp => P p (⇑ Hp)) H_base
    (fun q Hq => H_step q (⇑ Hq)).

Definition le_induction'_base_computes {n P H_base H_step}:
  le_induction' (♢ n.+1) P H_base H_step = H_base :=
  le_induction_base_computes.

Definition le_induction'_step_computes {n p P H_base H_step} {Hp: p.+2 <= n.+1}:
  le_induction' (↓ Hp) P H_base H_step =
    H_step p Hp (le_induction' Hp P H_base H_step) :=
      le_induction_step_computes.
