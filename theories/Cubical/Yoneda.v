Require Import Arith.
Require Import RelationClasses.
Require Import Coq.Program.Equality. (* dependent induction *)
Require Import Lia.
Require Import Aux.

Set Warnings "-notation-overridden".

(* False in SProp has no inhabitant *)
Inductive SFalse : SProp :=.
Inductive STrue : SProp := sI.

Fixpoint le' (n m : nat) : SProp :=
  match n, m with
  | O, _ => STrue
  | S n, O => SFalse
  | S n, S m => le' n m
  end.

Lemma le_refl' {n} : le' n n.
Proof.
  now induction n.
Qed.

Ltac reflexivity' := apply le_refl' || reflexivity.
Ltac reflexivity := reflexivity'.

Definition le n m := forall p, le' p n -> le' p m.
Infix "<=" := le : nat_scope.

(* Equality in SProp is =S *)
Inductive eqsprop {A : SProp} (x : A) : A -> Prop := eqsprop_refl : eqsprop x x.
Infix "=S" := eqsprop (at level 70) : type_scope.

Theorem le_irrelevance : forall {n m} (H H' : n <= m), H =S H'.
  now reflexivity.
Qed.

(* A simple contraction used in the next lemma *)
Lemma le'_1_O_contra: le' 1 O -> SFalse.
  now auto.
Qed.

(* Contradiction of type n.+1 <= 0 *)
Theorem le_contra {n}: n.+1 <= O -> False.
  intros; elimtype SFalse; unfold le in H.
  specialize H with (p := 1); apply le'_1_O_contra.
  apply H; clear H. now auto.
Qed.

(* le' -> Peano.le *)
(* SProp does not have <-> *)
Lemma le'_implies_le {n p} : le' p n -> Peano.le p n.
Admitted.

(* Peano.le -> le' *)
Lemma le_implies_le' {n p} : Peano.le p n -> le' p n.
Admitted.

(* leYoneda -> Peano.le *)
Lemma leYoneda_implies_le {n p} : p <= n -> Peano.le p n.
Admitted.

(* Peano.le -> leYoneda *)
Lemma le_implies_leYoneda {n p} : Peano.le p n -> p <= n.
Admitted.

(* Reflexivity in leYoneda *)
Definition le_refl n : n <= n :=
  fun _ x => x. (* Coq bug! *)

Notation "¹" := le_refl (at level 0).


(* Transitivity in leYoneda *)
Definition le_trans {n m p} (Hnm : n <= m) (Hmp : m <= p) : n <= p :=
  fun q (Hqn : le' q n) => Hmp _ (Hnm _ Hqn).

Infix "↕" := le_trans (at level 45).

(* Some trivial inequality proofs in leYoneda *)

Theorem le_S_up {n m} (Hnm : n <= m) : n <= m.+1.
  apply leYoneda_implies_le in Hnm. apply le_implies_leYoneda. now lia.
Qed.

Notation "↑ h" := (le_S_up h) (at level 40).

Theorem le_S_down {n m} (Hnm : n.+1 <= m) : n <= m.
  apply leYoneda_implies_le in Hnm. apply le_implies_leYoneda. now lia.
Qed.

Notation "↓ p" := (le_S_down p) (at level 40).

Theorem lower_S_both {n m} (Hnm : n.+1 <= m.+1) : n <= m.
  apply leYoneda_implies_le in Hnm. apply le_implies_leYoneda. now lia.
Qed.

Notation "⇓ p" := (lower_S_both p) (at level 40).

Theorem raise_S_both {n m} (Hnm : n <= m) : n.+1 <= m.+1.
  apply leYoneda_implies_le in Hnm. apply le_implies_leYoneda. now lia.
Qed.

Notation "⇑ p" := (raise_S_both p) (at level 40).

(* A tactic to turn inequalities of the form p.+2 <= q.+1 into p.+2 <= q.+2;
 * find_raise is a helper for the tactic *)

Ltac find_raise q :=
  match q with
  | ?q.+1 => find_raise q
  | _ => constr:(q)
  end.

Ltac invert_le Hpq :=
  match type of Hpq with
  | ?p.+1 <= ?q => let c := find_raise q in destruct c;
                   [exfalso; clear -Hpq; repeat apply lower_S_both in Hpq;
                   now apply le_contra in Hpq |]
  end.

(* Connecting Le with leYoneda *)

Lemma Le_implies_leYoneda {n p}: p <~ n -> p <= n.
Proof.
  intros [refl | q r]. now apply le_refl. apply le_S_down. induction l.
  now apply le_refl. now apply le_S_down.
Qed.

Lemma leYoneda_implies_Le {n p}: p <= n -> p <~ n.
Proof.
  intros H. unfold "<=" in H. specialize H with (1 := le_refl').
  revert n H. induction p, n. now constructor.
  intros _; now apply Le_0. intros H; now contradiction.
  intros H. simpl in H. apply IHp in H. now apply Raise_S_both.
Defined.

(* A couple of properties of the two connections, asserting the equality
 * of morphisms *)

Lemma Le_refl_morphism n: leYoneda_implies_Le (¹ n) = Le_refl' _.
Proof.
  induction n. now simpl.
  change (Le_refl' n.+1) with (Raise_S_both (Le_refl' n)). now rewrite <- IHn.
Qed.

Lemma Le_S_morphism {n p} (Hp: p.+1 <= n.+1):
  leYoneda_implies_Le (↓ Hp) = Le_S_down' (leYoneda_implies_Le Hp).
Proof.
  unfold leYoneda_implies_Le at 1.
Admitted.

(* Another way to state leYoneda *)
Inductive Leind n : forall p, p <= n -> Type :=
| Leind_n : Leind n n (¹ n)
| Leind_S p Hp : Leind n p.+1 Hp -> Leind n p (↓ Hp).

(* A constructor of Leind *)
Lemma Leind_construct {n p} Hp: Leind n p Hp.
Proof.
  intros; induction (leYoneda_implies_Le Hp).
  - rewrite (le_irrelevance Hp (¹ n)). (* should not be needed *)
    exact (Leind_n _).
  - rewrite (le_irrelevance Hp (↓ (Le_implies_leYoneda l))).
    apply Leind_S, IHl.
Defined.

(* le_induction along with a couple of computational properties *)

Theorem le_induction {n p} (Hp : p <= n) (P: forall p (Hp: p <= n), Type)
  (H_base: P n (¹ n))
  (H_step: forall p (Hp: p.+1 <= n) (H: P p.+1 Hp), P p (↓ Hp)): P p Hp.
Proof.
  induction (Leind_construct Hp); now auto.
Defined.

Lemma le_induction_base_computes {n P H_base H_step}:
  le_induction (¹ n) P H_base H_step = H_base.
Proof.
  unfold le_induction, Leind_construct. rewrite Le_refl_morphism; simpl.
  now destruct le_irrelevance.
Qed.

Lemma le_induction_step_computes {n p P H_base H_step} {Hp: p.+1 <= n}:
  le_induction (↓ Hp) P H_base H_step =
    H_step p Hp (le_induction Hp P H_base H_step).
Proof.
  invert_le Hp. unfold le_induction, Leind_construct.
  rewrite Le_S_morphism; simpl. now destruct le_irrelevance.
Qed.

(* Some helper-abbreviations *)

Definition le_induction' {n p} (Hp: p.+1 <= n.+1)
  (P: forall p (Hp: p.+1 <= n.+1), Type)
  (H_base: P n (¹ n.+1))
  (H_step: forall p (H : p.+2 <= n.+1), P p.+1 H -> P p (↓ H)): P p Hp :=
  le_induction (⇓ Hp) (fun p Hp => P p (⇑ Hp)) H_base
    (fun q Hq => H_step q (⇑ Hq)).

Definition le_induction'' {n p} (Hp : p.+2 <= n.+2)
  (P : forall p (Hp: p.+2 <= n.+2), Type)
  (H_base: P n (¹ n.+2))
  (H_step: forall p (H : p.+3 <= n.+2), P p.+1 H -> P p (↓ H)): P p Hp :=
  le_induction' (⇓ Hp) (fun p Hp => P p (⇑ Hp)) H_base
    (fun q Hq => H_step q (⇑ Hq)).

Definition le_induction'_base_computes {n P H_base H_step}:
  le_induction' (¹ n.+1) P H_base H_step = H_base :=
  le_induction_base_computes.

Definition le_induction'_step_computes {n p P H_base H_step} {Hp: p.+2 <= n.+1}:
  le_induction' (↓ Hp) P H_base H_step =
    H_step p Hp (le_induction' Hp P H_base H_step) :=
      le_induction_step_computes.
