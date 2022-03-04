Require Import Arith.
Require Import RelationClasses.
Require Import Coq.Program.Equality. (* dependent induction *)
Require Import Lia.
Require Import Aux.

Set Warnings "-notation-overridden".

Inductive le' (n : nat) : nat -> SProp :=
  | le_refl' : n <= n
  | le_S_up' : forall {m : nat}, n <= m -> n <= m.+1
  where "n <= m" := (le' n m) : nat_scope.

Ltac reflexivity' := apply le_refl' || reflexivity.
Ltac reflexivity := reflexivity'.

Definition le n m := forall p, p <= n -> p <= m.
Infix "<=" := le : nat_scope.

(* Equality in SProp is =S *)
Inductive eqsprop {A : SProp} (x : A) : A -> Prop := eqsprop_refl : eqsprop x x.
Infix "=S" := eqsprop (at level 70) : type_scope.

Theorem le_irrelevance : forall {n m} (H H' : n <= m), H =S H'.
  reflexivity.
Qed.

Inductive SFalse : SProp :=.

Lemma le'_1_O_contra: le' 1 O -> SFalse.
  inversion 1.
Qed.

Theorem le_contra {n}: n.+1 <= O -> False.
  intros; elimtype SFalse; unfold le in H.
  specialize H with (p := 1); apply le'_1_O_contra.
  apply H; clear H; induction n. constructor. now constructor.
Qed.

(* le' <-> Peano.le *)
(* SProp does not have <-> *)
Lemma le'_implies_le {n p} : le' p n -> Peano.le p n.
  intros H. destruct (Compare_dec.le_dec p n) as [|n0].
  now assumption. enough (G:SFalse) by destruct G. dependent induction H.
  destruct n0; now constructor. apply IHle'; intro; apply n0; now constructor.
Qed.

Lemma le_implies_le' {n p} : Peano.le p n -> le' p n.
  intros H. induction H. now constructor. now constructor.
Qed.

(* leYoneda <-> Peano.le *)
Lemma leYoneda_implies_le {n p} : p <= n -> Peano.le p n.
  intros H. apply le'_implies_le. unfold "<=" in H. now apply H, le_refl'.
Qed.

Lemma le_implies_leYoneda {n p} : Peano.le p n -> p <= n.
  intros H. unfold "<=". intros p0 H0. apply le'_implies_le in H0.
  apply le_implies_le'. now lia.
Qed.

Definition le_refl n : n <= n :=
  fun _ x => x. (* Coq bug! *)

Notation "¹" := le_refl (at level 0).

Definition le_trans {n m p} (Hnm : n <= m) (Hmp : m <= p) : n <= p :=
  fun q (Hqn : le' q n) => Hmp _ (Hnm _ Hqn).

Infix "↕" := le_trans (at level 45).

Theorem le_S_up {n m} (Hnm : n <= m) : n <= m.+1.
  unfold le; intros p Hpn.
  now apply le_S_up', Hnm.
Qed.

Notation "↑ h" := (le_S_up h) (at level 40).

Theorem le_S_down {n m} (Hnm : n.+1 <= m) : n <= m.
  unfold le; intros p Hpn.
  now apply Hnm, le_S_up'.
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

Theorem le_S_down_distr {n m p} (Hmn : n.+1 <= m.+1) (Hmp : m.+1 <= p) :
  ↓ (Hmn ↕ Hmp) =S (⇓ Hmn) ↕ (↓ Hmp).
  reflexivity.
Qed.

Lemma eq_pair {A B : Type} {u1 v1 : A} {u2 v2 : B} (p : u1 = v1) (q : u2 = v2):
  (u1, u2) = (v1, v2).
  now destruct p, q.
Qed.

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

Theorem le_induction {n p} (Hpn : p <= n) (P: forall p (Hpn: p <= n), Type)
  (H_base: P n (¹ n))
  (H_step: forall p (Hpn: p.+1 <= n) (H: P p.+1 Hpn), P p (↓ Hpn)): P p Hpn.
Proof.
  intros *. induction n.
  pose (Q := leYoneda_implies_le Hpn); pose (R := Peano.le_0_n).
  assert (p = 0) as -> by lia; now exact H_base.
  pose (Q := leYoneda_implies_le Hpn); apply le_lt_eq_dec in Q;
  destruct Q. apply le_implies_leYoneda in l. apply (H_step p l).
  refine (IHn (⇓ l) (fun p Hpn => P p.+1 (⇑ Hpn)) H_base _).
  change (⇑ (↓ ?H)) with (↑ H); intros q Hqn; now exact (H_step q.+1 (⇑ Hqn)).
  assert (p = n.+1) as -> by assumption. now exact H_base.
Defined.

Definition le_induction' {n p} (Hpn: p.+1 <= n.+1)
  (P: forall p (Hpn: p.+1 <= n.+1), Type)
  (H_base: P n (¹ n.+1))
  (H_step: forall p (H : p.+2 <= n.+1), P p.+1 H -> P p (↓ H)): P p Hpn :=
  le_induction (⇓ Hpn) (fun p Hpn => P p (⇑ Hpn)) H_base
    (fun q Hqn => H_step q (⇑ Hqn)).

Definition le_induction'' {n p} (Hpn : p.+2 <= n.+2)
  (P : forall p (Hpn: p.+2 <= n.+2), Type)
  (H_base: P n (¹ n.+2))
  (H_step: forall p (H : p.+3 <= n.+2), P p.+1 H -> P p (↓ H)): P p Hpn :=
  le_induction' (⇓ Hpn) (fun p Hpn => P p (⇑ Hpn)) H_base
    (fun q Hqn => H_step q (⇑ Hqn)).

Lemma le_induction_computes {n p P H_base H_step} {Hpn: p.+1 <= n}:
  le_induction (↓ Hpn) P H_base H_step =
    H_step p Hpn (le_induction Hpn P H_base H_step).
Proof.
Admitted.

Lemma le_induction'_base_computes {n P H_base H_step}:
  le_induction' (¹ n.+1) P H_base H_step = H_base.
Proof.
Admitted.

Lemma le_induction'_step_computes {n p P H_base H_step} {Hpn: p.+2 <= n.+1}:
  le_induction' (↓ Hpn) P H_base H_step =
    H_step p Hpn (le_induction' Hpn P H_base H_step).
Proof.
Admitted.
