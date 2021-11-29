Require Import Interface.
Require Import Arith.
Require Import RelationClasses.
Require Import Program.
Require Import Aux.
Require Import Lia.

Module LeYoneda.

Inductive le' (n : nat) : nat -> SProp :=
  | le_refl' : n <= n
  | le_S_up' : forall {m : nat}, n <= m -> n <= S m
  where "n <= m" := (le' n m) : nat_scope.

Ltac reflexivity' := apply le_refl' || reflexivity.
Ltac reflexivity := reflexivity'.

Definition le n m := forall p, p <= n -> p <= m.
Infix "<=" := le : nat_scope.

Inductive eqsprop {A : SProp} (x : A) : A -> Prop := eqsprop_refl : eqsprop x x.
Infix "=S" := eqsprop (at level 70) : type_scope.

Theorem le_irrelevance : forall {n m} (H H' : n <= m), H =S H'.
  reflexivity.
Defined.

Inductive SFalse : SProp :=.

Lemma le'_1_O_contra: le' 1 O -> SFalse.
  inversion 1.
Defined.

Theorem le_contra {n}: S n <= O -> False.
  intros; elimtype SFalse; unfold le in H.
  specialize H with (p := 1); apply le'_1_O_contra.
  apply H; clear H; induction n. constructor. now constructor.
Defined.
Lemma le'_implies_le {n p} : le' p n -> Peano.le p n.
  intros H. destruct (Compare_dec.le_dec p n) as [|n0].
  assumption. enough (G:SFalse) by destruct G. dependent induction H.
  destruct n0; constructor. apply IHle'; intro; apply n0; now constructor.
Qed.

Lemma le_implies_le' {n p} : Peano.le p n -> le' p n.
  intros H. induction H. constructor. now constructor.
Qed.

Lemma leYoneda_implies_le {n p} : p <= n -> Peano.le p n.
  intros H. apply le'_implies_le. unfold "<=" in H. now apply H, le_refl'.
Qed.

Lemma le_implies_leYoneda {n p} : Peano.le p n -> p <= n.
  intros H. unfold "<=". intros p0 H0. apply le'_implies_le in H0.
  apply le_implies_le'. now lia.
Qed.

Definition le_refl n : n <= n :=
  fun _ x => x. (* Coq bug! *)

Definition le_trans {n m p} (Hnm : n <= m) (Hmp : m <= p) : n <= p :=
  fun q (Hqn : le' q n) => Hmp _ (Hnm _ Hqn).

Infix "↕" := le_trans (at level 45).

Theorem le_S_up {n m} (Hnm : n <= m) : n <= S m.
  unfold le; intros p Hpn.
  now apply le_S_up', Hnm.
Defined.

Notation "↑ h" := (le_S_up h) (at level 40).

Theorem le_S_down {n m} (Hnm : S n <= m) : n <= m.
  unfold le; intros p Hpn.
  now apply Hnm, le_S_up'.
Defined.

Notation "↓ p" := (le_S_down p) (at level 40).

Theorem le_S_both {n m} (Hnm : S n <= S m) : n <= m.
  apply leYoneda_implies_le in Hnm. apply le_implies_leYoneda. now lia.
Defined.

Notation "⇓ p" := (le_S_both p) (at level 40).

Theorem raise_S_both {n m} (Hnm : n <= m) : S n <= S m.
  apply leYoneda_implies_le in Hnm. apply le_implies_leYoneda. now lia.
Defined.

Notation "⇑ p" := (raise_S_both p) (at level 40).

Theorem le_trans_assoc {n m p q} (Hnm : n <= m) (Hmp : m <= p) (Hpq : p <= q) :
  Hnm ↕ (Hmp ↕ Hpq) =S (Hnm ↕ Hmp) ↕ Hpq.
Proof.
  reflexivity.
Defined.

Theorem le_trans_comm {n m p} (Hnm : n <= m) (Hmp : m <= p) :
  (Hnm ↕ ↑ Hmp) =S ↑ (Hnm ↕ Hmp).
Proof.
  reflexivity.
Defined.

Theorem le_trans_comm2 {m p} (Hmm : m <= m) (Hmp : S m <= S p) :
  (Hmm ↕ ↓ Hmp) =S ↑ (⇓ Hmp).
Proof.
  reflexivity.
Defined.

Theorem le_trans_comm3 {n m} (Hmn : S (S n) <= S m) : ⇓ (↓ Hmn) =S ↓ (⇓ Hmn).
Proof.
  reflexivity.
Defined.

Theorem le_trans_comm4 {n m p} (Hmn : S n <= S m) (Hmp : S m <= S p) :
  ⇓ (Hmn ↕ Hmp) =S (⇓ Hmn) ↕ (⇓ Hmp).
  reflexivity.
Defined.

Theorem le_trans_comm5 {n m p} (Hmn : n <= m) (Hmp : m <= p) :
  ⇑ (Hmn ↕ Hmp) =S (⇑ Hmn) ↕ (⇑ Hmp).
  reflexivity.
Defined.

Theorem le_trans_comm6 {n m} (Hmn : n <= m) : (⇓ ⇑ Hmn) =S Hmn.
  reflexivity.
Defined.

Theorem le_trans_comm7 {n m p} (Hmn : S n <= S m) (Hmp : S m <= p) :
  ↓ (Hmn ↕ Hmp) =S (⇓ Hmn) ↕ (↓ Hmp).
  reflexivity.
Defined.

Lemma eq_pair {A B : Type} {u1 v1 : A} {u2 v2 : B}
              (p : u1 = v1) (q : u2 = v2) : (u1, u2) = (v1, v2).
  now destruct p, q.
Defined.

Ltac applys_eq_core H :=
  eapply applys_eq_init;
  [ applys_eq_loop tt | apply H ];
  try ( reflexivity || apply le_irrelevance ).

Tactic Notation "applys_eq" constr(H) :=
  applys_eq_core H.

Lemma np_comparitor_shift {n p} : p <= n.+1 -> n.+1 - p + p - 1 = n.
  intros Hp. induction p.
  * simpl. rewrite Nat.sub_0_r, Nat.add_0_r. trivial. (* the p = 0 case *)
  * replace (n.+1 - p.+1) with (n - p) by auto; rewrite Nat.add_comm, Nat.add_succ_comm, Nat.add_comm; rewrite <- Nat.sub_succ_l; [apply IHp, le_S_down, Hp | pose proof (le_S_both Hp) as H; unfold "<=" in H;
  specialize H with (1 := le_refl' p); clear Hp IHp]. now apply le'_implies_le.
Qed.

Lemma np_comparitor_shift2 {n p} : p <= n -> n - (n - p) = p.
  revert n. induction p; intros.
  * simpl. now rewrite Nat.sub_0_r, Nat.sub_diag.
  * destruct n. apply le_contra in H as []. simpl Nat.sub at 2.
    rewrite Nat.sub_succ_l. f_equal. apply IHp. now apply le_S_both in H.
    now lia.
Qed.

Theorem le_induction : forall n, forall P : forall p, p <= n -> Type,
          P n (le_refl n) ->
          (forall p' (H : p'.+1 <= n), P p'.+1 H -> P p' (le_S_down H)) ->
          forall p (H : p <= n),
          P p H.
Proof.
Admitted.

Lemma le_induction' : forall n, forall P : forall p, p.+1 <= n.+1 -> Type,
        P n (le_refl n.+1) ->
        (forall p (H : p.+2 <= n.+1), P p.+1 H -> P p (le_S_down H)) ->
        forall p (H : p.+1 <= n.+1),
        P p H.
Proof.
Admitted.

Lemma le_induction_computes {n P H0 HS p H} : le_induction n P H0 HS p (le_S_down H) = HS p H (le_induction n P H0 HS p.+1 H).
Proof.
Admitted.
End LeYoneda.
