(** Two definitions of "less than or equal" in SProp:
    - Recursive definition
    - "Yoneda trick" *)

From Bonak Require Import Notation.
From Coq Require Import StrictProp.

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
Class leY n m := le_intro : forall p, leR p n -> leR p m.
Infix "<=" := leY: nat_scope.

(* Equality in SProp is =S *)
Inductive eqsprop {A: SProp} (x: A): A -> Prop := eqsprop_refl: eqsprop x x.
Infix "=S" := eqsprop (at level 70): type_scope.

Theorem leY_irrelevance: forall {n m} (H H': n <= m), H =S H'.
  now reflexivity.
Qed.

(** A simple contraction used in the next lemma *)
Lemma leR_O_contra {n}: leR n.+1 O -> SFalse.
  now auto.
Qed.

Lemma leY_O {n}: O <= n.
  unfold "<=". intros p. destruct p. now auto. now auto.
Qed.

(** Contradiction of type n.+1 <= 0 *)
Theorem leY_O_contra {n}: n.+1 <= O -> False.
  intros. cut SFalse. intro Hn; elim Hn. unfold leY in H.
  specialize H with (p := 1); eapply leR_O_contra.
  apply H; clear H. now auto.
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
  now apply leR_O_contra in H. now apply IHn.
Qed.

Lemma leY_up {n m} (Hnm: n <= m): n <= m.+1.
  unfold "<=" in *. intros p Hpn. now apply leR_up, Hnm, Hpn.
Qed.

Notation "↑ h" := (leY_up h) (at level 40).

Lemma leR_down {n m} (Hnm: leR n.+1 m): leR n m.
  revert m Hnm. induction n. now auto. destruct m. intros H.
  now apply leR_O_contra in H. now apply IHn.
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

(* Small helpers *)

Definition rew_leY {x y z} (H: x = y) (le: leY z y): leY z x.
Proof.
  now rewrite H.
Defined.

Definition construct_Hq {n n'} (Hn': n' = n.+1): n.+1 <= n'.
  now subst n'.
Defined.

(** A tactic to derive contradiction from hypotheses of the form p.+2 <= 1 *)

Ltac le_contra Hq :=
  exfalso; clear -Hq; repeat apply leY_lower_both in Hq;
  now apply leY_O_contra in Hq.

(** A tactic to:
    - turn inequalities of the form p.+2 <= q.+1 into p.+2 <= q.+2
    - turn inequalities of the form p.+2 <= 2 into a substitution of p by 0
    - turn inequalities of the form p.+2 <= 1 into a contradiction *)

Ltac find_raise q :=
  match q with
  | ?q.+1 => find_raise q
  | 0 => constr:(@None nat)
  | _ => constr:(Some q)
  end.

Ltac invert_le Hpq :=
  match type of Hpq with
  | ?p.+1 <= ?q =>
     match find_raise q with
     | Some ?c => destruct c; [le_contra Hpq|]
     | None =>
       match find_raise p with
       | Some ?c => destruct c; [|le_contra Hpq]
       | None => le_contra Hpq
       end
     end
  end.
