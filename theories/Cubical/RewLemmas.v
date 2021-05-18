From Coq Require Import Arith.
Import Logic.EqNotations.
Require Import Aux.

Section RewLemmas.
  Lemma rew_rew A (x y : A) (H : x = y) P (a : P x) :
  rew <- [P] H in rew [P] H in a = a.
  destruct H; reflexivity.
  Defined.

  Lemma rew_context {A} {x y : A} (eq : x = y) {P} {a : P x}
  {Q : forall a, P a -> Type} : Q y (rew eq in a) = Q x a.
  destruct eq; reflexivity.
  Defined.

  Theorem rew_map_top A (P:A->Type) x1 x2 (H:x1=x2) (y:P x1) :
  rew [P] H in y = rew [fun x => x] f_equal P H in y.
  Proof.
  destruct H; reflexivity.
  Defined.

  Theorem rew_map_opp_top A (P:A->Type) x1 x2 (H:x2=x1) (y:P x1) :
  rew <- [P] H in y = rew <- [fun x => x] f_equal P H in y.
  Proof.
  destruct H; reflexivity.
  Defined.

  Lemma rew_opp_extrude A (P:A->Type) x1 x2 (H:x2=x1) (y:P x1) :
  rew <- [P] H in y = rew [P] (eq_sym H) in y.
  Proof.
  destruct H. reflexivity.
  Defined.

  Lemma eq_over_rew {A A'} {a:A} {a':A'} {H} (H0:a =_{H} a') : rew H in a = a'.
  Proof.
  now destruct H, H0.
  Defined.

  Lemma rew_over: forall {T U} {t u} {H: T = U} (P: T -> Type) (Q: U -> Type) (H': forall x y (H'':x =_{H} y), P x = Q y), t =_{H} u -> P t -> Q u.
  Proof.
    intros.
    destruct H0, (H' t t).
    reflexivity.
    assumption.
  Defined.

  Lemma rew_over_rl: forall {T U t u} {H: T = U} (P: T -> Type), t =_{H} u -> P (rew <- H in u) -> P t.
  Proof.
    intros.
    destruct H, H0.
    assumption.
  Defined.

  Lemma rew_over_rl': forall {T U t u} {H: T = U} (P: U -> Type), t =_{H} u -> P u -> P (rew H in t).
  Proof.
    intros.
    destruct H0.
    assumption.
  Defined.

  Lemma rew_over_lr: forall {T U t u} {H: T = U} (P: T -> Type), t =_{H} u -> P t -> P (rew <- H in u).
  Proof.
    intros.
    destruct H, H0.
    assumption.
  Defined.

  Lemma rew_over_lr': forall {T U t u} {H: T = U} (P: U -> Type), t =_{H} u -> P (rew H in t) -> P u.
  Proof.
    intros.
    destruct H0.
    assumption.
  Defined.
End RewLemmas.
