From Coq Require Import Arith.
Import Logic.EqNotations.

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
End RewLemmas.
