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

  Ltac rew_triple :=
    match goal with
    | |- True => idtac
    | [ |- rew [ id ] ?mkcsp_inh ?refln) in _] => idtac
    | [ |- rew [id] f_equal mkcsp (le_irrelevance ?Hn' ?refln) _ in _ ] => idtac
    | [ |- rew <- [fun s : sumbool => ?mkcsp_aux _] _ ?Hn' hdD in _ ] => rewrite rew_compose; rewrite rew_map_opp_top; rewrite rew_opp_extrude; rewrite rew_compose.
    end.
End RewLemmas.
