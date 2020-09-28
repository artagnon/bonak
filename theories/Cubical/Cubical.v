From Coq Require Import Arith.
Import Logic.EqNotations.
Require Import Yoneda.
Import LeYoneda.

Section Cubical.
Universe l'.
Universe l.

Inductive side := L | R.

Record Cubical {n : nat} :=
{
  csp {n'} (Hn' : n' <= n) : Type@{l'} ;
  hd {n'} {Hn' : S n' <= n} : csp Hn' -> csp (⇓ Hn') ;
  box {n' p} {Hn' : n' <= n} (Hp : p <= n') : csp Hn' -> Type@{l} ;
  tl {n'} {Hn' : S n' <= n} (D : csp Hn') :
    box (le_refl n') (hd D) -> Type@{l} ;
  layer {n' p} {Hn' : n' <= n} {Hp : p <= n'} {D : csp Hn'} :
    box Hp D -> Type@{l} ;
  cube {n' p} {Hn' : n' <= n} {Hp : p <= n'} {D : csp Hn'} :
    (box (le_refl n') D -> Type@{l}) -> box Hp D -> Type@{l} ;
  subbox {n' p q} {Hn' : S n' <= n} {Hp : p <= q} (Hq : q <= n')
    (ε : side) {D : csp Hn'} :
    box (Hp ↕ ↑ Hq) D -> box (Hp ↕ Hq) (hd D) ;
  sublayer {n' p q} {Hn' : S n' <= n} {Hp : p <= q} (Hq : q <= n')
    (ε : side) {D : csp Hn'} {d : box (Hp ↕ ↑ Hq) D} :
    layer d -> layer (Hp := Hp ↕ Hq)
    (subbox (Hp := Hp) Hq ε d) ;
  subcube {n' p q} {Hn' : S n' <= n} {Hp : p <= q}
    (Hq : q <= n') (ε : side) {D : csp Hn'}
    {E : box (le_refl (S n')) D -> Type@{l}}
    {d : box (Hp ↕ ↑ Hq) D} (b : cube E d) :
    cube (tl D) (subbox Hq ε d);
  cohbox {n' p q r} {Hn' : S (S n') <= n} {Hp : p <= r}
    {Hr : r <= q} {Hq : q <= n'} {ε : side} {ε' : side}
    {D : csp Hn'} (d : box (Hp ↕ (Hr ↕ ↑ ↑ Hq)) D) :
    subbox (Hp := Hp ↕ Hr) Hq ε
    (subbox (Hp := Hp) (Hr ↕ ↑ Hq) ε' d) =
    (subbox (Hp := Hp) (Hr ↕ Hq) ε'
    (subbox (Hp := Hp ↕ Hr) (↑ Hq) ε d));
  cohlayer {n' p q r} {Hn' : S (S n') <= n} {Hp : S p <= r}
    {Hr : r <= q} {Hq : q <= n'} (ε : side) (ε' : side)
    {D : csp Hn'} (d : box (Hp ↕ (Hr ↕ ↑ ↑ Hq)) D)
    (b : layer d) : rew (cohbox d) in
    (sublayer (Hp := Hp ↕ Hr) Hq ε
    (sublayer (Hp := Hp) (↑ (Hr ↕ Hq)) ε' b)) =
    sublayer (Hp := Hp) (Hr ↕ Hq) ε'
    (sublayer (Hp := Hp ↕ Hr) (↑ Hq) ε b);
  cohcube {n' p q r} {Hn' : S (S n') <= n} {Hp : p <= r}
    {Hr : r <= q} {Hq : q <= n'}
    (ε : side) (ε' : side) {D : csp Hn'}
    (E : box (le_refl (S (S n'))) D -> Type@{l})
    (d : box (Hp ↕ (Hr ↕ ↑ ↑ Hq)) D) (b : cube E d) :
    rew (cohbox d) in (subcube (Hp := Hp ↕ Hr) Hq ε
    (subcube (Hp := Hp) (↑ (Hr ↕ Hq)) ε' b)) =
    (subcube (Hp := Hp) (Hr ↕ Hq) ε'
    (subcube (Hp := Hp ↕ Hr) (↑ Hq) ε b))
}.

Notation "l '.1'" := (projT1 l) (at level 40).
Notation "l '.2'" := (projT2 l) (at level 40).

Theorem le_irrelevance : forall {n m} (H H':n<=m), H = H'.
Admitted.

Theorem thm1 : forall {n} (H:n <= S n), le_dec H = right (le_refl n).
Proof.
intros.
destruct (le_dec H) as [Heq|].
- exfalso. apply n_Sn in Heq as [].
- f_equal.
  apply le_irrelevance.
Defined.

Theorem le_disjoint : forall n m, S n <= m -> m <= n -> False.
Admitted.

Theorem thm2 : forall {n n'} (H:n' <= S n) (H':n' <= n), le_dec H = right H'.
Proof.
intros.
destruct (le_dec H) as [->|].
- exfalso.
  now apply le_disjoint in H'.
- f_equal.
  apply le_irrelevance.
Defined.


Fixpoint cubical {n : nat} : Cubical (n:=n).
Proof.
destruct n.
- unshelve econstructor; intros.
  + exact unit. (* csp *)
  + apply (le_discr Hn'). (* hd *)
  + exact unit. (* box *)
  + apply (le_discr Hn'). (* tl *)
  + exact unit. (* layer *)
  + admit. (* cube *)
  + apply (le_discr Hn'). (* subbox *)
  + apply (le_discr Hn'). (* sublayer *)
  + apply (le_discr Hn'). (* subcube *)
  + apply (le_discr Hn'). (* cohbox *)
  + apply (le_discr Hn'). (* cohlayer *)
  + apply (le_discr Hn'). (* cohcube *)
- set (cn := cubical n).
unshelve econstructor.
  + intros n' Hn'.
    destruct (le_dec Hn') as [|Hn'']. (* csp *)
    * exact { D : cn.(csp) (le_refl n) &
              cn.(box) (le_refl n) D -> Type@{l} }.
    * exact (cn.(csp) Hn'').
  + intros n' Hn' D. simpl in *.
    destruct (le_dec Hn') as [Heq|Hineq].
    * injection Heq as ->.
      rewrite (thm1 (⇓ Hn')).
      exact (D.1). (* hd *)
    * rewrite (thm2 (⇓ Hn') (le_trans (le_S_up (le_refl _)) Hineq)).
      now apply cn.(hd).
  + intros n' Hn' D. simpl in *.
    admit.
  + intros n' Hn' D. simpl in *.
    destruct (le_dec Hn') as [Heq|Hineq].
    * rewrite Heq.
    rewrite (thm1 (⇓ Hn')).
    exact (D.2). (* tl *)
  * rewrite (thm2 (⇓ Hn') (le_trans (le_S_up (le_refl _)) Hineq)).
    now apply cn.(tl).


End Cubical.
