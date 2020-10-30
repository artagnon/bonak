From Coq Require Import Arith.
Import Logic.EqNotations.
Require Import Yoneda.
Import LeYoneda.

Section Cubical.
Universe l'.
Universe l.

Inductive side := L | R.

Record PartialBox (n p : nat) (csp : forall {n'} (Hn' : n' <= n), Type@{l'})
  (hd : forall {n'} {Hn' : S n' <= n}, csp Hn' -> csp (⇓ Hn')) := {
  box {n'} {Hn' : n' <= n} (Hp : p <= n') : csp Hn' -> Type@{l} ;
  subbox {n' q} {Hn' : S n' <= n} {Hp : p <= q} (Hq : q <= n')
    (ε : side) {D : csp Hn'} :
    box (Hp ↕ ↑ Hq) D -> box (Hp ↕ Hq) (hd D) ;
  cohbox {n' q r} {Hn' : S (S n') <= n} {Hp : p <= r}
    {Hr : r <= q} {Hq : q <= n'} {ε : side} {ε' : side}
    {D : csp Hn'} (d : box (Hp ↕ (Hr ↕ ↑ ↑ Hq)) D) :
    subbox (Hp := Hp ↕ Hr) Hq ε
    (subbox (Hp := Hp) (Hr ↕ ↑ Hq) ε' d) =
    (subbox (Hp := Hp) (Hr ↕ Hq) ε'
    (subbox (Hp := Hp ↕ Hr) (↑ Hq) ε d));
}.

Arguments box {n p csp hd} _ {n' Hn'}.
Arguments subbox {n p csp hd} _ {n' q Hn' Hp} Hq ε {D}.
Arguments cohbox {n p csp hd} _ {n' q r Hn' Hp Hr Hq ε ε' D}.

Record PartialCube (n p : nat)
  (csp : forall {n'} (Hn' : n' <= n), Type@{l'})
  (hd : forall {n'} {Hn' : S n' <= n}, csp Hn' -> csp (⇓ Hn'))
  (Box : forall {p}, PartialBox n p (@csp) (@hd))
  (tl : forall {n'} {Hn' : S n' <= n} (D : csp Hn'),
    Box.(box) (le_refl n') (hd D) -> Type@{l}) := {
  cube {n' p} {Hn' : n' <= n} {Hp : p <= n'} {D : csp Hn'} :
    (Box.(box) (le_refl n') D -> Type@{l}) -> Box.(box) Hp D -> Type@{l} ;
  subcube {n' p q} {Hn' : S n' <= n} {Hp : p <= q}
    (Hq : q <= n') (ε : side) {D : csp Hn'}
    {E : Box.(box) (le_refl (S n')) D -> Type@{l}}
    {d : Box.(box) (Hp ↕ ↑ Hq) D} (b : cube E d) :
    cube (tl D) (Box.(subbox) Hq ε d);
  cohcube {n' p q r} {Hn' : S (S n') <= n} {Hp : p <= r}
    {Hr : r <= q} {Hq : q <= n'}
    (ε : side) (ε' : side) {D : csp Hn'}
    (E : Box.(box) (le_refl (S (S n'))) D -> Type@{l})
    (d : Box.(box) (Hp ↕ (Hr ↕ ↑ ↑ Hq)) D) (b : cube E d) :
    rew (Box.(cohbox) d) in (subcube (Hp := Hp ↕ Hr) Hq ε
    (subcube (Hp := Hp) (↑ (Hr ↕ Hq)) ε' b)) =
    (subcube (Hp := Hp) (Hr ↕ Hq) ε'
    (subcube (Hp := Hp ↕ Hr) (↑ Hq) ε b))
}.

Record Cubical (n : nat) := {
  csp {n'} (Hn' : n' <= n) : Type@{l'} ;
  hd {n'} {Hn' : S n' <= n} : csp Hn' -> csp (⇓ Hn') ;
  Box {p} : PartialBox n p (@csp) (@hd) ;
  tl {n'} {Hn' : S n' <= n} (D : csp Hn') :
    Box.(box) (le_refl n') (hd D) -> Type@{l} ;
  Cube {p : nat} : PartialCube n p (@csp) (@hd) (@Box) (@tl);
}.

Record Cubical' {n : nat} :=
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

Theorem le_irrelevance : forall {n m} (H H' : n <= m), H = H'.
Admitted.

Theorem thm1 : forall {n} (H : n <= S n), le_dec H = right (le_refl n).
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
  Print Build_Cubical.
   (refine (
    let csp := ?[csp] in
    let hd := ?[hd] in
    let box := ?[box] in
    let tl := ?[tl] in
    Build_Cubical _ csp hd box tl _ _ _ _ _ _ _ _)).
    Unshelve.
  [csp]: { intros n' Hn'. (* csp *)
    destruct (le_dec Hn') as [|Hineq].
    * exact { D : cn.(csp) (le_refl n) &
              cn.(box) (le_refl n) D -> Type@{l} }.
    * exact (cn.(csp) Hineq). }
  [hd]: { intros n' Hn' D; simpl in *. (* hd *)
    unfold csp in *.
     destruct (le_dec Hn') as [Heq|Hineq].
    * injection Heq as ->.
      rewrite (thm1 (⇓ Hn')).
      exact (D.1).
    * rewrite (thm2 (⇓ Hn') (le_trans (le_S_up (le_refl _)) Hineq)).
      now apply cn.(hd). }
  [box]: { simpl.
    eassert (forall {n' p : nat}, {box_n': (forall {Hn' : n' <= S n},
    p <= n' -> csp n' Hn' -> Type) &
      forall (q : nat)
         (Hn' : S n' <= S n) (Hp : p <= q) (Hq : q <= n'),
       side ->
       forall D,
       box_n' _ (Hp ↕ (↑Hq)) D -> cn.(box) (Hp ↕ Hq) (hd _ _ D) }).
    intros n' p. simpl in *.
    induction p as [|p box_n'_p].
    * unshelve esplit. (* S n ; p = 0 *)
      -- intros Hn' Hp D. exact unit.
      -- intros q Hn' Hp Hq s D d. simpl in *. exact tt. (cn.(subbox) d).
      -- intros Hn' Hp D.



    intros n' p Hn' Hp D; simpl in *. (* box *)
    induction p as [|p box_n'_p].
    * exact unit.
    * destruct (le_dec Hn') as [Heq|Hineq].
      destruct D as (D,E). (* n' = S n *) (*box^{n',p}*)
      -- exact { d : box_p (⇓ Hp) & (* cn.subbox : *)
         (cn.(cube) E (cn.(subbox) _ L d) *
          cn.(cube) E (cn.(subbox) _ R d)) }.
      -- exact { d : box_n'_p _ & cn.(layer) d }.
  + intros n' Hn' D; simpl in *. (* tl *)
    destruct (le_dec Hn') as [Heq|Hineq].
    * admit.
    * admit.
Admitted.
End Cubical.
