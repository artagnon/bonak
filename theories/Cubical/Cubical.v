From Coq Require Import Arith.
Import Logic.EqNotations.
Require Import Yoneda.
Import LeYoneda.
Require Import Aux.

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

Arguments cube {n p csp hd Box tl} _ {n' p Hn' Hp D}.

Record PartialLayer (n : nat)
  (csp : forall {n'} (Hn' : n' <= n), Type@{l'})
  (hd : forall {n'} {Hn' : S n' <= n}, csp Hn' -> csp (⇓ Hn'))
  (Box : forall {p}, PartialBox n p (@csp) (@hd)) := {
  layer {n' p} {Hn' : n' <= n} {Hp : p <= n'} {D : csp Hn'} :
    Box.(box) Hp D -> Type@{l} ;
  sublayer {n' p q} {Hn' : S n' <= n} {Hp : p <= q} (Hq : q <= n')
    (ε : side) {D : csp Hn'} {d : Box.(box) (Hp ↕ ↑ Hq) D} :
    layer d -> layer (Hp := Hp ↕ Hq)
    (Box.(subbox) (Hp := Hp) Hq ε d) ;
  cohlayer {n' p q r} {Hn' : S (S n') <= n} {Hp : S p <= r}
    {Hr : r <= q} {Hq : q <= n'} (ε : side) (ε' : side)
    {D : csp Hn'} (d : Box.(box) (Hp ↕ (Hr ↕ ↑ ↑ Hq)) D)
    (b : layer d) : rew (Box.(cohbox) d) in
    (sublayer (Hp := Hp ↕ Hr) Hq ε
    (sublayer (Hp := Hp) (↑ (Hr ↕ Hq)) ε' b)) =
    sublayer (Hp := Hp) (Hr ↕ Hq) ε'
    (sublayer (Hp := Hp ↕ Hr) (↑ Hq) ε b);
}.

Class Cubical (n : nat) := {
  csp {n'} (Hn' : n' <= n) : Type@{l'} ;
  hd {n'} {Hn' : S n' <= n} : csp Hn' -> csp (⇓ Hn') ;
  Box {p} : PartialBox n p (@csp) (@hd) ;
  tl {n'} {Hn' : S n' <= n} (D : csp Hn') :
    Box.(box) (le_refl n') (hd D) -> Type@{l} ;
  Cube {p : nat} : PartialCube n p (@csp) (@hd) (@Box) (@tl);
}.

Arguments csp {n} _ {n'} Hn'.
Arguments hd {n} _ {n'}.
Arguments Box {n} _ {p}.
Arguments tl {n} _ {n' Hn'}.
Arguments Cube {n} _ {p}.

Definition mkcsp_aux {n n' : nat} {C : Cubical n}
  (Hdec : {n' = S n} + {n' <= n}) : Type@{l'}.
  destruct Hdec as [|Hineq].
  * exact { D : C.(csp) (le_refl n) &
            C.(Box).(box) (le_refl n) D -> Type@{l} }.
  * exact (C.(csp) Hineq).
Defined.

Definition mkcsp {n n' : nat} {C : Cubical n} (Hn' : n' <= S n) : Type@{l'} :=
  mkcsp_aux (le_dec Hn').

Definition mkhd {n n'} {C : Cubical n} {Hn' : S n' <= S n}
  (D : mkcsp Hn') : mkcsp (⇓ Hn').
  simpl in *.
  unfold mkcsp in *.
    destruct (le_dec Hn') as [Heq|Hineq].
  * injection Heq as ->.
    rewrite (thm1 (⇓ Hn')).
    exact (D.1).
  * rewrite (thm2 (⇓ Hn') (le_trans (le_S_up (le_refl _)) Hineq)).
    now apply C.(hd).
Defined.

Lemma mkcsp_inh {n n'} (Hn' : n' <= n) {C : Cubical n} :
  mkcsp (↑ Hn') = C.(csp) Hn'.
  unfold mkcsp; rewrite (thm2 (↑ Hn') Hn'); reflexivity.
Defined.

Lemma rew_rew A (x y : A) (H : x = y) P (a : P x) :
  rew <- [P] H in rew [P] H in a = a.
  destruct H; reflexivity.
Defined.

Lemma rew_context {A} {x y : A} (eq : x = y) {P} {a : P x}
  {Q : forall a, P a -> Type} : Q y (rew eq in a) = Q x a.
  destruct eq; reflexivity.
Defined.

Notation "( a ; b )" := (existT _ a b).

Theorem deprew {A} (Q:A->Type) (P:forall a:A, Q a -> Type)
{x y} (H : x = y) : (forall b:Q y, P y (rew <- H in b)) ->
forall a:Q x, P x a.
Proof.
  now destruct H.
Qed.

Definition mkBox {n p} {C : Cubical n} :
  {B : PartialBox (S n) p
  (fun _ Hn' => mkcsp Hn')
  (fun _ _ D => mkhd D)
  & forall n' (Hn' : n' <= n) (Hp : p <= n) D, C.(Box).(box) Hn' D = B.(box) Hp
  (rew <- [id] mkcsp_inh (C := C) (le_refl n) in D) }.
  induction p as [|p ((boxSn, subboxSn, cohboxSn), Heq)].
  + unshelve esplit. (* p = O *)
    * unshelve esplit.
      - intros n' Hn' Hp D; exact unit.
      - intros n' q Hn' Hp Hq s D d; simpl in *; exact tt.
      - intros n' q r Hn' Hp Hr Hq ε ε' D; simpl; reflexivity.
    * intros n' Hn' Hp D; simpl.
      admit.
  + unshelve esplit. (* p = S _ *)
    * unshelve esplit.
      - intros n' Hn' Hp D; simpl in *; unfold mkcsp in *.
        destruct (le_dec Hn') as [|] eqn:Heqbox.
        ++ subst n'. destruct (D) as (D', E) eqn:HD.
          revert HD.
          symmetry in Heqbox; refine (deprew _ _ Heqbox _ E).
          assert (Hpn : p <= n). { admit. }
          pose (hdD := rew [id] (mkcsp_inh (le_refl n)) in
            (rew (le_irrelevance (⇓ Hn') (↑ (le_refl n))) in (mkhd D))).
          specialize Heq with (Hn' := (le_refl n)) (Hp := Hpn) (D := hdD).
          unfold hdD in Heq at 2.
          rewrite rew_rew in Heq.
          rewrite (rew_context (Q := fun a1 a2 => boxSn n a1 Hpn a2)
            (le_irrelevance (⇓ Hn') (↑ (le_refl n)))) in Heq.
          pose (sbn := fun side => subboxSn _ p _ (le_refl _) Hpn side D).
          pose (sbn' := rew <- [fun x => side -> _ -> x] Heq in sbn).
          eexact { d : boxSn _ _ _ D &
                  (C.(Cube).(cube) E (sbn' L d) *
                  C.(Cube).(cube) E (sbn' R d))%type }.
          ++ admit.
      - admit.
      - admit.
    * admit.
Admitted.

Definition mkbox {n p} {B : mkBox n p} : Type@{l}.
Admitted.

Definition mktl {n n'} {C : Cubical n} {Hn' : S n' <= n} (D : mkcsp Hn')
  (b : mkbox (le_refl n') (mkhd D)) : Type@{l}.
Admitted.

Fixpoint cubical {n : nat} : Cubical (n := n).
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
