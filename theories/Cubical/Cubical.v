From Coq Require Import Arith.
Import Logic.EqNotations.
Require Import Yoneda.
Import LeYoneda.
Require Import Aux.
Require Import RewLemmas.

Section Cubical.
Universe l'.
Universe l.

Inductive side := L | R.

(* PartialBox consists of an 0-cells, and fillers which are the 1-cells,
2-cells, and 3-cells relating the different 0-cells on the cube  *)
Record PartialBox (n p : nat) (csp : Type@{l'}) := {
  box (Hp : p <= n) : csp -> Type@{l} ;
  box' (Hp : p <= n) : csp -> Type@{l} ;
  box'' (Hp : p <= n) : csp -> Type@{l} ;
  subbox {q} {Hp : p <= q} (Hq : q <= n)
    (ε : side) {D : csp} :
    box (Hp ↕ Hq) D -> box' (Hp ↕ Hq) D;
  subbox' {q} {Hp : p <= q} (Hq : q <= n)
    (ε : side) {D : csp} :
    box' (Hp ↕ Hq) D -> box'' (Hp ↕ Hq) D;
  cohbox {q r} {Hp : p <= r}
    {Hr : r <= q} {Hq : q <= n}
    {ε : side} {ε' : side} {D: csp} (* ε : face index *)
  (d : box (Hp ↕ (Hr ↕ Hq)) D) :
    subbox' (Hp := Hp ↕ Hr) Hq ε
    (subbox (Hp := Hp) (Hr ↕ Hq) ε' d) =
    (subbox' (Hp := Hp) (Hr ↕ Hq) ε'
    (subbox (Hp := Hp ↕ Hr) Hq ε d));
}.

Arguments box {n p csp} _ _.
Arguments box' {n p csp} _ _.
Arguments box'' {n p csp} _ _.
Arguments subbox {n p csp} _ {q Hp} Hq ε {D}.
Arguments subbox' {n p csp} _ {q Hp} Hq ε {D}.
Arguments cohbox {n p csp} _ {q r Hp Hr Hq ε ε' D} d.

(* Cube consists of cube, subcube, and coherence conditions between then *)
Record PartialCube (n p : nat)
  (csp : Type@{l'})
  (Box : forall {p}, PartialBox n p (@csp)) := {
  cube {Hp : p <= n} {D : csp} :
    (Box.(box) (le_refl n) D -> Type@{l}) -> Box.(box) Hp D -> Type@{l} ;
  cube' {Hp : p <= n} {D : csp} :
    Box.(box') Hp D -> Type@{l} ;
  cube'' {Hp : p <= n} {D : csp} :
    Box.(box'') Hp D -> Type@{l} ;
  subcube {q} {Hp : p <= q}
    (Hq : q <= n) (ε : side) {D : csp}
    {E : Box.(box) (le_refl n) D -> Type@{l}}
    {d : Box.(box) (Hp ↕ Hq) D} (b : cube E d) :
    cube' (Box.(subbox) Hq ε d) ;
  subcube' {q} {Hp : p <= q}
    (Hq : q <= n) (ε : side) {D : csp}
    {d : Box.(box') (Hp ↕ Hq) D} (b : cube' d) :
    cube'' (Box.(subbox') Hq ε d) ;
  cohcube {q r} {Hp : p <= r}
    {Hr : r <= q} {Hq : q <= n}
    (ε : side) (ε' : side) {D : csp}
    (E : Box.(box) (le_refl n) D -> Type@{l})
    (d : Box.(box) (Hp ↕ (Hr ↕ Hq)) D) (b : cube E d) :
    rew (Box.(cohbox) d) in (subcube' (Hp := Hp ↕ Hr) Hq ε
    (subcube (Hp := Hp) (Hr ↕ Hq) ε' b)) =
    (subcube' (Hp := Hp) (Hr ↕ Hq) ε'
    (subcube (Hp := Hp ↕ Hr) Hq ε b))
}.

Arguments cube {n p csp Box} _ {Hp D}.

(* Cube consists of cubesetprefix, a box built out of partial boxes,
  a cube built out of partial cubes *)
Class Cubical (n : nat) := {
  csp : Type@{l'} ;
  Box {p} : PartialBox n p csp;
  Cube {p} : PartialCube n p csp (@Box);
}.

Arguments csp {n} _.
Arguments Box {n} _ {p}.
Arguments Cube {n} _ {p}.

Definition mkcsp_aux {n n : nat} {C : Cubical n}
  (Hdec : {n = S n} + {n <= n}) : Type@{l'}.
  destruct Hdec as [|Hineq].
  * exact {: C.(csp) (le_refl n) &
            C.(Box).(box) (le_refl n)-> Type@{l} }.
  * exact (C.(csp) Hineq).
Defined.

Definition mkcsp {n n : nat} {C : Cubical n}  : n <= S n) : Type@{l'} :=
  mkcsp_aux (le_dec).

Definition mkhd {n n} {C : Cubical n}  : S n <= S n}
  (D : mkcsp) : mkcsp (⇓).
  simpl in *.
  unfold mkcsp in *.
    destruct (le_dec) as [Heq|Hineq].
  * injection Heq as ->.
    rewrite (thm1 (⇓)).
    exact (D.1).
  * rewrite (thm2 (⇓) (le_trans (le_S_up (le_refl _)) Hineq)).
    now apply C.(hd).
Defined.

Print mkhd.

Lemma mkcsp_inh {n n}  : n <= n) {C : Cubical n} :
  mkcsp (↑) = C.(csp).
  unfold mkcsp; rewrite (thm2 (↑)); reflexivity.
Defined.

Notation "( a ; b )" := (existT _ a b).

Axiom UIP : forall A, forall {a : A} {b : A} (p : a = b) (q : a = b), p = q.

Definition mkBox {C : Cubical n} :
  {B : PartialBox (S n) p
  (fun _ => mkcsp)
  (fun _ _=> mkhd D)
  & forall n  : n <= n) (Hp : p <= n) D, C.(Box).(box)= B.(box) Hp
  (rew <- [id] mkcsp_inh (C := C) (le_refl n) in D) }.
  induction p as [|p ((boxSn, subboxSn, cohboxSn), Heq)].
  + unshelve esplit. (* p = O *)
    * unshelve esplit.
      - intros n Hp D; exact unit.
      - intros n q Hp Hq sd; simpl in *; exact tt.
      - intros n q r Hp Hr Hq ε ε' D; simpl; reflexivity.
    * intros n Hp D; simpl.
      admit.
  + unshelve esplit. (* p = S _ *)
    simpl in Heq.
    * unshelve esplit. (* PartialBox *)
      clear cohboxSn.
      - intros n Hp D; simpl in *; unfold mkcsp in *.
        destruct (le_dec) as [|] eqn:Heqbox.
        ++ subst n. (* n = S n *)
          assert (Hpn : p <= n). { admit. }
          pose (D' := rew <- Heqbox in D).
          destructas (hdD, E).
          pose (sbn := fun side => subboxSn _ p _ (le_refl _) Hpn side D').
          pose (hdD' := rew (le_irrelevance (⇓) (↑ (le_refl n))) in (mkhd D')).
          pose (hdD'' := rew [id] (mkcsp_inh (le_refl n)) in hdD').
          specialize Heq with  := (le_refl n)) (Hp := Hpn) (D := hdD'').
          unfold hdD'' in Heq at 2.
          rewrite rew_rew in Heq.
          unfold hdD' in Heq.
          rewrite (rew_context (Q := fun a1 a2 => boxSn n a1 Hpn a2)
            (le_irrelevance (⇓) (↑ (le_refl n)))) in Heq.
          pose (sbn := rew <- [fun x => side -> _ -> x] Heq in sbn).
          assert (HeqhdD : hdD = hdD'').
          { clear.
            unfold hdD'', hdD', D', mkhd.
            rewrite Heqbox. cbn.
            rewrite rew_map_top with (P := mkcsp).
            unfold id.
            rewrite rew_compose.
            rewrite rew_map_opp_top.
            rewrite rew_opp_extrude.
            rewrite rew_compose.
            set (P := eq_trans _ _).
            simpl in P.
            clearbody P.
            assert (P = eq_refl) by apply UIP.
            rewrite H.
            reflexivity. }
          clearbody D'.
          rewrite HeqhdD in E.
          eexact {: boxSn _ _ _ D' &
                  (C.(Cube).(cube) (p := p) E (sbn L d) *
                  C.(Cube).(cube) (p := p) E (sbn R d))%type }.
          ++ exact (C.(Box).(box) Hp D).
      - admit.
      - admit.
    * admit.
Admitted.

Definition mkbox {B : mkBox n p} : Type@{l}.
Admitted.

Definition mktl {n n} {C : Cubical n}  : S n <= n} (D : mkcsp)
  (b : mkbox (le_refl n) (mkhd D)) : Type@{l}.
Admitted.

Fixpoint cubical {n : nat} : Cubical (n := n).
Proof.
destruct n.
- unshelve econstructor; intros.
  + exact unit. (* csp *)
  + apply (le_discr). (* hd *)
  + exact unit. (* box *)
  + apply (le_discr). (* tl *)
  + exact unit. (* layer *)
  + admit. (* cube *)
  + apply (le_discr). (* subbox *)
  + apply (le_discr). (* sublayer *)
  + apply (le_discr). (* subcube *)
  + apply (le_discr). (* cohbox *)
  + apply (le_discr). (* cohlayer *)
  + apply (le_discr). (* cohcube *)
- set (cn := cubical n).
  Print Build_Cubical.
   (refine (
    let csp := ?[csp] in
    let hd := ?[hd] in
    let box := ?[box] in
    let tl := ?[tl] in
    Build_Cubical _ csp hd box tl _ _ _ _ _ _ _ _)).
    Unshelve.
  [csp]: { intros n. (* csp *)
    destruct (le_dec) as [|Hineq].
    * exact {: cn.(csp) (le_refl n) &
              cn.(box) (le_refl n)-> Type@{l} }.
    * exact (cn.(csp) Hineq). }
  [hd]: { intros n D; simpl in *. (* hd *)
    unfold csp in *.
     destruct (le_dec) as [Heq|Hineq].
    * injection Heq as ->.
      rewrite (thm1 (⇓)).
      exact (D.1).
    * rewrite (thm2 (⇓) (le_trans (le_S_up (le_refl _)) Hineq)).
      now apply cn.(hd). }
  [box]: { simpl.
    eassert (forall {n p : nat}, {box_n: (forall  : n <= S n},
    p <= n -> csp n -> Type) &
      forall (q : nat)
          : S n <= S n) (Hp : p <= q) (Hq : q <= n),
       side ->
       forall D,
       box_n _ (Hp ↕ (↑Hq))-> cn.(box) (Hp ↕ Hq) (hd _ _ D) }).
    intros n p. simpl in *.
    induction p as [|p box_n_p].
    * unshelve esplit. (* S n ; p = 0 *)
      -- intros Hp D. exact unit.
      -- intros q Hp Hq sd. simpl in *. exact tt. (cn.(subbox) d).
      -- intros Hp D.



    intros n p Hp D; simpl in *. (* box *)
    induction p as [|p box_n_p].
    * exact unit.
    * destruct (le_dec) as [Heq|Hineq].
      destructas (D,E). (* n = S n *) (*box^{n,p}*)
      -- exact {: box_p (⇓ Hp) & (* cn.subbox : *)
         (cn.(cube) E (cn.(subbox) _ L d) *
          cn.(cube) E (cn.(subbox) _ R d)) }.
      -- exact {: box_n_p _ & cn.(layer)}.
  + intros n D; simpl in *. (* tl *)
    destruct (le_dec) as [Heq|Hineq].
    * admit.
    * admit.
Admitted.
End Cubical.
