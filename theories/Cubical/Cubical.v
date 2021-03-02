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

Arguments box {n p csp} _ Hp.
Arguments box' {n p csp} _ Hp.
Arguments box'' {n p csp} _ Hp.
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

Arguments cube {n p csp Box} _ {Hp D} E.
Arguments cube' {n p csp Box} _ {Hp D}.
Arguments cube'' {n p csp Box} _ {Hp D}.
Arguments subcube {n p csp Box} _ {q Hp} Hq ε {D} E {d} b.
Arguments subcube' {n p csp Box} _ {q Hp} Hq ε {D d} b.

Axiom n0 : forall {n : nat}, 0 <= n.
Axiom np : forall {n : nat} p, p <= n.

(* Cube consists of cubesetprefix, a box built out of partial boxes,
  a cube built out of partial cubes *)
Class Cubical (n : nat) := {
  csp : Type@{l'} ;
  Box {p} : PartialBox n p csp ;
  Cube {p} : PartialCube n p csp (@Box) ;
  box0 {D : csp}: Box.(box) n0 D = unit ;
  box0' {D : csp}: Box.(box') n0 D = unit ;
  boxSp {D : csp} {p} : Box.(box) (np (S p)) D = {d : Box.(box) (np p) D &
  (Cube.(cube') (Box.(subbox) _ L d) *
  Cube.(cube') (Box.(subbox) _ R d))%type } ;
}.

Arguments csp {n} _.
Arguments Box {n} _ {p}.
Arguments Cube {n} _ {p}.

Definition mkcsp {n : nat} {C : Cubical n} : Type@{l'} :=
  { D : C.(csp) & C.(Box).(box) (le_refl n) D -> Type@{l} }.

Axiom UIP : forall A, forall {a : A} {b : A} (p : a = b) (q : a = b), p = q.

Definition mkBox {n p} {C : Cubical n} : {d : PartialBox (S n) p mkcsp &
forall {Hp : p <= n} {D : mkcsp}, d.(box') (↑ Hp) D = C.(Box).(box) Hp D.1 }.
  induction p as [|p
    ((boxSn, boxSn', boxSn'', subboxSn, subboxSn', cohboxSn), eqBox)].
  + unshelve esplit. (* p = O *)
    * unshelve esplit. (* the six first goals *)
      - intros Hp D; exact unit.
      - intros Hp D; exact (C.(Box).(box) n0 D.1).
      - intros Hp D; exact (C.(Box).(box') n0 D.1).
      - simpl; intros q Hp Hq ε D _. rewrite C.(@box0 _). exact tt.
      - simpl; intros q Hp Hq ε D _. rewrite C.(@box0' _). exact tt.
      - simpl; intros q Hp Hr Hq ε ε' D d _; reflexivity.
    * simpl. (* the eqBox *)
      intros Hp D. f_equal. apply le_irrelevance.
  + unshelve esplit. (* p = S _ *)
    * simpl in eqBox.
      assert (Hpn : p <= S n). { admit. }
      pose (Sub side := (subboxSn _ (le_refl p) Hpn side)).
      assert (↑ (np p) = le_refl p ↕ Hpn) by apply le_irrelevance.
      specialize eqBox with (Hp := (np p)).
      rewrite H in eqBox.
      unshelve esplit. (* the first six goals *)
      - intros Hp D.
        pose (Sub' side d := rew [fun X => X] (eqBox D) in Sub side D d).
        exact {d : boxSn Hpn D &
               (C.(Cube).(cube) D.2 (Sub' L d) *
               C.(Cube).(cube) D.2 (Sub' R d))%type }.
      - intros Hp D. exact (C.(Box).(box) (np (S p)) D.1).
      - intros Hp D. exact (C.(Box).(box') (np (S p)) D.1).
      - simpl. intros. destruct X as (d, (CL, CR)).
        rewrite C.(@boxSp _). unshelve esplit.
        ++ exact (rew [fun X : Type => X] eqBox D in Sub ε D d).
        ++ split.
          ** apply (C.(Cube).(subcube) _ ε D.2 CL).
  - admit.
      - admit.
    * admit.
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
