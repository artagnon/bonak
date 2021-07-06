From Coq Require Import Arith.
Import Logic.EqNotations.
Require Import Yoneda.
Import LeYoneda.
Require Import Aux.
Require Import RewLemmas.
Set Printing Projections.
Set Primitive Projections.

Section Cubical.
Universe l'.
Universe l.

Inductive side := L | R.

(* PartialBox consists of an 0-cells, and fillers which are the 1-cells,
2-cells, and 3-cells relating the different 0-cells on the cube  *)
Record PartialBoxBase (n : nat) (csp : Type@{l'}) := {
  box' {p} (Hp : p.+1 <= n) : csp -> Type@{l} ; (* [box' n D] is [box (n-1) D.1] *)
  box'' {p} (Hp : p.+2 <= n) : csp -> Type@{l} ;
  subbox' {p q} {Hp : p.+2 <= q.+2} (Hq : q.+2 <= n) (ε : side) {D : csp} :
    box' (↓ (Hp ↕ Hq)) D -> box'' (Hp ↕ Hq) D;
}.

Arguments box' {n csp} _ {p} Hp D.
Arguments box'' {n csp} _ {p} Hp D.
Arguments subbox' {n csp} _ {p q Hp} Hq ε {D} d.

Record PartialBox (n p : nat) (csp : Type@{l'})
       (PB : PartialBoxBase n csp) := {
  box (Hp : p <= n) : csp -> Type@{l} ;
  subbox {q} {Hp : p.+1 <= q.+1} (Hq : q.+1 <= n) (ε : side) {D : csp} :
    box (↓ (Hp ↕ Hq)) D -> PB.(box') (Hp ↕ Hq) D;
  cohbox {q r} {Hpr : p.+2 <= r.+2} {Hr : r.+2 <= q.+2} {Hq : q.+2 <= n}
    {ε : side} {ε' : side} {D: csp} (d : box (↓ (⇓ Hpr ↕ (↓ (Hr ↕ Hq)))) D) :
    PB.(subbox') Hq ε (subbox (↓ (Hr ↕ Hq)) ε' d) =
    (PB.(subbox') (Hp := Hpr) (Hr ↕ Hq) ε' (subbox Hq ε d));
}.


Arguments box {n p csp PB} _ Hp D.
Arguments subbox {n p csp PB} _ {q Hp} Hq ε {D}.
Arguments cohbox {n p csp PB} _ {q r Hpr Hr Hq ε ε' D} d.

Record PartialCubeBase (n : nat) (csp : Type@{l'})
  (PB : PartialBoxBase n (@csp)) := {
  cube' {p} {Hp : p.+1 <= n} {D : csp} :
    PB.(box') Hp D -> Type@{l} ;
  cube'' {p} {Hp : p.+2 <= n} {D : csp} :
    PB.(box'') Hp D -> Type@{l} ;
  subcube' {p q} {Hp : p.+2 <= q.+2}
    (Hq : q.+2 <= n) (ε : side) {D : csp}
    {d : PB.(box') (↓ (Hp ↕ Hq)) D} (b : cube' d) :
    cube'' (PB.(subbox') Hq ε d) ;
}.

Arguments cube' {n csp PB} _ {p Hp D} d.
Arguments cube'' {n csp PB} _ {p Hp D} d.
Arguments subcube' {n csp PB} _ {p q Hp} Hq ε {D d} b.

(* Cube consists of cube, subcube, and coherence conditions between them *)
Record PartialCube (n p : nat) (csp : Type@{l'}) {PB : PartialBoxBase n (@csp)}
  (PC : PartialCubeBase n csp PB)
  (Box : forall {p}, PartialBox n p (@csp) PB) := {
  cube {Hp : p <= n} {D : csp} :
    (Box.(box) (le_refl n) D -> Type@{l}) -> Box.(box) Hp D -> Type@{l} ;
  subcube {q} {Hp : p.+1 <= q.+1}
    (Hq : q.+1 <= n) (ε : side) {D : csp}
    {E : Box.(box) (le_refl n) D -> Type@{l}}
    {d : Box.(box) (↓ (Hp ↕ Hq)) D} (b : cube E d) :
    PC.(cube') (Box.(subbox) Hq ε d) ;
  cohcube {q r} {Hpr : p.+2 <= r.+2}
    {Hr : r.+2 <= q.+2} {Hq : q.+2 <= n}
    (ε : side) (ε' : side) {D : csp}
    (E : Box.(box) (le_refl n) D -> Type@{l})
    (d : Box.(box) (↓ (⇓ Hpr ↕ (↓ (Hr ↕ Hq)))) D) (b : cube E d) :
    rew (Box.(cohbox) d) in
    (PC.(subcube') Hq ε (subcube (↓ (Hr ↕ Hq)) ε' b)) =
    (PC.(subcube') (Hp := Hpr) (Hr ↕ Hq) ε' (subcube Hq ε b))
}.

Arguments cube {n p csp PB PC Box} _ {Hp D} E.
Arguments subcube {n p csp PB PC Box} _ {q Hp} Hq ε {D} E {d} b.
Arguments cohcube {n p csp PB PC Box} _ {q r Hpr Hr Hq ε ε' D E d} b.

(* Cube consists of cubesetprefix, a box built out of partial boxes,
  a cube built out of partial cubes *)
Class Cubical (n : nat) := {
  csp : Type@{l'} ;
  PB : PartialBoxBase n csp ;
  Box {p} : PartialBox n p csp PB ;
  PC : PartialCubeBase n csp PB ;
  Cube {p} : PartialCube n p csp PC (@Box) ;
  eqBox0 {len0: 0 <= n} {D : csp} : Box.(box) len0 D = unit ;
  eqBox0' {len1: 1 <= n} {D : csp} : PB.(box') len1 D = unit ;
  eqBoxSp {D : csp} {p} (Hp : p.+1 <= n) :
    Box.(box) Hp D = {d : Box.(box) (↓ Hp) D &
                          (PC.(cube') (Box.(subbox) _ L d) *
                           PC.(cube') (Box.(subbox) _ R d))%type } ;
  eqSubbox0 {q} {len0: 0 <= q} (Hq : q.+1 <= n) (ε : side) (D : csp) :
    Box.(subbox) (Hp := (⇑ len0)) Hq ε (rew <- [id] eqBox0 (D := D) in tt) =
      (rew <- [id] eqBox0' in tt);
}.

Arguments csp {n} _.
Arguments PB {n} _.
Arguments PC {n} _.
Arguments Box {n} _ {p}.
Arguments Cube {n} _ {p}.

Definition mkcsp {n : nat} {C : Cubical n} : Type@{l'} :=
  { D : C.(csp) & C.(Box).(box) (le_refl n) D -> Type@{l} }.

Definition mkPB {n} {C : Cubical n} :
  PartialBoxBase n.+1 mkcsp := {|
  box' {p} {Hp : p.+1 <= n.+1} {D : mkcsp} := C.(Box).(box) (⇓ Hp) D.1 ;
  box'' {p} {Hp : p.+2 <= n.+1} {D : mkcsp} := C.(PB).(box') (⇓ Hp) D.1 ;
  subbox' {p q} {Hp : p.+2 <= q.+2} {Hq : q.+2 <= n.+1} {ε} {D : mkcsp} {d} :=
    C.(Box).(subbox) (Hp := ⇓ Hp) (⇓ Hq) ε d ;
|}.

Definition mkBox {n p} {C : Cubical n} : PartialBox n.+1 p mkcsp mkPB.
  induction p as [|p (boxSn, subboxSn, cohboxSn)].
  + unshelve esplit. (* p = O *)
  * intros Hp D; exact unit.
  * simpl; intros. rewrite C.(@eqBox0 _); exact tt. (* subboxSn *)
  * simpl; intros. (* cohboxSn *)
    rewrite (eqSubbox0 (len0 := (⇓ ⇓ Hpr))).
    rewrite (eqSubbox0 (len0 := (⇓ ⇓ (Hpr ↕ Hr)))); reflexivity.
  + unshelve esplit; (* p = S _ *)
    pose (Sub Hp side := (subboxSn p (le_refl p.+1) Hp side)).
    * intros Hp D. (* boxSn *)
      pose (Sub' side d := Sub Hp side D d).
      exact {d : boxSn (↓ Hp) D &
                 (C.(Cube).(cube) D.2 (Sub' L d) *
                  C.(Cube).(cube) D.2 (Sub' R d))%type }.
    * simpl. intros. destruct X as (d, (CL, CR)). (* subboxSn *)
      rewrite C.(@eqBoxSp _). destruct q. admit. unshelve esplit.
      - clear CL CR.
        exact (subboxSn q.+1 (↓ Hp) Hq ε _ d).
      - simpl in *; cbv zeta; unfold Sub. (* Sides L and R *)
        specialize cohboxSn with (Hpr := le_refl p.+2) (Hr := Hp) (Hq := Hq)
                                 (ε := ε) (D := D).
        change (le_refl p.+2 ↕ (Hp ↕ Hq)) with (Hp ↕ Hq) in cohboxSn.
        set (T := fun (q : nat) Hqn => _) in cohboxSn.
        change T with (↓ Hp) in cohboxSn; clear T.
        set (T := fun (q0 : nat) Hqn => Hqn).
        (* SProp bug! *)
        change T with (le_refl p.+1); clear T.
        change (le_refl p.+1) with (⇓ le_refl p.+2). split.
        ++ specialize cohboxSn with (ε' := L) (d := d). (* The side L *)
           rewrite <- cohboxSn.
           eapply (C.(Cube).(subcube) (Hp := ⇓ Hp)) with (Hq := ⇓ Hq) in CL.
           exact CL.
        ++ specialize cohboxSn with (ε' := R) (d := d). (* The side R *)
           rewrite <- cohboxSn.
           eapply (C.(Cube).(subcube) (Hp := ⇓ Hp)) with (Hq := ⇓ Hq) in CR.
           exact CR.
    * simpl; intros. (* cohboxSn *)
      destruct d.
Admitted.
End Cubical.
