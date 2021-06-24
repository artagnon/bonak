From Coq Require Import Arith.
Import Logic.EqNotations.
Require Import Yoneda.
Import LeYoneda.
Require Import Aux.
Require Import RewLemmas.
Set Printing Projections.

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
    {ε : side} {ε' : side} {D: csp} (d : box (↓ ↓ (Hpr ↕ (Hr ↕ Hq))) D) :
    PB.(subbox') Hq ε (subbox (Hr ↕ Hq) ε' d) =
    (PB.(subbox') (Hp := Hpr) (Hr ↕ Hq) ε'
    (subbox (Hp := ⇓ (Hpr ↕ Hr)) (↓ Hq) ε d));
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
    (d : Box.(box) (↓ ↓ (Hpr ↕ (Hr ↕ Hq))) D) (b : cube E d) :
    rew (Box.(cohbox) d) in
    (PC.(subcube') Hq ε (subcube (Hr ↕ Hq) ε' b)) =
    (PC.(subcube') (Hp := Hpr) (Hr ↕ Hq) ε'
    (subcube (Hp := ⇓ (Hpr ↕ Hr)) (↓ Hq) ε b))
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
  eqBox {len0: 0 <= n} {D : csp} : Box.(box) len0 D = unit ;
  eqBox' {len1: 1 <= n} {D : csp} : PB.(box') len1 D = unit ;
  eqBoxSp {D : csp} {p} (Hp : p.+1 <= n) :
    Box.(box) Hp D = {d : Box.(box) (↓ Hp) D &
                          (PC.(cube') (Box.(subbox) _ L d) *
                           PC.(cube') (Box.(subbox) _ R d))%type } ;
  eqSubox0 {q} {len0: 0 <= q} (Hq : q.+1 <= n) (ε : side) (D : csp) :
    Box.(subbox) (Hp := (⇑ len0)) Hq ε
    =_{f_equal2 (fun T1 T2 => T1 -> T2) (eqBox (D := D)) (eqBox' (D := D))}
      (fun _ => tt);
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
  * simpl; intros. rewrite C.(@eqBox _); exact tt. (* subboxSn *)
  * simpl; intros. admit. (* cohboxSn *)
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
        exact (subboxSn q (⇓ Hp) (↓ Hq) ε _ d).
      - split; simpl in *; (* Sides L and R *)
          cbv zeta; unfold Sub.
        specialize cohboxSn with (Hpr := le_refl p.+2) (Hr := Hp) (Hq := Hq)
                                 (ε := ε) (D := D).
        (* eqBox''': subboxSn' = subbox : Prop proving equality of terms *)
        (* The Prop is inhabited by eqBox'' *)
        (* rewrite tactic only works with eq_refl *)
        change (le_refl p.+2 ↕ (Hp ↕ Hq)) with (Hp ↕ Hq) in cohboxSn.
        pose (Q := fun (u : C.(PB).(box') (⇓ (Hp ↕ Hq)) D.1) =>
                        C.(PC).(cube') u).
        ++ specialize cohboxSn with (ε' := L) (d := d). (* The side L *)
           rewrite <- cohboxSn.
           specialize eqBox_copy''' with (ε := ε) (HpS := le_refl p.+2)
                                         (HqS := Hp ↕ Hq) (d := r')
                                         (d' := subboxSn p.+1 F (Hp ↕ Hq) L D d).
           apply (rew_over_rl' Q eqBox_copy''').
           unfold Q.
           eapply C.(Cube).(subcube) with (Hq0 := (⇓ Hp ↕ Hq)) (E := D.2).
           exact CL.
        ++ specialize cohboxSn with (ε' := R) (d := d). (* The side R *)
           set (r := rew _ in _).
           rewrite (le_trans_comm3 (Hp ↕ Hq)) in CR.
           set (r' := rew _ in _) in CR.
           assert (eqBox_copy''' := eqBox''').
           specialize eqBox''' with (ε := R) (HpS := le_refl p.+2)
                                    (HqS := Hp ↕ Hq) (d := r) (d' :=
                                                                 subboxSn p.+1 F (Hp ↕ Hq) ε D d).
           apply (rew_over_lr' Q eqBox''').
           rewrite <- cohboxSn.
           specialize eqBox_copy''' with (ε := ε) (HpS := le_refl p.+2)
                                         (HqS := Hp ↕ Hq) (d := r')
                                         (d' := subboxSn p.+1 F (Hp ↕ Hq) R D d).
           apply (rew_over_rl' Q eqBox_copy''').
           unfold Q.
           eapply C.(Cube).(subcube) with (Hq0 := (⇓ Hp ↕ Hq)) (E := D.2).
           exact CR.
      - intros. lazy zeta beta in X.  (* subboxSn' *)
        exact (C.(Box).(subbox) (⇓ Hq) ε X).
      - simpl. intros. lazy zeta. (* cohbox *)
        * admit. (* eqBox, eqBox', eqBox''' *)
Defined.
End Cubical.
