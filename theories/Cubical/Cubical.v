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
  box' (Hp : p.+1 <= n) : csp -> Type@{l} ; (* [box' n D] is [box (n-1) D.1] *)
  box'' (Hp : p.+2 <= n) : csp -> Type@{l} ;
  (* [box'' n D] is [box (n-2) D.1.1] *)
  subbox {q} {Hp : p.+1 <= q.+1} (Hq : q.+1 <= n) (ε : side) {D : csp} :
  box (↓ (Hp ↕ Hq)) D -> box' (Hp ↕ Hq) D;
  subbox' {q} {Hp : p.+2 <= q.+2} (Hq : q.+2 <= n) (ε : side) {D : csp} :
  box' (↓ (Hp ↕ Hq)) D -> box'' (Hp ↕ Hq) D;
  cohbox {q r} {Hp : p.+2 <= r.+2}
  {Hr : r.+2 <= q.+1} {Hq : q.+1 <= n}
  {ε : side} {ε' : side} {D: csp} (* ε : face index *)
  (d : box (↓ ↓ (Hp ↕ (Hr ↕ Hq))) D) :
  subbox' _ ε (subbox _ ε' d) = (subbox' _ ε' (subbox _ ε d));
}.

Arguments box {n p csp} _ Hp.
Arguments box' {n p csp} _ Hp.
Arguments box'' {n p csp} _ Hp.
Arguments subbox {n p csp} _ {q Hp} Hq ε {D}.
Arguments subbox' {n p csp} _ {q Hp} Hq ε {D}.
Arguments cohbox {n p csp} _ {q r Hp Hr Hq ε ε' D} d.

(* Cube consists of cube, subcube, and coherence conditions between them *)
Record PartialCube (n p : nat)
  (csp : Type@{l'})
  (Box : forall {p}, PartialBox n p (@csp)) := {
  cube {Hp : p <= n} {D : csp} :
    (Box.(box) (le_refl n) D -> Type@{l}) -> Box.(box) Hp D -> Type@{l} ;
  cube' {Hp : p.+1 <= n} {D : csp} :
    Box.(box') Hp D -> Type@{l} ;
  cube'' {Hp : p.+2 <= n} {D : csp} :
    Box.(box'') Hp D -> Type@{l} ;
  subcube {q} {Hp : p.+1 <= q.+1}
    (Hq : q.+1 <= n) (ε : side) {D : csp}
    {E : Box.(box) (le_refl n) D -> Type@{l}}
    {d : Box.(box) (↓ (Hp ↕ Hq)) D} (b : cube E d) :
    cube' (Box.(subbox) Hq ε d) ;
  subcube' {q} {Hp : p.+2 <= q.+2}
    (Hq : q.+2 <= n) (ε : side) {D : csp}
    {d : Box.(box') (↓ (Hp ↕ Hq)) D} (b : cube' d) :
    cube'' (Box.(subbox') Hq ε d) ;
  cohcube {q r} {Hp : p.+2 <= r.+2}
    {Hr : r.+2 <= q.+1} {Hq : q.+1 <= n}
    (ε : side) (ε' : side) {D : csp}
    (E : Box.(box) (le_refl n) D -> Type@{l})
    (d : Box.(box) (↓ ↓ (Hp ↕ (Hr ↕ Hq))) D) (b : cube E d) :
    rew (Box.(cohbox) d) in
    (subcube' _ ε (subcube _ ε' b)) = (subcube' _ ε' (subcube _ ε b))
}.

Arguments cube {n p csp Box} _ {Hp D} E.
Arguments cube' {n p csp Box} _ {Hp D}.
Arguments cube'' {n p csp Box} _ {Hp D}.
Arguments subcube {n p csp Box} _ {q Hp} Hq ε {D} E {d} b.
Arguments subcube' {n p csp Box} _ {q Hp} Hq ε {D d} b.

(* Cube consists of cubesetprefix, a box built out of partial boxes,
  a cube built out of partial cubes *)
Class Cubical (n : nat) := {
  csp : Type@{l'} ;
  Box {p} : PartialBox n p csp ;
  Cube {p} : PartialCube n p csp (@Box) ;
  eqBox {len0: 0 <= n} {D : csp} : Box.(box) len0 D = unit ;
  eqBox' {len1: 1 <= n} {D : csp} : Box.(box') len1 D = unit ;
  eqBoxSp {D : csp} {p} (Hp : S p <= n) :
  Box.(box) Hp D = {d : Box.(box) (↓ Hp) D &
  (Cube.(cube') (Box.(subbox) _ L d) *
  Cube.(cube') (Box.(subbox) _ R d))%type } ;
  eqSubox0 {q} {len0: 0 <= q} {len1: 1 <= n} (Hq : q.+1 <= n)
    (ε : side) (D : csp) :
  Box.(subbox) (Hp := (⇑ len0)) Hq ε
    =_{f_equal2 (fun T1 T2 => T1 -> T2) (eqBox (D := D)) (eqBox' (D := D))}
    (fun _ => tt);
}.

Arguments csp {n} _.
Arguments Box {n} _ {p}.
Arguments Cube {n} _ {p}.

Definition mkcsp {n : nat} {C : Cubical n} : Type@{l'} :=
  { D : C.(csp) & C.(Box).(box) (le_refl n) D -> Type@{l} }.

Definition mkBox {n p} {C : Cubical n} : {dp : PartialBox n.+1 p mkcsp &
{eqbox' :
forall {Hp : p <= n} {HpS: p.+1 <= n.+1} {D : mkcsp},
  dp.(box') HpS D = C.(Box).(box) Hp D.1 &
  {eqbox'' :
  forall {Hp: p.+1 <= n} {HpS : p.+2 <= n.+1} {D : mkcsp},
    dp.(box'') HpS D = C.(Box).(box') Hp D.1 &
      forall {ε q} {D : mkcsp} {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n},
        dp.(subbox') (Hp := Hpq) (↑ Hq) ε
        =_{f_equal2 (fun T1 T2 => T1 -> T2) (eqbox' _ _ D) (eqbox'' _ _ D)}
        C.(Box).(subbox) (Hp := ↓ Hpq) Hq ε}}}.
  induction p as [|p ((boxSn, boxSn', boxSn'', subboxSn, subboxSn', cohboxSn),
                      (eqBox', (eqBox'', eqBox''')))].
  + unshelve esplit. (* p = O *)
    * unshelve esplit. (* the six first goals *)
      - intros Hp D; exact unit.
      - intros Hp D. exact (C.(Box).(box) (⇓ Hp) D.1).
      - intros Hp D; exact (C.(Box).(box') (⇓ Hp) D.1).
      - simpl; intros q Hp Hq ε D _; rewrite C.(@eqBox _); exact tt.
      - simpl; intros q Hp Hq ε D _; rewrite C.(@eqBox' _); exact tt.
      - simpl; intros q Hp Hr Hq ε ε' D d _; reflexivity.
    * unshelve esplit; simpl. intros Hp HpS D. (* eqBox' and eqbox'' *)
      rewrite <- (le_irrelevance (⇓ HpS) Hp).
      - reflexivity. (* eqBox' *)
      - unshelve esplit; simpl. intros Hp HpS.
        rewrite <- (le_irrelevance (⇓ HpS) Hp).
        ++ reflexivity. (* eqBox'' *)
        ++ intros ε q D Hpq H; simpl. (* eqBox''' *)
           admit.
  + unshelve esplit. (* p = S _ *)
    * simpl in eqBox', eqBox'', eqBox'''; (* the six first goals *)
      unshelve esplit;
      pose (Sub Hp side := (subboxSn p (le_refl p.+1) Hp side)).
      - intros Hp D. (* boxSn *)
        clear eqBox''' eqBox''.
        specialize eqBox' with (Hp := (⇓ Hp)) (D := D).
        pose (Sub' side d := rew [fun X => X] (eqBox' Hp) in Sub Hp side D d).
        exact {d : boxSn (↓ Hp) D &
               (C.(Cube).(cube) D.2 (Sub' L d) *
               C.(Cube).(cube) D.2 (Sub' R d))%type }.
      - intros Hp D. exact (C.(Box).(box) (⇓ Hp) D.1). (* boxSn' *)
      - intros Hp D. exact (C.(Box).(box') (⇓ Hp) D.1). (* boxSn '' *)
      - simpl. intros. destruct X as (d, (CL, CR)). (* subboxSn *)
        rewrite C.(@eqBoxSp _). unshelve esplit.
        ++ clear eqBox''' eqBox'' CL CR.
           specialize Sub with (Hp := (↓ (Hp ↕ Hq))) (D := D).
           specialize eqBox' with (Hp := (⇓ ↓ (Hp ↕ Hq)))
                                  (HpS := (↓ (Hp ↕ Hq))) (D := D).
           rewrite <- (le_trans_comm3 (Hp ↕ Hq)).
           exact (rew [fun X : Type => X] eqBox' in Sub ε d).
        ++ split. (* Sides L and R *)
           specialize cohboxSn with (r := p) (q := q) (Hp := le_refl p.+2)
                                    (Hr := Hp) (Hq := Hq) (ε := ε) (D := D).
           apply C.(Cube).(subcube) with (E := D.2); cbv zeta; unfold Sub.
           ** specialize cohboxSn with (ε' := L) (d := d). (* The side L *)
              admit.
           ** specialize cohboxSn with (ε' := R) (d := d). (* The side R *)
              admit.
      - simpl. admit. (* subboxSn' *)
      - admit.
   * admit. (* eqBox, eqBox', eqBox''' *)
Defined.
End Cubical.
