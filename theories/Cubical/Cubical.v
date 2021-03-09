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

(* Cube consists of cubesetprefix, a box built out of partial boxes,
  a cube built out of partial cubes *)
Class Cubical (n : nat) := {
  csp : Type@{l'} ;
  Box {p} : PartialBox n p csp ;
  Cube {p} : PartialCube n p csp (@Box) ;
  eqbox0 {D : csp} : Box.(box) le0 D = unit ;
  eqbox0' {D : csp} : Box.(box') le0 D = unit ;
  eqboxSp {D : csp} {p} {Hp : p <= n} :
  Box.(box) Hp D = {d : Box.(box) Hp D &
  (Cube.(cube') (Box.(subbox) _ L d) *
  Cube.(cube') (Box.(subbox) _ R d))%type } ;
  eqsubbox0 {q} {Hq : q <= n} {ε : side} :
  Box.(subbox) (Hp := le0) Hq ε
  =_{f_equal2 (fun T1 T2 => T1 -> T2)
    (rew [fun e => Box.(box) e _] le_irrelevance le0 _ in eqbox0)
    (rew [fun e => Box.(box') e _] le_irrelevance le0 _ in eqbox0')} (fun _ => tt);
}.

Arguments csp {n} _.
Arguments Box {n} _ {p}.
Arguments Cube {n} _ {p}.

Definition mkcsp {n : nat} {C : Cubical n} : Type@{l'} :=
  { D : C.(csp) & C.(Box).(box) (le_refl n) D -> Type@{l} }.

Definition mkBox {n p} {C : Cubical n} : {dp : PartialBox (S n) p mkcsp &
{eqbox' :
forall {Hp : p <= n} {D : mkcsp}, dp.(box') (↑ Hp) D = C.(Box).(box) Hp D.1 &
{eqbox'' :
forall {Hp : p <= n} {D : mkcsp}, dp.(box'') (↑ Hp) D = C.(Box).(box') Hp D.1 &
forall {ε q} {D : mkcsp} {Hp : p <= q} {Hq : q <= n}, dp.(subbox') (↑ Hq) ε
=_{f_equal2 (fun T1 T2 => T1 -> T2) (eqbox' (Hp ↕ Hq) D) (eqbox'' (Hp ↕ Hq) D)}
C.(Box).(subbox) Hq ε}}}.
  induction p as [|p
    ((boxSn, boxSn', boxSn'', subboxSn, subboxSn', cohboxSn), eqBox)].
  + unshelve esplit. (* p = O *)
    * unshelve esplit. (* the six first goals *)
      - intros Hp D; exact unit.
      - intros Hp D; exact (C.(Box).(box) le0 D.1).
      - intros Hp D; exact (C.(Box).(box') le0 D.1).
      - simpl; intros q Hp Hq ε D _. rewrite C.(@box0 _). exact tt.
      - simpl; intros q Hp Hq ε D _. rewrite C.(@box0' _). exact tt.
      - simpl; intros q Hp Hr Hq ε ε' D d _; reflexivity.
    * unshelve esplit; simpl. (* the eqBox *)
      - intros Hp D. f_equal. apply le_irrelevance.
      - unshelve esplit; simpl.
        ++ intros Hp D. f_equal. apply le_irrelevance.
        ++ intros ε q D Hp Hq. simpl. destruct le_irrelevance.
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
End Cubical.
