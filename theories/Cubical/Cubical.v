Import Logic.EqNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Program. (* UIP *)
Require Import Aux.
Require Import RewLemmas.

Set Warnings "-notation-overridden".
Require Import Yoneda.

Set Printing Projections.
Set Keyed Unification.
Remove Printing Let sigT.
Remove Printing Let prod.

Universe l'.
Universe l.

Parameter side: Type.

(* PartialBox consists of an 0-cells, and fillers which are the 1-cells,
   2-cells, and 3-cells relating the different 0-cells on the cube. *)
Class PartialBoxPrev (n : nat) (csp : Type@{l'}) := { (* csp: CubeSetPrefix *)
  box' {p} (Hp : p.+1 <= n) : csp -> Type@{l} ;
  box'' {p} (Hp : p.+2 <= n) : csp -> Type@{l} ;
  subbox' {p q} {Hpq : p.+2 <= q.+2} (Hq : q.+2 <= n) (ε : side) {D : csp} :
    box' (↓ (Hpq ↕ Hq)) D -> box'' (Hpq ↕ Hq) D;
}.

Arguments box' {n csp} _ {p} Hp D.
Arguments box'' {n csp} _ {p} Hp D.
Arguments subbox' {n csp} _ {p q Hpq} Hq ε {D} d.

Class PartialBox (n p : nat) (csp : Type@{l'})
  (BoxPrev : PartialBoxPrev n csp) := {
  box (Hp : p <= n) : csp -> Type@{l} ;
  subbox {q} {Hpq : p.+1 <= q.+1} (Hq : q.+1 <= n) (ε : side) {D : csp} :
    box (↓ (Hpq ↕ Hq)) D -> BoxPrev.(box') (Hpq ↕ Hq) D;
  cohbox {q r} {Hpr : p.+2 <= r.+2} {Hrq : r.+2 <= q.+2} {Hq : q.+2 <= n}
    {ε : side} {ω : side} {D: csp} (d : box (↓ (⇓ Hpr ↕ (↓ (Hrq ↕ Hq)))) D) :
    BoxPrev.(subbox') (Hpq := Hpr ↕ Hrq) Hq ε
      (subbox (Hpq := ⇓ Hpr) (↓ (Hrq ↕ Hq)) ω d) =
    (BoxPrev.(subbox') (Hpq := Hpr) (Hrq ↕ Hq) ω
      (subbox (Hpq := ↓ (Hpr ↕ Hrq)) Hq ε d));
}.

Arguments box {n p csp BoxPrev} _ Hp D.
Arguments subbox {n p csp BoxPrev} _ {q Hpq} Hq ε {D} d.
Arguments cohbox {n p csp BoxPrev} _ {q r Hpr Hrq Hq ε ω D} d.
(* We want ε and ω to be printed, but have them inferred;
   Coq doesn't support this. *)

(* We build cubes using an iterated construction: a cube at level n depends
   on cubes at level n-1 and n-2; just as we have box' and box'', we have
   cube' and cube''. *)
Class PartialCubePrev (n : nat) (csp : Type@{l'})
  (BoxPrev : PartialBoxPrev n (@csp)) := {
  cube' {p} {Hp : p.+1 <= n} {D : csp} :
    BoxPrev.(box') Hp D -> Type@{l};
  cube'' {p} {Hp : p.+2 <= n} {D : csp} :
    BoxPrev.(box'') Hp D -> Type@{l};
  subcube' {p q} {Hpq : p.+2 <= q.+2}
    (Hq : q.+2 <= n) (ε : side) {D : csp}
    {d : BoxPrev.(box') (↓ (Hpq ↕ Hq)) D} :
    cube' d -> cube'' (BoxPrev.(subbox') Hq ε d) ;
}.

Arguments cube' {n csp BoxPrev} _ {p Hp D} d.
Arguments cube'' {n csp BoxPrev} _ {p Hp D} d.
Arguments subcube' {n csp BoxPrev} _ {p q Hpq} Hq ε {D} [d] b.

(* Cube consists of cube, subcube, and coherence conditions between them *)
Class PartialCube (n : nat) (csp : Type@{l'})
  {BoxPrev : PartialBoxPrev n (@csp)}
  (CubePrev : PartialCubePrev n csp BoxPrev)
  (Box : forall {p}, PartialBox n p (@csp) BoxPrev) := {
  cube {p} {Hp : p <= n} {D : csp} :
    (Box.(box) (¹ n) D -> Type@{l}) -> Box.(box) Hp D -> Type@{l} ;
  subcube {p q} {Hpq : p.+1 <= q.+1}
    (Hq : q.+1 <= n) (ε : side) {D : csp}
    {E : Box.(box) (¹ n) D -> Type@{l}}
    {d : Box.(box) (↓ (Hpq ↕ Hq)) D} (c : cube E d) :
    CubePrev.(cube') (Box.(subbox) Hq ε d) ;
  cohcube {p q r} {Hpr : p.+2 <= r.+2}
    {Hrq : r.+2 <= q.+2} {Hq : q.+2 <= n}
    (ε : side) (ω : side) {D : csp}
    (E : Box.(box) (¹ n) D -> Type@{l})
    (d : Box.(box) (↓ (⇓ Hpr ↕ (↓ (Hrq ↕ Hq)))) D) (c : cube E d) :
    rew (Box.(cohbox) d) in
    CubePrev.(subcube') (Hpq := Hpr ↕ Hrq) Hq
    ε (subcube (Hpq := ⇓ Hpr) (↓ (Hrq ↕ Hq)) ω c) =
      (CubePrev.(subcube') (Hpq := Hpr) (Hrq ↕ Hq)
      ω (subcube (Hpq := ↓ (Hpr ↕ Hrq)) Hq ε c));
}.

Arguments cube {n csp BoxPrev CubePrev Box} _ {p Hp D} E.
Arguments subcube {n csp BoxPrev CubePrev Box} _ {p q Hpq Hq ε D E} [d] c.
Arguments cohcube {n csp BoxPrev CubePrev Box} _ {p q r Hpr Hrq Hq ε ω D E d} c.

(* Cube consists of CubeSetPrefix, a box built out of partial boxes,
  a cube built out of partial cubes, and some axioms related to our
  construction. *)
Class Cubical (n : nat) := {
  csp : Type@{l'} ;
  BoxPrev : PartialBoxPrev n csp ;
  Box {p} : PartialBox n p csp BoxPrev ;
  CubePrev : PartialCubePrev n csp BoxPrev ;
  Cube : PartialCube n csp CubePrev (@Box) ;

  (* Abbreviations corresponding to coherence conditions in Box *)
  Layer' {p} {Hp : p.+1 <= n} {D: csp} (d: Box.(box) (↓ Hp) D) :=
    forall ε, CubePrev.(cube') (Box.(subbox) Hp ε d);
  Layer'' {p} {Hp : p.+2 <= n} {D: csp} (d: BoxPrev.(box') (↓ Hp) D) :=
    forall ε, CubePrev.(cube'') (BoxPrev.(subbox') Hp ε d);
  SubLayer' {p q ε} {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n} {D: csp}
    (d: Box.(box) (↓ ↓ (Hpq ↕ Hq)) D) (l: Layer' d):
      Layer'' (Box.(subbox) Hq ε d) :=
  fun ω => rew Box.(cohbox) (Hrq := Hpq) d in CubePrev.(subcube') Hq ε (l ω) ;

  eqBox0 {len0: 0 <= n} {D : csp} : Box.(box) len0 D = unit ;
  eqBox0' {len1: 1 <= n} {D : csp} : BoxPrev.(box') len1 D = unit ;
  eqBoxSp {p} {Hp : p.+1 <= n} {D : csp} :
    Box.(box) Hp D = {d : Box.(box) (↓ Hp) D & Layer' d};
  eqBoxSp' {p} {Hp : p.+2 <= n} {D : csp} :
    BoxPrev.(box') Hp D = {d : BoxPrev.(box') (↓ Hp) D & Layer'' d } ;
  eqSubbox0 {q} {Hpq : 1 <= q.+1} {Hq : q.+1 <= n} {ε : side} {D : csp} :
    Box.(subbox) (Hpq := Hpq) Hq ε (rew <- [id] eqBox0 (D := D) in tt) =
      (rew <- [id] eqBox0' in tt) ;
  eqSubboxSp {ε p q} {D : csp} {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n}
    {d: Box.(box) (↓ ↓ (Hpq ↕ Hq)) D}
    {l: Layer' (Hp := ↓ (Hpq ↕ Hq)) d} :
    Box.(subbox) Hq ε (rew <- [id] eqBoxSp in (d; l)) =
      rew <- [id] eqBoxSp' in (Box.(subbox) Hq ε d; SubLayer' d l) ;
  eqCubeSp {p} {Hp : p.+1 <= n} {D : csp} {E d} :
    Cube.(cube) (Hp := ↓ Hp) E d = {l : Layer' d &
      Cube.(cube) (D := D) E (rew <- [id] eqBoxSp in (d; l))} ;
  eqCubeSp' {p} {Hp : p.+2 <= n} {D : csp} {d} :
    CubePrev.(cube') (Hp := ↓ Hp) d = {b : Layer'' d &
      CubePrev.(cube') (rew <- [id] eqBoxSp' (D := D) in (d; b))} ;
  eqSubcube0 {p} {Hp: p.+1 <= n} {D: csp} {E} {d} {ε : side}
    {l: Layer' d}
    {Q: Cube.(cube) (D := D) E (rew <- eqBoxSp in (d; l))} :
      l ε = Cube.(subcube) (Hq := Hp) (rew <- [id] eqCubeSp in (l; Q)) ;
  eqSubcubeSp {p q} {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n} {D : csp} {E} {d}
    {ε: side}
    {l: Layer' (Hp := ↓ (Hpq ↕ Hq)) d}
    {Q: Cube.(cube) (D := D) E (rew <- eqBoxSp in (d; l))} :
    Cube.(subcube) (Hpq := ↓ Hpq) (ε := ε) (rew <- [id] eqCubeSp in (l; Q)) = rew <- [id] eqCubeSp' (Hp := Hpq ↕ Hq) in
      (SubLayer' d l; rew [CubePrev.(cube')] eqSubboxSp in Cube.(subcube) Q) ;
}.

Arguments csp {n} _.
Arguments BoxPrev {n} _.
Arguments CubePrev {n} _.
Arguments Box {n} _ {p}.
Arguments Cube {n} _.
Arguments Layer' {n} _ {p Hp D} d.
Arguments Layer'' {n} _ {p Hp D} d.
Arguments SubLayer' {n} _ {p q} ε {Hpq Hq D d} l.
Arguments eqBox0 {n} _ {len0 D}.
Arguments eqBox0' {n} _ {len1 D}.
Arguments eqBoxSp {n} _ {p Hp D}.
Arguments eqBoxSp' {n} _ {p Hp D}.
Arguments eqSubbox0 {n} _ {q Hpq Hq ε D}.
Arguments eqSubboxSp {n} _ {ε p q D Hpq Hq d l}.
Arguments eqCubeSp {n} _ {p Hp D E d}.
Arguments eqCubeSp' {n} _ {p Hp D d}.
Arguments eqSubcube0 {n} _ {p Hp D E d ε l Q}.
Arguments eqSubcubeSp {n} _ {p q Hpq Hq D E d ε l Q}.

(* The csp at universe l' *)
Definition mkcsp {n} {C : Cubical n} : Type@{l'} :=
  { D : C.(csp) & C.(Box).(box) (¹ n) D -> Type@{l} }.

(* The previous level of Box *)
Definition mkBoxPrev {n} {C : Cubical n}: PartialBoxPrev n.+1 mkcsp := {|
  box' (p : nat) (Hp : p.+1 <= n.+1) (D : mkcsp) := C.(Box).(box) (⇓ Hp) D.1 ;
  box'' (p : nat) (Hp : p.+2 <= n.+1) (D : mkcsp) :=
    C.(BoxPrev).(box') (⇓ Hp) D.1 ;
  subbox' (p q : nat) (Hpq : p.+2 <= q.+2) (Hq : q.+2 <= n.+1) (ε : side)
    (D : mkcsp) (d : _) :=
    C.(Box).(subbox) (Hpq := ⇓ Hpq) (⇓ Hq) ε d ;
|}.

(* The coherence conditions that Box needs to satisfy to build the next level
   of Box. These will be used in the proof script of mkBox. *)

Definition mkLayer {n p} {Hp: p.+1 <= n.+1} {C: Cubical n} {D: mkcsp}
  {Box: PartialBox n.+1 p mkcsp mkBoxPrev} {d: Box.(box) (↓ Hp) D}: Type :=
  forall ε, C.(Cube).(cube) D.2 (Box.(subbox) (Hpq := ¹ _) Hp ε d).

Definition mkSubLayer {n p q} {ε: side} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n.+1}
  {C: Cubical n} {D: mkcsp} {Box: PartialBox n.+1 p mkcsp mkBoxPrev}
  (d: Box.(box) (↓ ↓ (Hpq ↕ Hq)) D)
  (l: mkLayer): C.(Layer') (Box.(subbox) Hq ε d) :=
  fun ω => rew Box.(cohbox) d in C.(Cube).(subcube) (Hpq := ⇓ Hpq) (l ω).

Definition cohBoxSnHyp {n p q r} {ε ω: side} {Hpr: p.+3 <= r.+3}
  {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1} {C: Cubical n} {D: mkcsp}
  {Box': PartialBox n.+1 p mkcsp mkBoxPrev}
  {d: Box'.(box) (↓ ↓ ↓ (Hpr ↕ Hrq ↕ Hq)) D} :
  C.(Box).(subbox) (Hpq := ↓ ⇓ (Hpr ↕ Hrq)) (⇓ Hq) ε
    (Box'.(subbox) (Hpq := ↓ ⇓ Hpr) (↓ (Hrq ↕ Hq)) ω d) =
  C.(Box).(subbox) (Hpq := ↓ ⇓ Hpr) (⇓ (Hrq ↕ Hq)) ω
    (Box'.(subbox) Hq ε d) :=
  Box'.(cohbox) (Hpr := ↓ Hpr) (Hrq := Hrq) (Hq := Hq) d.

Definition mkCohLayer {n p q r} {ε ω: side} {Hpr: p.+3 <= r.+3}
  {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1} {C: Cubical n} {D: mkcsp}
  {Box: PartialBox n.+1 p mkcsp mkBoxPrev}
  {d: Box.(box) (↓ ↓ ↓ (Hpr ↕ Hrq ↕ Hq)) D} (l: mkLayer):
  let sl := C.(SubLayer') (Hpq := ⇓ (Hpr ↕ Hrq)) ε
              (mkSubLayer (Hpq := ⇓ Hpr) d l) in
  let sl' := C.(SubLayer') (Hpq := ⇓ Hpr) ω
               (mkSubLayer (Hpq := ↓ (Hpr ↕ Hrq)) d l) in
  rew [C.(Layer'')] cohBoxSnHyp in sl = sl'.
Proof.
  intros *.
  subst sl sl'; apply functional_extensionality_dep; intros 𝛉; unfold Layer''.
  rewrite <- map_subst_app with
    (P := fun 𝛉 x => C.(CubePrev).(cube'') (C.(BoxPrev).(subbox') _ 𝛉 x))
    (f := C.(SubLayer') _ (mkSubLayer d l))
    (H := cohBoxSnHyp).
  unfold SubLayer', cohBoxSnHyp, mkSubLayer.
  rewrite <- map_subst with (f := C.(CubePrev).(subcube') (⇓ Hq) ε).
  rewrite <- map_subst with (f := C.(CubePrev).(subcube') (⇓ (Hrq ↕ Hq)) ω).
  rewrite rew_map with
    (f := fun x => C.(BoxPrev).(subbox') (⇓ (Hpr ↕ Hrq) ↕ ⇓ Hq) 𝛉 x).
  rewrite rew_map with (f := fun x => C.(BoxPrev).(subbox') (⇓ Hq) ε x).
  rewrite rew_map with
    (f := fun x => (C.(BoxPrev).(subbox') (⇓ (Hrq ↕ Hq)) ω x)).
  rewrite <- (C.(Cube).(cohcube) (Hrq := ⇓ Hrq) (Hq := ⇓ Hq)).
  repeat rewrite rew_compose; rewrite <- rew_swap. rewrite rew_app.
  now reflexivity. now apply UIP.
Qed.

#[local]
Instance mkCubePrev {n} {C: Cubical n} : PartialCubePrev n.+1 mkcsp mkBoxPrev :=
{|
  cube' (p : nat) (Hp : p.+1 <= n.+1) (D : mkcsp) := C.(Cube).(cube) D.2 :
    mkBoxPrev.(box') Hp D -> Type; (* Bug? *)
  cube'' (p : nat) (Hp : p.+2 <= n.+1) (D : mkcsp)
    (d : mkBoxPrev.(box'') Hp D) :=
    C.(CubePrev).(cube') d;
  subcube' (p q : nat) (Hpq : p.+2 <= q.+2) (Hq : q.+2 <= n.+1) (ε : side)
    (D : mkcsp) (d : _) (b : _) := C.(Cube).(subcube) (Hpq := ⇓ Hpq)
    (Hq := ⇓ Hq) (E := D.2) b;
|}.

(* The box at level n.+1 with p = O *)
#[local]
Instance mkBox0 {n} {C: Cubical n} : PartialBox n.+1 O mkcsp mkBoxPrev.
  unshelve esplit.
  * intros; now exact unit. (* boxSn *)
  * simpl; intros; rewrite C.(eqBox0). now exact tt. (* subboxSn *)
  * simpl; intros. (* cohboxp *)
    now rewrite eqSubbox0 with (Hpq := ⇓ Hpr),
                eqSubbox0 with (Hpq := ⇓ (Hpr ↕ Hrq)).
Defined.

(* The box at level n.+1 with p = S _ *)
#[local]
Instance mkBoxSp {n p} {C: Cubical n}
  {Box: PartialBox n.+1 p mkcsp mkBoxPrev}:
  PartialBox n.+1 p.+1 mkcsp mkBoxPrev.
  unshelve esplit.
  * intros Hp D; exact {d : Box.(box) (↓ Hp) D & mkLayer (d := d)}.
  * simpl; intros * ε * (d, l); invert_le Hpq. (* subboxp *)
    now exact (rew <- [id] C.(eqBoxSp) in
      (Box.(subbox) Hq ε d; mkSubLayer d l)).
  * simpl; intros q r Hpr Hrq Hq ε ω D (d, l). (* cohboxp *)
    invert_le Hpr; invert_le Hrq.

    (* A roundabout way to simplify the proof of mkCohCube_step *)
    etransitivity. apply (C.(eqSubboxSp) (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq)).
    etransitivity.
    2: symmetry; apply (C.(eqSubboxSp) (Hpq := ⇓ Hpr) (Hq := ⇓ (Hrq ↕ Hq))).

    apply f_equal with (B := C.(BoxPrev).(box') _ D.1)
      (f := fun x => rew <- (C.(eqBoxSp') (Hp := ⇓ (Hpr ↕ Hrq) ↕ ⇓ Hq)) in x).
    now exact (= (cohBoxSnHyp (Hpr := Hpr) (Hrq := Hrq)); mkCohLayer l).
    (* Bug? Coq being too smart for its own good. *)
Defined.

(* Finally, we can define mkBox *)
#[local]
Instance mkBox {n} {C: Cubical n} p : PartialBox n.+1 p mkcsp mkBoxPrev.
  induction p.
  + now exact mkBox0. (* p = O *)
  + now exact (mkBoxSp (Box := IHp)). (* p = S _ *)
Defined.

(* For Cube, we take a different strategy. We first define mkcube, mksubcube,
  and lemmas corresponding to their computational properties *)
(* Fist, for cube *)

Definition mkcube {n p} {C: Cubical n} {Hp : p <= n.+1} {D : mkcsp}
  (E: (mkBox n.+1).(box) (¹ n.+1) D -> Type)
  (d: (mkBox p).(box) Hp D): Type.
  revert d; apply le_induction with (Hp := Hp); clear p Hp. (* cubeSn *)
  + now exact E. (* p = n *)
  + intros p Hp IH d; exact {l : mkLayer & IH (d; l)}. (* p = S n *)
Defined.

Lemma mkcube_computes {n p} {C : Cubical n} {Hp : p.+1 <= n.+1} {D : mkcsp}
  {E: (mkBox n.+1).(box) (¹ n.+1) D -> Type} {d}:
  mkcube (Hp := ↓ Hp) E d = {l : mkLayer & mkcube (Hp := Hp) E (d; l)}.
Proof.
  unfold mkcube; now rewrite le_induction_step_computes.
Qed.

(* Now, subcube, and the corresponding computational properties. *)

Definition mksubcube {n} {C: Cubical n} {p q} {Hpq : p.+1 <= q.+1}
  {Hq: q.+1 <= n.+1} {ε : side} {D}
  (E : (mkBox n.+1).(box) (¹ n.+1) D -> Type)
  (d : (mkBox p).(box) (↓ (Hpq ↕ Hq)) D)
  (Cube: mkcube (Hp := ↓ (Hpq ↕ Hq)) E d):
    mkCubePrev.(cube') ((mkBox p).(subbox) Hq ε d).
Proof.
  intros *; revert d Cube; simpl. (* subcubeSn *)
  pattern p, Hpq. (* Bug? Why is this needed? *)
  apply le_induction'.
  + intros d c; rewrite mkcube_computes in c. destruct c as (l, _).
    now exact (l ε).
  + clear p Hpq; intros p Hpq IH d c; invert_le Hpq.
    rewrite mkcube_computes in c; destruct c as (l, c).
    change (⇓ (↓ ?Hpq ↕ ?Hq)) with (↓ ⇓ (Hpq ↕ Hq)); rewrite C.(eqCubeSp).
    apply IH in c.
    now exact (mkSubLayer d l; c).
Defined.

Lemma mksubcube_base_computes {p n} {C : Cubical n} {Hp : p.+1 <= n.+1}
  {ε : side} {D E} {d: (mkBox p).(box) _ D} {c} :
  mksubcube (Hq := Hp) E d c =
  match (rew [id] mkcube_computes in c) with
  | (l; _) => l ε
  end.
Proof.
  unfold mksubcube; now rewrite le_induction'_base_computes.
Qed.

Lemma mksubcube_step_computes {q r n} {C : Cubical n} {Hq : q.+2 <= n.+1}
  {Hrq : r.+2 <= q.+2} {ε : side} {D E} {d: (mkBox r).(box) _ D} {c} :
  mksubcube (Hpq := ↓ Hrq) (Hq := Hq) (ε := ε) E d c =
  match (rew [id] mkcube_computes in c) with
  | (l; c) => rew <- [id] C.(eqCubeSp) in
    (mkSubLayer d l; mksubcube (Hpq := Hrq) E (d; l) c)
  end.
Proof.
  unfold mksubcube; now rewrite le_induction'_step_computes.
Qed.

(* Now, for the last part of the proof: proving coherence conditions
  on cohcube *)

(* The base case is easily discharged *)
Definition mkCohCube_base {q r n} {ε ω: side} {C : Cubical n} {D: mkcsp}
  {Hrq: r.+2 <= q.+2} {Hq: q.+2 <= n.+1}
  {E: (mkBox n.+1).(box) (¹ n.+1) D -> Type}
  (d: (mkBox r).(box) (↓ ↓ (Hrq ↕ Hq)) D)
  (c: mkcube E d):
  rew [mkCubePrev.(cube'')] (mkBox r).(cohbox) (Hpr := ¹ _) d in
    mkCubePrev.(subcube') (Hpq := Hrq) Hq ε
      (mksubcube (ε := ω) (Hpq := ¹ _) (Hq := ↓ (Hrq ↕ Hq)) E d c) =
  mkCubePrev.(subcube') (Hpq := ¹ _) (Hrq ↕ Hq) ω
    (mksubcube (ε := ε) (Hpq := ↓ Hrq) (Hq := Hq) E d c).
  change (¹ _ ↕ ?H) with H; change (⇓ ¹ _ ↕ ?H) with H.
  rewrite mksubcube_base_computes, mksubcube_step_computes.
  destruct (rew [id] mkcube_computes in c) as (l, c'); clear c.
  now refine (C.(eqSubcube0)
    (Q := mksubcube (Hpq := Hrq) E (_; _) c')).
Qed.

(* A small abbreviation *)
Definition mkCohCube p {q r n} {ε ω: side} {C : Cubical n} {D: mkcsp}
  (Hpr: p.+2 <= r.+3) {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1}
  {E: (mkBox n.+1).(box) (¹ n.+1) D -> Type}
  (d: (mkBox p).(box) (↓ ↓ (Hpr ↕ Hrq ↕ Hq)) D)
  (c: mkcube E d) :=
  rew [mkCubePrev.(cube'')] (mkBox p).(cohbox) (Hrq := Hrq) d in
  C.(Cube).(subcube) (ε := ε) (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq)
    (mksubcube (ε := ω) (Hpq := (⇓ Hpr)) (Hq := ↓ (Hrq ↕ Hq)) E d c) =
  C.(Cube).(subcube) (ε := ω) (Hpq := (⇓ Hpr)) (Hq := ⇓ (Hrq ↕ Hq))
    (mksubcube (ε := ε) (Hpq := ↓ (Hpr ↕ Hrq)) (Hq := Hq) E d c).

(* The step case is discharged as (mkCohLayer; IHP) *)
Definition mkCohCube_step {p q r n} {ε ω: side} {C : Cubical n} {D: mkcsp}
  {Hpr: p.+3 <= r.+3} {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1}
  {E: (mkBox n.+1).(box) (¹ n.+1) D -> Type}
  {d: (mkBox p).(box) (↓ ↓ (↓ Hpr ↕ Hrq ↕ Hq)) D}
  {c: mkcube E d}
  {IHP: forall (d: (mkBox p.+1).(box) (↓ ↓ (Hpr ↕ Hrq ↕ Hq)) D) (c: mkcube E d),
        mkCohCube p.+1 Hpr (ε := ε) (ω := ω) d c}:
        mkCohCube p (↓ Hpr) (ε := ε) (ω := ω) d c.
  unfold mkCohCube in *; simpl projT1 in *; simpl projT2 in *.
  change (⇓ (↓ ?Hpr)) with (↓ (⇓ Hpr)).
  do 2 rewrite mksubcube_step_computes.
  destruct (rew [id] mkcube_computes in c) as (l, c'); clear c.
  rewrite (C.(eqSubcubeSp) (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq)).
  rewrite (C.(eqSubcubeSp) (Hpq := ⇓ Hpr) (Hq := ⇓ (Hrq ↕ Hq))).
  change ((fun _ (x : le' _ ?y) => x) ↕ ?z) with z.
  change (⇓ ?x ↕ ⇓ ?y) with (⇓ (x ↕ y)).
  rewrite <- rew_permute with (H := @eqCubeSp' _ _ _ (⇓ _) _)
                              (H' := (mkBox p).(cohbox) _).
  change (↓ ?Hpr ↕ ?Hrq) with (↓ (Hpr ↕ Hrq)).
  f_equal.
  unshelve eapply (rew_existT_curried (P := C.(Layer''))
  (Q := fun x => C.(CubePrev).(cube') (rew <- [id] C.(eqBoxSp') in x))
  (H := (mkBox p).(cohbox) (Hpr := ↓ Hpr) (Hrq := Hrq) (Hq := Hq) (ε := ε)
        (ω := ω) (D := D) d)
  (u := C.(SubLayer') (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq) (D := D.1) ε
          (mkSubLayer (Hpq := ⇓ Hpr) (Hq := ↓ (Hrq ↕ Hq)) (C := C) (D := D)
          (Box := mkBox p) (ε := ω) d l))
  (v := rew [C.(CubePrev).(cube')] C.(eqSubboxSp) in
    C.(Cube).(subcube) (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq) (ε := ε)
                       (D := D.1) (E := D.2)
                       (mksubcube (Hpq := ⇓ Hpr) (Hq := ↓ (Hrq ↕ Hq))
                       (D := D) (ε := ω) E (d; l) c'))).
  now exact (mkCohLayer (Hpr := Hpr) (Hrq := Hrq) (Hq := Hq) l).
  rewrite <- IHP with (d := (d; l)) (c := c').
  simpl (mkBox p.+1). unfold mkCubePrev, cube''.
  change (fun x => C.(CubePrev).(cube') (Hp := ?Hp) (D := ?D) x) with
    (C.(CubePrev).(cube') (Hp := Hp) (D := D)).
  unfold mkBoxSp; unfold cohbox at -1.
  rewrite rew_map with (f := fun x => rew <- [id] C.(eqBoxSp') in x).
  repeat rewrite rew_compose.
  set (FEQ := f_equal _ _); simpl in FEQ; clearbody FEQ.
  repeat rewrite <- eq_trans_assoc.
  now rewrite eq_trans_sym_inv_l, eq_trans_refl_r.
Qed.

(* Build a PartialCube n.+1 using what we just defined *)
#[local]
Instance mkCube {n} {C : Cubical n} : PartialCube n.+1 mkcsp mkCubePrev mkBox.
  unshelve esplit; intros p.
  - intros *; now exact mkcube.
  - intros q Hpq Hq ε d; now exact mksubcube.
  - intros *. revert d c. pattern p, Hpr. apply le_induction''.
    + now exact mkCohCube_base.
    + clear p Hpr; unfold mkCubePrev, subcube'; cbv beta iota;
      intros p Hpr IHP d c; invert_le Hpr; invert_le Hrq.
      now exact (mkCohCube_step (IHP := IHP)).
Defined.

#[local]
Instance mkCubical0: Cubical 0.
  unshelve esplit.
  - now exact unit.
  - unshelve esplit.
    * intros p Hp; now apply le_contra in Hp.
    * intros p Hp; now apply le_contra in Hp.
    * intros *; exfalso; now apply le_contra in Hq.
  - unshelve esplit.
    * intros Hp _; now exact unit.
    * intros *; exfalso; now apply le_contra in Hq.
    * intros *; exfalso; clear -Hq; now apply le_contra in Hq.
  - unshelve esplit; intros *.
    * exfalso; now apply le_contra in Hp.
    * exfalso; now apply le_contra in Hp.
    * exfalso; clear -Hq; now apply le_contra in Hq.
  - unshelve esplit.
    * unfold box. intros p Hp _ _ _; now exact unit.
    * simpl; intros *; exfalso; now apply le_contra in Hq.
    * simpl; intros *; exfalso; now apply le_contra in Hq.
  - now intros *.
  - intros *; exfalso; now apply le_contra in len1.
  - intros *; exfalso; now apply le_contra in Hp.
  - intros *; exfalso; now apply le_contra in Hp.
  - intros *; exfalso; clear -Hq; now apply le_contra in Hq.
  - intros *; exfalso; clear -Hp; now apply le_contra in Hp.
  - intros *; exfalso; clear -Hp; now apply le_contra in Hp.
  - intros *; exfalso; now apply le_contra in Hq.
  - intros *; exfalso; clear -Hp; now apply le_contra in Hp.
  - intros *; exfalso; clear -Hq; now apply le_contra in Hq.
Defined.

(* We are now ready to build a Cubical *)
#[local]
Instance mkCubicalSn {n} {C: Cubical n}: Cubical n.+1.
  unshelve esplit.
  - now exact mkcsp.
  - now exact mkBoxPrev.
  - now exact mkBox.
  - now exact mkCubePrev.
  - now exact mkCube.
  - now intros *.
  - intros *; now apply C.(eqBox0).
  - now intros *.
  - intros *; now refine C.(eqBoxSp).
  - now intros *.
  - intros *; simpl; now rewrite mkcube_computes.
  - intros *; now refine C.(eqCubeSp).
  - now intros *.
  - intros *; change (fun _ (_ : le' _ ?q) => _) with (¹ q); simpl.
    rewrite mksubcube_base_computes; rewrite eq_ind_r_refl.
    now rewrite rew_rew'.
  - intros *; simpl; rewrite eq_ind_r_refl; rewrite mksubcube_step_computes.
    now rewrite rew_rew'.
Defined.

Definition CubicalAt: forall n, Cubical n.
  induction n.
  - now exact mkCubical0.
  - now exact mkCubicalSn.
Defined.

CoInductive CubeUniverse n (X: (CubicalAt n).(csp)) : Type := cons {
  this : (CubicalAt n).(Box).(box) (¹ n) X -> Type@{l};
  next : CubeUniverse n.+1 (X; this)
}.

Definition CubeInfinity := CubeUniverse 0 tt.
