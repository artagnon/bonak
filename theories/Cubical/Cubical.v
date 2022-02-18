Import Logic.EqNotations.
Require Import Program. (* UIP *)
Require Import Aux.
Require Import RewLemmas.

Set Warnings "-notation-overridden".
Require Import Yoneda.

Set Printing Projections.
Set Primitive Projections.
Set Keyed Unification.
Remove Printing Let sigT.
Remove Printing Let prod.

Universe l'.
Universe l.

Inductive side := L | R.

(* PartialBox consists of an 0-cells, and fillers which are the 1-cells,
   2-cells, and 3-cells relating the different 0-cells on the cube. *)
Record PartialBoxPrev (n : nat) (csp : Type@{l'}) := { (* csp: CubeSetPrefix *)
  box' {p} (Hp : p.+1 <= n) : csp -> Type@{l} ;
  box'' {p} (Hp : p.+2 <= n) : csp -> Type@{l} ;
  subbox' {p q} {Hpq : p.+2 <= q.+2} (Hq : q.+2 <= n) (ε : side) {D : csp} :
    box' (↓ (Hpq ↕ Hq)) D -> box'' (Hpq ↕ Hq) D;
}.

Arguments box' {n csp} _ {p} Hp D.
Arguments box'' {n csp} _ {p} Hp D.
Arguments subbox' {n csp} _ {p q Hpq} Hq ε {D} d,
                  {n csp} _ {p q} Hpq Hq ε {D} d,
                  {n csp} _ {p q} Hpq Hq ε D d.

Record PartialBox (n p : nat) (csp : Type@{l'})
(BoxPrev : PartialBoxPrev n csp) := {
  box (Hp : p <= n) : csp -> Type@{l} ;
  subbox {q} {Hpq : p.+1 <= q.+1} (Hq : q.+1 <= n) (ε : side) {D : csp} :
    box (↓ (Hpq ↕ Hq)) D -> BoxPrev.(box') (Hpq ↕ Hq) D;
  cohbox {q r} {Hpr : p.+2 <= r.+2} {Hrq : r.+2 <= q.+2} {Hq : q.+2 <= n}
    {ε : side} {ω : side} {D: csp} (d : box (↓ (⇓ Hpr ↕ (↓ (Hrq ↕ Hq)))) D) :
    BoxPrev.(subbox') (Hpr ↕ Hrq) Hq ε (subbox (Hpq := ⇓ Hpr) (↓ (Hrq ↕ Hq)) ω d) =
    (BoxPrev.(subbox') Hpr (Hrq ↕ Hq) ω (subbox (Hpq := ↓ (Hpr ↕ Hrq)) Hq ε d));
}.

Arguments box {n p csp BoxPrev} _ Hp D.
Arguments subbox {n p csp BoxPrev} _ {q Hpq} Hq ε {D}.
Arguments cohbox {n p csp BoxPrev} _ {q r Hpr Hrq Hq ε ω D} d.

(* We build cubes using an iterated construction: a cube at level n depends
   on cubes at level n-1 and n-2; just as we have box' and box'', we have
   cube' and cube''. *)
Record PartialCubePrev (n : nat) (csp : Type@{l'})
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

Arguments cube' {n csp BoxPrev} _ {p Hp} {D} d.
Arguments cube'' {n csp BoxPrev} _ {p Hp} {D} d.
Arguments subcube' {n csp BoxPrev} _ {p q Hpq} Hq ε {D} [d] b.

(* Cube consists of cube, subcube, and coherence conditions between them *)
Record PartialCube (n : nat) (csp : Type@{l'})
  {BoxPrev : PartialBoxPrev n (@csp)}
  (CubePrev : PartialCubePrev n csp BoxPrev)
  (Box : forall {p}, PartialBox n p (@csp) BoxPrev) := {
  cube {p} {Hp : p <= n} {D : csp} :
    (Box.(box) (le_refl n) D -> Type@{l}) -> Box.(box) Hp D -> Type@{l} ;
  subcube {p q} {Hp : p.+1 <= q.+1}
    (Hq : q.+1 <= n) (ε : side) {D : csp}
    {E : Box.(box) (le_refl n) D -> Type@{l}}
    {d : Box.(box) (↓ (Hp ↕ Hq)) D} (c : cube E d) :
    CubePrev.(cube') (Box.(subbox) Hq ε d) ;
  cohcube {p q r} {Hpr : p.+2 <= r.+2}
    {Hrq : r.+2 <= q.+2} {Hq : q.+2 <= n}
    (ε : side) (ω : side) {D : csp}
    (E : Box.(box) (le_refl n) D -> Type@{l})
    (d : Box.(box) (↓ (⇓ Hpr ↕ (↓ (Hrq ↕ Hq)))) D) (c : cube E d) :
    rew (Box.(cohbox) d) in
    CubePrev.(subcube') (Hpq := Hpr ↕ Hrq) Hq
    ε (subcube (Hp := ⇓ Hpr) (↓ (Hrq ↕ Hq)) ω c) =
      (CubePrev.(subcube') (Hpq := Hpr) (Hrq ↕ Hq)
      ω (subcube (Hp := ↓ (Hpr ↕ Hrq)) Hq ε c));
}.

Arguments cube {n csp BoxPrev CubePrev Box} _ {p Hp D} E.
Arguments subcube {n csp BoxPrev CubePrev Box} _ {p q Hp Hq ε D E} [d] c.
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

  (* A few abbreviations *)
  Layer' {p} {Hp : p.+1 <= n} {D: csp} (d: Box.(box) (↓ Hp) D) :=
    (CubePrev.(cube') (Box.(subbox) Hp L d) *
     CubePrev.(cube') (Box.(subbox) Hp R d))%type ;
  Layer'' {p} {Hp : p.+2 <= n} {D: csp} (d: BoxPrev.(box') (↓ Hp) D) :=
    (CubePrev.(cube'') (BoxPrev.(subbox') Hp L d) *
     CubePrev.(cube'') (BoxPrev.(subbox') Hp R d))%type;
  SubLayer' {p q ε} {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n} {D: csp}
    (d: Box.(box) (↓ ↓ (Hpq ↕ Hq)) D) (c: Layer' d) :=
    (rew Box.(cohbox) (Hrq := Hpq) d in CubePrev.(subcube') Hq ε (fst c),
      rew Box.(cohbox) (Hrq := Hpq) d in CubePrev.(subcube') Hq ε (snd c)) ;

  eqBox0 {len0: 0 <= n} {D : csp} : Box.(box) len0 D = unit ;
  eqBox0' {len1: 1 <= n} {D : csp} : BoxPrev.(box') len1 D = unit ;
  eqBoxSp {p} {Hp : p.+1 <= n} {D : csp} :
    Box.(box) Hp D = {d : Box.(box) (↓ Hp) D & Layer' d};
  eqBoxSp' {p} {Hp : p.+2 <= n} {D : csp} :
    BoxPrev.(box') Hp D = {d : BoxPrev.(box') (↓ Hp) D & Layer'' d } ;
  eqSubbox0 {q} {Hpq : 1 <= q.+1} {Hq : q.+1 <= n} {ε : side} {D : csp} :
    Box.(subbox) (Hpq := Hpq) Hq ε (rew <- [id] eqBox0 (D := D) in tt) =
      (rew <- [id] eqBox0' in tt) ;
  eqSubboxSn {ε p q} {D : csp} {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n}
    {d: Box.(box) (↓ ↓ (Hpq ↕ Hq)) D}
    {c: Layer' (Hp := ↓ (Hpq ↕ Hq)) d} :
    Box.(subbox) Hq ε (rew <- [id] eqBoxSp in (d; c)) =
      rew <- [id] eqBoxSp' in (Box.(subbox) Hq ε d; SubLayer' d c) ;
  eqCubeSn {p} {Hp : p.+1 <= n} {D : csp} {E d} :
    Cube.(cube) (Hp := ↓ Hp) E d = {c : Layer' d &
      Cube.(cube) (D := D) E (rew <- [id] eqBoxSp in (d; c))} ;
  eqCubeSn' {p} {Hp : p.+2 <= n} {D : csp} {d} :
    CubePrev.(cube') (Hp := ↓ Hp) d = {b : Layer'' d &
      CubePrev.(cube') (rew <- [id] eqBoxSp' (D := D) in (d; b))} ;
  eqSubcube0 {p} {Hp: p.+1 <= n} {D: csp} {E} {d} {ε : side}
    {l: Layer' d}
    {Q: Cube.(cube) (D := D) E (rew <- eqBoxSp in (d; l))} :
      match ε with
      | L => fst l
      | R => snd l
      end = Cube.(subcube) (Hq := Hp) (rew <- [id] eqCubeSn in (l; Q)) ;
  eqSubcubeSn {p q} {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n} {D : csp} {E} {d}
    {ε: side}
    {l: Layer' (Hp := ↓ (Hpq ↕ Hq)) d}
    {Q: Cube.(cube) (D := D) E (rew <- eqBoxSp in (d; l))} :
    Cube.(subcube) (Hp := ↓ Hpq) (ε := ε) (rew <- [id] eqCubeSn in (l; Q)) = rew <- [id] eqCubeSn' (Hp := Hpq ↕ Hq) in
      (SubLayer' d l; rew [CubePrev.(cube')] eqSubboxSn in Cube.(subcube) Q) ;
}.

Arguments csp {n} _.
Arguments BoxPrev {n} _.
Arguments CubePrev {n} _.
Arguments Box {n} _ {p}.
Arguments Cube {n} _.
Arguments Layer' {n} _ {p Hp D} d.
Arguments Layer'' {n} _ {p Hp D} d.
Arguments SubLayer' {n} _ {p q ε Hpq Hq D d} c.
Arguments eqBox0 {n} _ {len0 D}.
Arguments eqBox0' {n} _ {len1 D}.
Arguments eqBoxSp {n} _ {p Hp D}.
Arguments eqBoxSp' {n} _ {p Hp D}.
Arguments eqSubbox0 {n} _ {q Hpq Hq ε D}.
Arguments eqSubboxSn {n} _ {ε p q D Hpq Hq d c}.
Arguments eqCubeSn {n} _ {p Hp D E d}.
Arguments eqCubeSn' {n} _ {p Hp D d}.
Arguments eqSubcube0 {n} _ {p Hp D E d ε l Q}.
Arguments eqSubcubeSn {n} _ {p q Hpq Hq D E d ε l Q}.

Definition mkcsp {n} {C : Cubical n} : Type@{l'} :=
  { D : C.(csp) & C.(Box).(box) (le_refl n) D -> Type@{l} }.

Definition mkBoxPrev {n} {C : Cubical n} :
  PartialBoxPrev n.+1 mkcsp := {|
  box' (p : nat) (Hp : p.+1 <= n.+1) (D : mkcsp) := C.(Box).(box) (⇓ Hp) D.1 ;
  box'' (p : nat) (Hp : p.+2 <= n.+1) (D : mkcsp) :=
    C.(BoxPrev).(box') (⇓ Hp) D.1 ;
  subbox' (p q : nat) (Hpq : p.+2 <= q.+2) (Hq : q.+2 <= n.+1) (ε : side)
    (D : mkcsp) (d : _) :=
    C.(Box).(subbox) (Hpq := ⇓ Hpq) (⇓ Hq) ε d ;
|}.

Definition mkCubePrev {n} {C: Cubical n} :
  PartialCubePrev n.+1 mkcsp mkBoxPrev := {|
  cube' (p : nat) (Hp : p.+1 <= n.+1) (D : mkcsp) := C.(Cube).(cube) D.2 :
    mkBoxPrev.(box') Hp D -> Type; (* Bug? *)
  cube'' (p : nat) (Hp : p.+2 <= n.+1) (D : mkcsp)
    (d : mkBoxPrev.(box'') Hp D) :=
    C.(CubePrev).(cube') d;
  subcube' (p q : nat) (Hpq : p.+2 <= q.+2) (Hq : q.+2 <= n.+1) (ε : side)
    (D : mkcsp) (d : _) (b : _) := C.(Cube).(subcube) (Hp := ⇓ Hpq)
    (Hq := ⇓ Hq) (E := D.2) b;
|}.

Definition mkLayer {n p} {Hp: p.+1 <= n.+1} {C: Cubical n} {D: mkcsp}
  {Box: PartialBox n.+1 p mkcsp mkBoxPrev} {d: Box.(box) (↓ Hp) D}: Type :=
  (C.(Cube).(cube) D.2 (Box.(subbox) (Hpq := le_refl _) Hp L d) *
   C.(Cube).(cube) D.2 (Box.(subbox) (Hpq := le_refl _) Hp R d))%type.

Definition mkSubLayer {n p q} {ε: side} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n.+1}
  {C: Cubical n} {D: mkcsp} {Box: PartialBox n.+1 p mkcsp mkBoxPrev}
  {d: Box.(box) (↓ ↓ (Hpq ↕ Hq)) D}
  {c: mkLayer}: C.(Layer') (Box.(subbox) Hq ε d) :=
  let Rx (x: {ω: side & C.(Cube).(cube) D.2 (Box.(subbox) _ ω _)}) :=
    rew Box.(cohbox) (ε := ε) (ω := x.1) (Hrq := Hpq) d in
      (C.(Cube).(subcube) (Hp := ⇓ Hpq) x.2) in
  (Rx (L; (fst c)), Rx (R; (snd c))).

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
  {d: Box.(box) (↓ ↓ ↓ (Hpr ↕ Hrq ↕ Hq)) D} {c: mkLayer}:
  let sl :=
    C.(SubLayer') (ε := ε) (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq)
        (mkSubLayer (ε := ω) (Hpq := ⇓ Hpr) (d := d) (c := c)) in
  let sl' :=
    C.(SubLayer') (ε := ω) (Hpq := ⇓ Hpr) (Hq := ⇓ (Hrq ↕ Hq))
        (mkSubLayer (ε := ε) (Hpq := ↓ (Hpr ↕ Hrq)) (d := d) (c := c)) in
  rew [C.(Layer'')] cohBoxSnHyp (Hrq := Hrq) in sl = sl'.
Proof.
  simpl; rewrite <- rew_pair; apply eq_pair;
  rewrite <- map_subst with (f := C.(CubePrev).(subcube') (⇓ Hq) ε);
  rewrite <- map_subst with (f := C.(CubePrev).(subcube') (⇓ (Hrq ↕ Hq)) ω);
  rewrite rew_map; eapply eq_trans.
  1, 3: now apply rew_compose.
  all:  eapply eq_trans.
  1, 3: rewrite rew_map with (f := C.(BoxPrev).(subbox') (⇓ Hq) ε);
        now apply rew_compose.
  all:  rewrite rew_map with (f := C.(BoxPrev).(subbox') (⇓ (Hrq ↕ Hq)) ω),
        rew_compose; apply rew_swap;
        rewrite <- (C.(Cube).(cohcube) (Hrq := ⇓ Hrq) (Hq := ⇓ Hq));
        rewrite rew_compose, rew_app.
  1, 3: now reflexivity.
  all:  now apply UIP.
Defined.

Definition mkBox0 {n} {C: Cubical n} : PartialBox n.+1 O mkcsp mkBoxPrev.
  unshelve esplit.
  * intros Hp D; exact unit. (* boxSn *)
  * simpl; intros. rewrite C.(eqBox0); exact tt. (* subboxSn *)
  * simpl; intros. (* cohboxp *)
    now rewrite eqSubbox0 with (Hpq := ⇓ Hpr),
                eqSubbox0 with (Hpq := ⇓ (Hpr ↕ Hrq)).
Defined.

Definition mkBoxSp {n p} {C: Cubical n}
  {Box: PartialBox n.+1 p mkcsp mkBoxPrev}:
  PartialBox n.+1 p.+1 mkcsp mkBoxPrev.
  unshelve esplit.
  * intros Hp D. (* boxSn *)
    exact {d : Box.(box) (↓ Hp) D & mkLayer (d := d)}.
  * simpl; intros * ε * (d, c). (* subboxSn *)
    rewrite C.(eqBoxSp); invert_le Hpq.
    now exact (Box.(subbox) Hq ε d; mkSubLayer (c := c)).
  * simpl; intros. (* cohboxp *)
    destruct d as (d, c); invert_le Hpr; invert_le Hrq.
    repeat rewrite eqSubboxSn.
    f_equal. apply eq_existT_uncurried.
    now exact (cohBoxSnHyp; mkCohLayer).
Defined.

Definition mkBox {n} {C: Cubical n} p : PartialBox n.+1 p mkcsp mkBoxPrev.
  induction p.
  + now apply mkBox0. (* p = O *)
  + now apply (mkBoxSp (Box := IHp)). (* p = S _ *)
Defined.

Definition mkcube {n} {C: Cubical n}: forall {p} (Hp : p <= n.+1) (D : mkcsp),
((mkBox n.+1).(box) (le_refl n.+1) D -> Type) -> (mkBox p).(box) Hp D -> Type.
  intros p Hp D E; apply le_induction with (H := Hp); clear p Hp. (* cubeSn *)
  + now exact E. (* n = p *)
  + intros p Hp IH d.  (* p = S n *)
    exact {b :
        (C.(Cube).(cube) D.2 ((mkBox p).(subbox) Hp L d) *
        C.(Cube).(cube) D.2 ((mkBox p).(subbox) Hp R d))%type
        & IH (d; b)}.
Defined.

Lemma mkcube_computes {q n} {C : Cubical n} {Hq : q.+1 <= n.+1} {D E d} :
  mkcube (↓ Hq) D E d = {l :
        (C.(Cube).(cube) D.2 ((mkBox q).(subbox) _ L d) *
        C.(Cube).(cube) D.2 ((mkBox q).(subbox) _ R d))%type
        & mkcube Hq D E (d; l)}.
Proof.
  unfold mkcube; now rewrite le_induction_computes.
Defined.

Definition mksubcube {n} {C: Cubical n} {p q} (Hp : p.+1 <= q.+1)
  (Hq: q.+1 <= n.+1) (ε : side) {D}
  (E : (mkBox n.+1).(box) (le_refl n.+1) D -> Type)
  (d : (mkBox p).(box) (↓ (Hp ↕ Hq)) D) :
  mkcube (↓ (Hp ↕ Hq)) D E d -> mkCubePrev.(cube') ((mkBox p).(subbox) Hq ε d).
Proof.
  intros *. revert d. (* subcubeSn *)
  simpl.
  pattern p, Hp. (* Bug? Why is this needed? *)
  apply le_induction'.
  + intros d c. rewrite mkcube_computes in c. destruct c as (l, _).
    destruct ε. now exact (fst l). now exact (snd l).
  + clear p Hp. intros p Hp IH d c. rewrite mkcube_computes in c.
    destruct c as (l, d').
    change (⇓ (↓ ?Hp ↕ ?Hq)) with (↓ ⇓ (Hp ↕ Hq)). (* This shouldn't be
                                                    necessary: rewrite
                                                    should support SProp. *)
    rewrite C.(eqCubeSn); invert_le Hp.
    unshelve esplit.
    * change (C.(Box).(subbox) (⇓ (Hp ↕ Hq)) ?ω _) with
              (mkBoxPrev.(subbox') (le_refl p.+2) (Hp ↕ Hq) ω
                ((mkBox p).(subbox) Hq ε d)).
      change (le_refl _ ↕ ?H) with H. split;
      rewrite <- ((mkBox p).(cohbox) (q := q) (r := p) (Hrq := Hp) (Hpr := (le_refl p.+2)));
      eapply (C.(Cube).(subcube) (Hp := ⇓ Hp) (Hq := ⇓ Hq) (E := D.2)).
      now exact (fst l). now exact (snd l).
    * apply IH in d'. now exact d'.
Defined.

Lemma mksubcube_base_computes {q r n} {C : Cubical n} {Hq : q.+2 <= n.+1}
  {Hrq : r.+2 <= q.+2} {ω : side} {D E} {d: (mkBox r).(box) _ D} {c} :
  mksubcube (le_refl r.+1) (↓ (Hrq ↕ Hq)) ω E d c =
  match (rew [id] mkcube_computes in c) with
  | (l; _) => match ω with
    | L => fst l
    | R => snd l
    end
  end.
Proof.
  unfold mksubcube; now rewrite le_induction'_base_computes.
Qed.

Lemma mksubcube_step_computes {q r n} {C : Cubical n} {Hq : q.+2 <= n.+1}
  {Hrq : r.+2 <= q.+2} {ω : side} {D E} {d: (mkBox r).(box) _ D} {c} :
  mksubcube (↓ Hrq) Hq ω E d c =
  match (rew [id] mkcube_computes in c) with
  | (l; c) => rew <- [id] C.(eqCubeSn) in
    ((rew (mkBox r).(cohbox) (r := r) d in
      C.(Cube).(subcube) (Hq := ⇓ Hq) (ε := ω) (E := D.2) (fst l),
      rew (mkBox r).(cohbox) (r := r) d in
      C.(Cube).(subcube) (Hq := ⇓ Hq) (ε := ω) (E := D.2) (snd l));
    mksubcube Hrq _ ω E (d; l) c)
  end.
Proof.
  unfold mksubcube; now rewrite le_induction'_step_computes.
Qed.

Definition mkCube {n} {C : Cubical n} : PartialCube n.+1 mkcsp mkCubePrev mkBox.
  unshelve esplit.
  - intros p; now exact mkcube.
  - intros p q; now exact mksubcube.
  -  intros *. revert d c. pattern p, Hpr. apply le_induction''.
    + change (le_refl _ ↕ ?H) with H; change (⇓ le_refl _ ↕ ?H) with H.
      change (⇓ le_refl ?r.+2) with (le_refl r.+1); intros d c.
      rewrite mksubcube_base_computes, mksubcube_step_computes.
      destruct (rew [id] mkcube_computes in c) as (l, c'); clear c; destruct ω.
      now refine (C.(eqSubcube0) (ε := L) (Q := mksubcube Hrq Hq _ _ (_; _) _)).
      now refine (C.(eqSubcube0) (ε := R) (Q := mksubcube Hrq Hq _ _ (_; _) _)).
    + clear p Hpr; unfold mkCubePrev, subcube'; cbv beta iota;
      intros p Hpr IHP d c; invert_le Hpr; invert_le Hrq.
      change (⇓ (↓ ?Hpr)) with (↓ (⇓ Hpr)).
      do 2 rewrite mksubcube_step_computes.
      destruct (rew [id] mkcube_computes in c) as (l, c'); clear c.
      rewrite (C.(eqSubcubeSn) (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq)).
      rewrite (C.(eqSubcubeSn) (Hpq := ⇓ Hpr) (Hq := ⇓ (Hrq ↕ Hq))).
      change ((fun _ (x : le' _ ?y) => x) ↕ ?z) with z.
      change (⇓ ?x ↕ ⇓ ?y) with (⇓ (x ↕ y)).
      rewrite <- rew_permute with (H := @eqCubeSn' _ _ _ (⇓ _) _)
                                  (H' := (mkBox p).(cohbox) _).
      change (↓ ?Hpr ↕ ?Hrq) with (↓ (Hpr ↕ Hrq)).
      rewrite <- IHP with (d := (d; l)) (c := c').
      f_equal; rewrite rew_triple; simpl projT1; simpl projT2.
      unshelve eapply eq_existT_curried.
      now rewrite mkCohLayer.
      Arguments cohbox {n p csp BoxPrev} _ {q r Hpr Hrq Hq} ε ω {D} d.
      Notation "'rew' [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
            (at level 10, H' at level 10,
            format "'[' 'rew'  [ P ]  '/    ' H  in  '/' H' ']'").
      Notation "'rew' <- [ P ] H 'in' H'" := (eq_rect_r P H' H)
            (at level 10, H' at level 10,
            format "'[' 'rew'  <-  [ P ]  '/    ' H  in  '/' H' ']'").
      unfold cube'', mkBoxPrev, box', box'', subbox'. admit.
Admitted.
