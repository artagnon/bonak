From Coq Require Import Arith.
Import Logic.EqNotations.
Require Import Logic.Eqdep.
Require Import Yoneda.
Import LeYoneda.
Require Import Aux.
Require Import RewLemmas.
Require Import Program.
Set Printing Projections.

Section Cubical.
Universe l'.
Universe l.

Inductive side := L | R.

(* PartialBox consists of an 0-cells, and fillers which are the 1-cells,
2-cells, and 3-cells relating the different 0-cells on the cube  *)
Record PartialBoxBase (n : nat) (csp : Type@{l'}) := {
  box' {p} (Hp : p.+1 <= n) : csp -> Type@{l} ;
  (* [box' n D] is [box (n-1) D.1] *)
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
  {ε : side} {ω : side} {D: csp} (d : box (↓ (⇓ Hpr ↕ (↓ (Hr ↕ Hq)))) D) :
  PB.(subbox') (Hp := Hpr ↕ Hr) Hq ε (subbox (Hp := ⇓ Hpr) (↓ (Hr ↕ Hq)) ω d) =
  (PB.(subbox') (Hp := Hpr) (Hr ↕ Hq) ω (subbox (Hp := ↓ (Hpr ↕ Hr)) Hq ε d));
}.

Arguments box {n p csp PB} _ Hp D.
Arguments subbox {n p csp PB} _ {q Hp} Hq ε {D}.
Arguments cohbox {n p csp PB} _ {q r Hpr Hr Hq ε ω D} d.

Record PartialCubeBase (n : nat) (csp : Type@{l'})
  (PB : PartialBoxBase n (@csp)) := {
  cube' {p} {Hp : p.+1 <= n} {D : csp} :
    PB.(box') Hp D -> Type@{l};
  cube'' {p} {Hp : p.+2 <= n} {D : csp} :
    PB.(box'') Hp D -> Type@{l};
  subcube' {p q} {Hp : p.+2 <= q.+2}
    (Hq : q.+2 <= n) (ε : side) {D : csp}
    {d : PB.(box') (↓ (Hp ↕ Hq)) D} :
    cube' d -> cube'' (PB.(subbox') Hq ε d) ;
}.

Arguments cube' {n csp PB} _ {p Hp} {D} d.
Arguments cube'' {n csp PB} _ {p Hp} {D} d.
Arguments subcube' {n csp PB} _ {p q Hp} Hq ε {D} [d] b.

(* Cube consists of cube, subcube, and coherence conditions between them *)
Record PartialCube (n : nat) (csp : Type@{l'}) {PB : PartialBoxBase n (@csp)}
  (PC : PartialCubeBase n csp PB)
  (Box : forall {p}, PartialBox n p (@csp) PB) := {
  cube {p} {Hp : p <= n} {D : csp} :
    (Box.(box) (le_refl n) D -> Type@{l}) -> Box.(box) Hp D -> Type@{l} ;
  subcube {p q} {Hp : p.+1 <= q.+1}
    (Hq : q.+1 <= n) (ε : side) {D : csp}
    {E : Box.(box) (le_refl n) D -> Type@{l}}
    {d : Box.(box) (↓ (Hp ↕ Hq)) D} (b : cube E d) :
    PC.(cube') (Box.(subbox) Hq ε d) ;
  cohcube {p q r} {Hpr : p.+2 <= r.+2}
    {Hr : r.+2 <= q.+2} {Hq : q.+2 <= n}
    (ε : side) (ω : side) {D : csp}
    (E : Box.(box) (le_refl n) D -> Type@{l})
    (d : Box.(box) (↓ (⇓ Hpr ↕ (↓ (Hr ↕ Hq)))) D) (b : cube E d) :
    rew (Box.(cohbox) d) in
    PC.(subcube') (Hp := Hpr ↕ Hr) Hq
    ε (subcube (Hp := ⇓ Hpr) (↓ (Hr ↕ Hq)) ω b) =
      (PC.(subcube') (Hp := Hpr) (Hr ↕ Hq)
      ω (subcube (Hp := ↓ (Hpr ↕ Hr)) Hq ε b));
}.

Arguments cube {n csp PB PC Box} _ {p Hp D} E.
Arguments subcube {n csp PB PC Box} _ {p q Hp} Hq ε {D} E [d] b.
Arguments cohcube {n csp PB PC Box} _ {p q r Hpr Hr Hq ε ω D E d} b.

(* Cube consists of cubesetprefix, a box built out of partial boxes,
  a cube built out of partial cubes *)
Class Cubical (n : nat) := {
  csp : Type@{l'} ;
  PB : PartialBoxBase n csp ;
  Box {p} : PartialBox n p csp PB ;
  PC : PartialCubeBase n csp PB ;
  Cube : PartialCube n csp PC (@Box) ;
  eqBox0 {len0: 0 <= n} {D : csp} : Box.(box) len0 D = unit ;
  eqBox0' {len1: 1 <= n} {D : csp} : PB.(box') len1 D = unit ;
  eqBoxSp {D : csp} {p} (Hp : p.+1 <= n) :
    Box.(box) Hp D = {d : Box.(box) (↓ Hp) D &
                  (PC.(cube') (Box.(subbox) (Hp := le_refl p.+1) _ L d) *
                  PC.(cube') (Box.(subbox) (Hp := le_refl p.+1) _ R d))%type } ;
  eqBoxSp' {D : csp} {p} (Hp : p.+2 <= n) :
    PB.(box') Hp D = {d : PB.(box') (↓ Hp) D &
                (PC.(cube'') (PB.(subbox') (Hp := le_refl p.+2) _ L d) *
                PC.(cube'') (PB.(subbox') (Hp := le_refl p.+2) _ R d))%type } ;
  eqSubbox0 {q} {Hp : 1 <= q.+1} (Hq : q.+1 <= n) (ε : side) (D : csp) :
    Box.(subbox) (Hp := Hp) Hq ε (rew <- [id] eqBox0 (D := D) in tt) =
      (rew <- [id] eqBox0' in tt) ;
  eqSubboxSn {ε p q} {D : csp} {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n}
    {d : Box.(box) (↓ ↓ (Hpq ↕ Hq)) D}
    {CL : PC.(cube') (Box.(subbox) (↓ (Hpq ↕ Hq)) L d)}
    {CR : PC.(cube') (Box.(subbox) (↓ (Hpq ↕ Hq)) R d)} :
    Box.(subbox) Hq ε
    (rew <- [id] eqBoxSp (↓ (Hpq ↕ Hq)) in (d; (CL, CR))) =
    (rew <- [id] eqBoxSp' (Hpq ↕ Hq) in (Box.(subbox) Hq ε d;
      (rew [PC.(cube'')] Box.(cohbox) (Hr := Hpq) d in
        PC.(subcube') Hq ε CL,
      rew [PC.(cube'')] Box.(cohbox) (Hr := Hpq) d in
        PC.(subcube') Hq ε CR))) ;
}.

Arguments csp {n} _.
Arguments PB {n} _.
Arguments PC {n} _.
Arguments Box {n} _ {p}.
Arguments Cube {n} _.
Arguments eqSubboxSn {n} _ {ε p q D Hpq Hq d CL CR}.

Definition mkcsp {n : nat} {C : Cubical n} : Type@{l'} :=
  { D : C.(csp) & C.(Box).(box) (le_refl n) D -> Type@{l} }.

Definition mkPB {n} {C : Cubical n} :
  PartialBoxBase n.+1 mkcsp := {|
  box' {p} {Hp : p.+1 <= n.+1} {D : mkcsp} := C.(Box).(box) (⇓ Hp) D.1 ;
  box'' {p} {Hp : p.+2 <= n.+1} {D : mkcsp} := C.(PB).(box') (⇓ Hp) D.1 ;
  subbox' {p q} {Hp : p.+2 <= q.+2} {Hq : q.+2 <= n.+1} {ε} {D : mkcsp} {d} :=
    C.(Box).(subbox) (Hp := ⇓ Hp) (⇓ Hq) ε d ;
|}.

Definition mkPC {n} {C : Cubical n} :
  PartialCubeBase n.+1 mkcsp mkPB := {|
  cube' {p} {Hp : p.+1 <= n.+1} {D : mkcsp} := C.(Cube).(cube) D.2 :
    mkPB.(box') Hp D -> Type; (* Bug? *)
  cube'' {p} {Hp : p.+2 <= n.+1} {D : mkcsp} {d : C.(PB).(box') _ D.1} :=
    C.(PC).(cube') d ;
  subcube' {p q} {Hp : p.+2 <= q.+2} {Hq : q.+2 <= n.+1} {ε} {D : mkcsp} {d}
    {b : C.(Cube).(cube) D.2 _} :=
    C.(Cube).(subcube) (Hp := ⇓ Hp) (⇓ Hq) ε D.2 b;
|}.

Definition mkBox {n} {C : Cubical n} p : PartialBox n.+1 p mkcsp mkPB.
  induction p as [|p (boxSn, subboxSn, cohboxSn)].
  + unshelve esplit.
  * intros Hp D; exact unit. (* p = O *)
  * simpl; intros. rewrite C.(@eqBox0 _); exact tt. (* subboxSn *)
  * simpl; intros. (* cohboxSn *)
    rewrite (eqSubbox0 (Hp := ⇓ Hpr)).
    rewrite (eqSubbox0 (Hp := ⇓ (Hpr ↕ Hr))); reflexivity.
  + unshelve esplit; (* p = S _ *)
    pose (Sub Hp side := (subboxSn p (le_refl p.+1) Hp side)).
    * intros Hp D. (* boxSn *)
      pose (Sub' side d := Sub Hp side D d).
      exact {d : boxSn (↓ Hp) D &
                 (C.(Cube).(cube) D.2 (Sub' L d) *
                  C.(Cube).(cube) D.2 (Sub' R d))%type }.
    * simpl. intros. destruct X as (d, (CL, CR)). (* subboxSn *)
      rewrite C.(@eqBoxSp _). destruct q. exfalso. clear -Hp.
      apply le_S_both in Hp. apply le_contra in Hp; assumption.
      unshelve esplit.
      - clear CL CR.
        exact (subboxSn q.+1 (↓ Hp) Hq ε _ d).
      - simpl in *; cbv zeta; unfold Sub. (* Sides L and R *)
        specialize cohboxSn with (Hpr := le_refl p.+2) (Hr := Hp) (Hq := Hq)
                                 (ε := ε) (D := D).
        change (le_refl p.+2 ↕ Hp) with Hp in cohboxSn.
        change (⇓ le_refl p.+2) with (le_refl p.+1) in cohboxSn.
        split.
        ++ specialize cohboxSn with (ω := L) (d := d). (* The side L *)
           rewrite <- cohboxSn.
           eapply (C.(Cube).(subcube) (Hp := ⇓ Hp)) with (Hq := ⇓ Hq) in CL.
           exact CL.
        ++ specialize cohboxSn with (ω := R) (d := d). (* The side R *)
           rewrite <- cohboxSn.
           eapply (C.(Cube).(subcube) (Hp := ⇓ Hp)) with (Hq := ⇓ Hq) in CR.
           exact CR.
    * simpl; intros. (* cohboxSn *)
      destruct d as (d', (CL, CR)); destruct r.
      exfalso. clear -Hpr. repeat apply le_S_both in Hpr. (* r = S O *)
      eapply le_contra.
      - eassumption.
      - destruct q. (* r = S (S _) *)
        exfalso. clear -Hr. repeat apply le_S_both in Hr. eapply le_contra.
        ++ eassumption.
        ++ rewrite <- le_trans_comm7. repeat rewrite eqSubboxSn. f_equal.
           simpl in cohboxSn. unshelve eapply eq_existT_curried.
           exact (cohboxSn _ _ (↓ Hpr) Hr Hq _ _ _ _).
           rewrite <- rew_pair. apply eq_pair.
        ** rewrite <- map_subst with (f := C.(PC).(subcube') (⇓ Hq) ε).
           rewrite <- map_subst with (f := C.(PC).(subcube') (⇓ (Hr ↕ Hq)) ω).
           eapply eq_trans.
           -- rewrite rew_map; apply rew_compose.
           -- eapply eq_trans.
           +++ rewrite rew_map with (f := C.(PB).(subbox') (⇓ Hq) ε).
               apply rew_compose.
           +++ rewrite rew_map with (f := C.(PB).(subbox') (⇓ (Hr ↕ Hq)) ω).
               rewrite rew_compose. apply rew_swap.
               rewrite <- (C.(Cube).(cohcube) (Hr := ⇓ Hr) (Hq := ⇓ Hq)).
               rewrite rew_compose, rew_app.
               *** reflexivity.
               *** apply UIP.
        ** rewrite <- map_subst with (f := C.(PC).(subcube') (⇓ Hq) ε).
           rewrite <- map_subst with (f := C.(PC).(subcube') (⇓ (Hr ↕ Hq)) ω).
           eapply eq_trans.
           -- rewrite rew_map; apply rew_compose.
           -- eapply eq_trans.
           +++ rewrite rew_map with (f := C.(PB).(subbox') (⇓ Hq) ε).
               apply rew_compose.
           +++ rewrite rew_map with (f := C.(PB).(subbox') (⇓ (Hr ↕ Hq)) ω).
               rewrite rew_compose. apply rew_swap.
               rewrite <- (C.(Cube).(cohcube) (Hr := ⇓ Hr) (Hq := ⇓ Hq)).
               rewrite rew_compose, rew_app.
               *** reflexivity.
               *** apply UIP.
Defined.

Definition mkCube {n} {C : Cubical n} : PartialCube n.+1 mkcsp mkPC mkBox.
  unshelve esplit.
  - intros p Hp. generalize Hp. revert C. assert (1 <= p). admit. (* cubeSn *)
    replace n with (n.+1 - p + p - 1).
    + induction (n.+1 - p).
      destruct p. exfalso. eapply le_contra. eassumption.
      simpl Nat.add. simpl Nat.sub. rewrite Nat.sub_0_r.
      * intros C Hp' D E. exact E.
      * intros. admit.
      + clear H. induction p.
      * simpl. rewrite Nat.sub_0_r, Nat.add_0_r. trivial. (* the p = 0 case *)
      * replace (n.+1 - p.+1) with (n - p) by auto. (* the p.+1 case *)
        rewrite Nat.add_comm, Nat.add_succ_comm, Nat.add_comm.
        rewrite <- Nat.sub_succ_l. apply IHp, le_S_down, Hp.
        pose proof (le_S_both Hp). unfold "<=" in H.
        specialize H with (1 := le_refl' p). clear Hp IHp.
        destruct (Compare_dec.le_dec p n). assumption.
        enough (H0: SFalse) by destruct H0. dependent induction H.
        destruct n0. constructor. apply IHle'. intro. apply n0. constructor.
        assumption.
      * admit. (* p <= n *)
  - intros p q. revert C. assert (1 <= p). admit. (* subcubeSn *)
    replace q with (q.+1 - p + p - 1).
    + induction (q.+1 - p).
      destruct p. exfalso. eapply le_contra. eassumption.
      simpl Nat.add. simpl Nat.sub.
      * intros C Hp D E. admit.
      * intros. admit.
    + admit.
  - admit.
Admitted.
End Cubical.
