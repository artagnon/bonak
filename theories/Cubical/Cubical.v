From Coq Require Import Arith.
Import Logic.EqNotations.
Require Import Yoneda.
Import LeYoneda.

Section Cubical.
Universe l'.
Universe l.

Inductive side := L | R.

Record Cubical {n : nat} :=
{
  csp {n'} (Hn' : n' <= n) : Type@{l'} ;
  hd {n'} {Hn' : S n' <= n} : csp Hn' -> csp (⇓ Hn') ;
  box {n' p} {Hn' : n' <= n} (Hp : p <= n') : csp Hn' -> Type@{l} ;
  tl {n'} {Hn' : S n' <= n} (D : csp Hn') :
    box (le_refl n') (hd D) -> Type@{l} ;
  layer {n' p} {Hn' : n' <= n} {Hp : p <= n'} {D : csp Hn'} :
    box Hp D -> Type@{l} ;
  cube {n' p} {Hn' : n' <= n} {Hp : p <= n'} {D : csp Hn'} :
    (box (le_refl n') D -> Type@{l}) -> box Hp D -> Type@{l} ;
  subbox {n' p q} {Hn' : S n' <= n} {Hp : p <= q} (Hq : q <= n')
    (ε : side) {D : csp Hn'} :
    box (Hp ↕ ↑ Hq) D -> box (Hp ↕ Hq) (hd D) ;
  sublayer {n' p q} {Hn' : S n' <= n} {Hp : p <= q} (Hq : q <= n')
    (ε : side) {D : csp Hn'} {d : box (Hp ↕ ↑ Hq) D} :
    layer d -> layer (Hp := Hp ↕ Hq)
    (subbox (Hp := Hp) Hq ε d) ;
  subcube {n' p q} {Hn' : S n' <= n} {Hp : p <= q}
    (Hq : q <= n') (ε : side) {D : csp Hn'}
    {E : box (le_refl (S n')) D -> Type@{l}}
    {d : box (Hp ↕ ↑ Hq) D} (b : cube E d) :
    cube (tl D) (subbox Hq ε d);
  cohbox {n' p q r} {Hn' : S (S n') <= n} {Hp : p <= r}
    {Hr : r <= q} {Hq : q <= n'} {ε : side} {ε' : side}
    {D : csp Hn'} (d : box (Hp ↕ (Hr ↕ ↑ ↑ Hq)) D) :
    subbox (Hp := Hp ↕ Hr) Hq ε
    (subbox (Hp := Hp) (Hr ↕ ↑ Hq) ε' d) =
    (subbox (Hp := Hp) (Hr ↕ Hq) ε'
    (subbox (Hp := Hp ↕ Hr) (↑ Hq) ε d));
  cohlayer {n' p q r} {Hn' : S (S n') <= n} {Hp : S p <= r}
    {Hr : r <= q} {Hq : q <= n'} (ε : side) (ε' : side)
    {D : csp Hn'} (d : box (Hp ↕ (Hr ↕ ↑ ↑ Hq)) D)
    (b : layer d) : rew (cohbox d) in
    (sublayer (Hp := Hp ↕ Hr) Hq ε
    (sublayer (Hp := Hp) (↑ (Hr ↕ Hq)) ε' b)) =
    sublayer (Hp := Hp) (Hr ↕ Hq) ε'
    (sublayer (Hp := Hp ↕ Hr) (↑ Hq) ε b);
  cohcube {n' p q r} {Hn' : S (S n') <= n} {Hp : p <= r}
    {Hr : r <= q} {Hq : q <= n'}
    (ε : side) (ε' : side) {D : csp Hn'}
    (E : box (le_refl (S (S n'))) D -> Type@{l})
    (d : box (Hp ↕ (Hr ↕ ↑ ↑ Hq)) D) (b : cube E d) :
    rew (cohbox d) in (subcube (Hp := Hp ↕ Hr) Hq ε
    (subcube (Hp := Hp) (↑ (Hr ↕ Hq)) ε' b)) =
    (subcube (Hp := Hp) (Hr ↕ Hq) ε'
    (subcube (Hp := Hp ↕ Hr) (↑ Hq) ε b))
}.

Notation "l '.1'" := (projT1 l) (at level 40).
Notation "l '.2'" := (projT2 l) (at level 40).

Fixpoint cubical {n : nat} : Cubical :=
  match n with
  | O => {| csp _ _ := unit;
    hd _ Hn' _ := ltac:(apply (le_discr Hn'));
    box _ _ _ _ _ := unit;
    tl _ Hn' _ _ := ltac:(apply (le_discr Hn'));
    layer _ _ Hn' Hp _ _ := unit;
    cube _ _ _ _ _ E d := E d;
    subbox _ _ _ Hn' _ _ _ _ _ := ltac:(apply (le_discr Hn'));
    sublayer _ _ _ Hn' Hp _ _ _ _  := ltac:(apply (le_discr Hn'));
    subcube _ _ _ Hn' _ _ _ _ _ _ _ := ltac:(apply (le_discr Hn'));
    cohbox _ _ _ _ Hn' _ _ _ _ _ _ _ := ltac:(apply (le_discr Hn'));
    cohlayer _ _ _ _ Hn' _ _ _ _ _ _ _ := ltac:(apply (le_discr Hn'));
    cohcube _ _ _ _ Hn' _ _ _ _ _ _ _ _ _ := ltac:(apply (le_discr Hn'));
    |}
  | S n => let cn := cubical (n := n) in

  (* Factor out the 0th and nth cases for reuse *)
  let cspn {_} Hn' := match le_dec Hn' with
  | left _ => { D : cn.(csp) _ & cn.(box) _ D -> Type@{l} }
  | right _ => cn.(csp) _
  end in
  let hdn {n'} Hn' := match (S n) with
  | S O => cn.(hd) _
  | _ =>
    match le_dec Hn' return cspn Hn' -> cspn (⇓ Hn') with
    | left _ => fun D => D.1
    | right _ => fun D => cn.(hd) D
    end
  end in
  let boxn {_ _ Hn'} Hp := match le_dec Hp return cspn Hn' -> Type@{l} with
  | left _ => fun D => cn.(box) _ D
  | right _ => fun D => cn.(box) _ D
  end in
  let tln {n'} Hn' := match (S n) with
  | S O => cn.(tl) _
  | _ =>
    match le_dec Hn' return boxn _ -> Type@{l} with
    | left _ => fun D => D.2
    | right _ => fun D => cn.(tl) D
    end
  end in

  (* Build the nth record *)
  {|
    csp _ Hn' := cspn Hn';
    hd _ Hn' := hdn Hn';
    box _ _ _ Hp := boxn Hp;
    tl _ Hn' := tln Hn';
  |}
end.

End Cubical.
