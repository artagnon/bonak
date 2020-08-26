From Coq Require Import Arith.
Import Logic.EqNotations.

Section Cubical.
Universe l'.
Universe l.

Inductive side := L | R.

Notation "'uniq'" := (le_unique _ _ _ _) (at level 80).

Record Cubical {n : nat} :=
{
  csp {n'} (Hn' : n' <= n) : Type@{l'} ;
  hd {n'} {Hn' : S n' <= n} : csp Hn' -> csp (⇓ Hn') ;
  box {n' p} {Hn' : n' <= n} (Hp : p <= n') : csp Hn' -> Type@{l} ;
  tl {n'} {Hn' : S n' <= n} (D : csp Hn') :
    box (le_n n') (hd D) -> Type@{l} ;
  layer {n' p} {Hn' : n' <= n} {Hp : p <= n'} {D : csp Hn'} :
    box Hp D -> Type@{l} ;
  cube {n' p} {Hn' : n' <= n} {Hp : p <= n'} {D : csp Hn'} :
    (box (le_n n') D -> Type@{l}) -> box Hp D -> Type@{l} ;
  subbox {n' p q} {Hn' : S n' <= n} {Hp : p <= q} (Hq : q <= n')
    (ε : side) {D : csp Hn'} :
    box (Hp ↕ ↑ Hq) D -> box (Hp ↕ Hq) (hd D) ;
  sublayer {n' p q} {Hn' : S n' <= n} {Hp : p <= q} (Hq : q <= n')
    (ε : side) {D : csp Hn'} {d : box (↑ (Hp ↕ Hq)) D} :
    layer (rew uniq in d) -> layer (Hp := Hp ↕ Hq)
    (rew uniq in subbox Hq ε (rew uniq in d)) ;
  subcube {n' p q} {Hn' : S n' <= n} {Hp : p <= q}
    (Hq : q <= n') (ε : side) {D : csp Hn'}
    {E : box (le_n (S n')) D -> Type@{l}}
    {d : box (Hp ↕ ↑ Hq) D} (b : cube E d) :
    cube (tl D) (subbox Hq ε d);
  cohbox {n' p q r} {Hn' : S (S n') <= n} {Hp : p <= r}
    {Hr : r <= q} {Hq : q <= n'} {ε : side} {ε' : side}
    {D : csp Hn'} (d : box (Hp ↕ (Hr ↕ ↑ ↑ Hq)) D) :
    subbox (Hp := Hp ↕ Hr) Hq ε
    (subbox (Hp := Hp) (↑ (Hr ↕ Hq)) ε' d) =
    (rew uniq in subbox (Hp := Hp) (Hr ↕ Hq) ε'
    (rew uniq in subbox (Hp := Hp ↕ Hr) (↑ Hq) ε (rew uniq in d)));
  cohlayer {n' p q r} {Hn' : S (S n') <= n} {Hp : S p <= r}
    {Hr : r <= q} {Hq : q <= n'} (ε : side) (ε' : side)
    {D : csp Hn'} (d : box (Hp ↕ (Hr ↕ ↑ ↑ Hq)) D)
    (b : layer (rew uniq in d)) : rew (cohbox d) in
    (sublayer (Hp := Hp ↕ Hr) Hq ε
    (rew uniq in sublayer (Hp := Hp) (↑ (Hr ↕ Hq)) ε' b)) =
    sublayer (Hp := Hp) (Hr ↕ Hq) ε'
    (sublayer (Hp := Hp ↕ Hr) (↑ Hq) ε (rew uniq in b));
  cohcube {n' p q r} {Hn' : S (S n') <= n} {Hp : p <= r}
    {Hr : r <= q} {Hq : q <= n'}
    (ε : side) (ε' : side) {D : csp Hn'}
    (E : box (le_n (S (S n'))) D -> Type@{l})
    (d : box (Hp ↕ (Hr ↕ ↑ ↑ Hq)) D) (b : cube E d) :
    rew (cohbox d) in (subcube (Hp := Hp ↕ Hr) Hq ε
    (subcube (Hp := Hp) (↑ (Hr ↕ Hq)) ε' b)) =
    (subcube (Hp := Hp) (Hr ↕ Hq) ε'
    (subcube (Hp := Hp ↕ Hr) (↑ Hq) ε b))
}.

Inductive mysum (A:Type) (B:SProp) := inl : A -> mysum A B | inr : B -> mysum A B.
Axiom le_dec : forall {n m}, n <= S m -> mysum (n = S m) (n <= m).

Fixpoint cubical {n : nat} : Cubical :=
match n with
  | O => {| csp _ _ := Unit;
    hd _ Hn' _ := ltac:(inversion Hn');
    box _ _ _ _ _ := Unit;
    tl _ Hn' _ _ := ltac:(inversion Hn');
    layer _ _ Hn' Hp _ _ := ltac:(inversion (trans Hp Hn'));
    cube _ _ _ _ _ E d := E d;
    subbox _ _ _ _ _ _ _ _ _ := tt;
    sublayer _ _ _ Hn' Hp _ _ _ _  := ltac:(inversion Hn');
    subcube _ _ _ Hn' _ _ _ _ _ _ _ := ltac:(inversion Hn');
    cohbox _ _ _ _ Hn' _ _ _ _ _ _ _ := ltac:(inversion Hn');
    cohlayer _ _ _ _ Hn' _ _ _ _ _ _ _ := ltac:(inversion Hn');
    cohcube _ _ _ _ Hn' _ _ _ _ _ _ _ _ _ := ltac:(inversion Hn');
    |}
  | S n => let cn := cubical (n := n) in
  let cspn {n'} (Hn':n' <= S n) := match le_dec Hn' return Type with
    | inl _ => { D : cn.(csp) _ & box cn Hn' D -> Type@{l} }
    | inr Hn' => cn.(csp) Hn'
    end in
    let hd {n'} (Hn':S n' <= S n) := match le_dec Hn' as x return match x return Type with
    | inl _ => { D : cn.(csp) (le_n n) & cn.(box) (le_n n) D -> Type@{l} }
    | inr Hn' => cn.(csp) Hn'
    end -> (*match x return Type with
    | inl _ => cn.(csp) (le_n n)
    | inr Hn' => *)cn.(csp) _
    (*end *)with
    | inl _ => fun D => D.1
    | inr Hn' => fun D => cn.(hd) D
    end in
    {| csp n' Hn' := cspn Hn';
    hd n' Hn' := hd Hn';
    tl {n'} Hn' := match Hn' with
    | le_n => fun D => D.2
    | le_S n' Hn' => fun D => cn.(tl) Hn'
    end;
    layer n' p Hn' Hp D d := (cn.(cube) (tl D)
    (cn.(subbox) L Hp d) * cube cn (cn.(tl) D) (cn.(subbox) R Hp d))%type
    |}
end.

End Section Cubical.
