From HoTT Require Import HoTT.
From HoTT Require Import peano_naturals.

Section Cubical.
Universe l'.
Universe l.

Inductive le (n:nat) : nat -> SProp :=
  | le_n : n <= n
  | le_S : forall {m:nat}, n <= m -> n <= S m
  where "n <= m" := (le n m).

Arguments le_S {n m}.

Definition lt (n m:nat) := S n <= m.
Infix "<" := lt.

Theorem le_n_S : forall n m, n <= m -> S n <= S m.
Admitted.

(* Constructor *)
Notation "↑ h" := (le_S h) (at level 40).

(* Re-prove le_S_n *)
Theorem le_adjust {p n} : S p <= S n -> p <= n.
  intros G.
  change n with (pred (S n)).
  induction G.
  - apply le_n.
  - destruct m.
    * assumption.
    * apply (↑ IHG).
Defined.

(* No loss of information: primitive *)
Theorem trans {p q n} : p <= q -> q <= n -> p <= n.
  intros G H.
  induction H as [|r].
  - exact G.
  - apply le_S; exact IHle.
Defined.

Infix "↕" := trans (at level 30).

Definition weaken_trans {p q n} (Hp : p <= q) (Hq : q <= n) :
  p <= S n :=
  ↑ (Hp ↕ Hq).

Definition adjust_weaken {p n} (Hp : p < n) : p <= n := le_adjust (↑ Hp).

Notation "⇓ p" := (adjust_weaken p) (at level 40).

Theorem le_pqrn_trans {p q r n} (Hp : p <= r)
  (Hr : r <= q) (Hq : q <= n) : p <= S (S n).
  apply le_S.
  eapply weaken_trans.
  2: apply Hq.
  eapply trans.
  - exact Hp.
  - exact Hr.
Defined.

Inductive side := L | R.

Record Cubical (n : nat) :=
{
  csp {n'} (Hn' : n' <= n) : Type@{l'} ;
  hd {n'} {Hn' : S n' <= n} : csp Hn' -> csp (⇓ Hn') ;
  box {n' p} {Hn' : n' <= n} (Hp : p <= n') : csp Hn' -> Type@{l} ;
  tl {n'} {Hn' : S n' <= n} (D : csp Hn') :
    box (le_n n') (hd D) -> Type@{l} ;
  layer {n' p} {Hn' : n' <= n} {Hp : p < n'} {D : csp Hn'} :
    box (⇓ Hp) D -> Type@{l} ;
  cube {n' p} {Hn' : n' <= n} {Hp : p <= n'} {D : csp Hn'} :
    (box (le_n n') D -> Type@{l}) -> box Hp D -> Type@{l} ;
  subbox {n' p q} {Hn' : S n' <= n} {Hp : p <= q} (Hq : q <= n')
    (ε : side) {D : csp Hn'} :
    box (↑ (Hp ↕ Hq)) D -> box (Hp ↕ Hq) (hd D) ;
  sublayer {n' p q} {Hn' : S n' <= n} {Hp : p < q} (Hq : q <= n')
    (ε : side) {D : csp Hn'} {d : box (⇓ (↑ (Hp ↕ Hq))) D} :
    layer d -> layer (Hp := Hp ↕ Hq)
    (subbox (Hp := (⇓ Hp)) Hq ε d) ;
  subcube {n' p q} {Hn' : S n' <= n} {Hp : p <= q}
    (Hq : q <= n') (ε : side) {D : csp Hn'}
    {E : box (le_n (S n')) D -> Type@{l}}
    {d : box (↑ (Hp ↕ Hq)) D} (b : cube E d) :
    cube (tl D) (subbox Hq ε d);
  cohbox {n' p q r} {Hn' : S (S n') <= n} {Hp : p <= r}
    {Hr : r <= q} {Hq : q <= n'} {ε : side} {ε' : side}
    {D : csp Hn'} (d : box (le_pqrn_trans Hp Hr Hq) D) :
    subbox (Hp := Hp ↕ Hr) Hq ε
    (subbox (Hp := Hp) (↑ (Hr ↕ Hq)) ε' d) =
    subbox (Hp := Hp) (Hr ↕ Hq) ε'
    (subbox (Hp := Hp ↕ Hr) (↑ Hq) ε d);
  cohlayer {n' p q r} {Hn' : S (S n') <= n} {Hp : S p <= r}
    {Hr : r <= q} {Hq : q <= n'} (ε : side) (ε' : side)
    {D : csp Hn'} (d : box (le_pqrn_trans (⇓ Hp) Hr Hq) D)
    (b : layer (Hp := le_pqrn_trans Hp Hr Hq) d) :
    (cohbox d) # (sublayer (Hp := Hp ↕ Hr) Hq ε
    (sublayer (Hp := Hp) (↑ (Hr ↕ Hq)) ε' b)) =
    sublayer (Hp := Hp) (Hr ↕ Hq) ε' (sublayer (↑ Hq) ε b);
  cohcube {n' p q r} {Hn' : S (S n') <= n} {Hp : p <= r}
    {Hr : r <= q} {Hq : q <= n'}
    (ε : side) (ε' : side) {D : csp Hn'}
    (E : box (le_n (S (S n'))) D -> Type@{l})
    (d : box (le_pqrn_trans Hp Hr Hq) D) (b : cube E d) :
    (cohbox d) # (subcube (Hp := Hp ↕ Hr) Hq ε (subcube
    (Hp := Hp) (↑ (Hr ↕ Hq)) ε' b)) =
    (subcube (Hp := Hp) (Hr ↕ Hq) ε' (subcube (↑ Hq) ε b))
}.

Fixpoint cubical (n : nat) : Cubical n :=
match n with
  | O => {| csp _ _ := unit;
    hd _ Hn' _ := ltac:(inversion Hn');
    box _ _ _ _ _ := Unit;
    tl _ Hn' _ _ := ltac:(inversion Hn');
    layer _ _ _ Hp _ _ := ltac:(inversion Hp);
    cube _ _ _ _ _ _ E d := E(d);
    subbox _ _ _ _ _ _ _ _ _ := tt;
    sublayer _ _ _ _ Hp _ _ _ _ _ := ltac:(inversion Hp);
    subcube _ _ _ Hn' _ _ _ _ _ _ _ := ltac:(inversion Hn');
    cohbox _ _ _ _ Hn' _ _ _ _ _ _ _ := ltac:(inversion Hn');
    cohlayer _ _ _ _ Hn' _ _ _ _ _ _ _ := ltac:(inversion Hn');
    cohcube _ _ _ _ Hn' _ _ _ _ _ _ _ _ _ := ltac:(inversion Hn');
    |}
  | S n => { D : cubsetprefix (S n) & (mkBox n n D) -> Type@{l} }
end.

End Section Cubical.
