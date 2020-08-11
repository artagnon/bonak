From HoTT Require Import HoTT.
From HoTT Require Import peano_naturals.
From HoTT Require Import Spaces.Nat.

Section Cubical.
Universe l'.
Universe l.

Inductive le (n:nat) : nat -> SProp :=
  | le_n : n <= n
  | le_S : forall {m:nat}, n <= m -> n <= S m
  where "n <= m" := (le n m).

  Inductive leT (n:nat) : nat -> Type :=
  | leT_n : leT n n
  | leT_S : forall {m:nat}, leT n m -> leT n (S m).

  Axiom le_leT : forall {n m}, n <= m -> leT n m.

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

Record Cubical {n : nat} :=
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

Set Printing All.

Axiom foo : forall {n}, S n <= 0 -> False.
Fixpoint cubical {n : nat} : Cubical :=
match n with
  | O => {| csp _ _ := Unit;
    hd _ Hn' _ := ltac:(destruct (foo Hn'));
    box _ _ _ _ _ := Unit;
    tl _ Hn' _ _ := ltac:(destruct (foo Hn'));
    layer _ _ Hn' Hp _ _ := ltac:(destruct (foo (trans Hp Hn')));
    cube _ _ _ _ _ E d := E d;
    subbox _ _ _ _ _ _ _ _ _ := tt;
    sublayer _ _ _ Hn' Hp _ _ _ _  := ltac:(destruct (foo Hn'));
    subcube _ _ _ Hn' _ _ _ _ _ _ _ := ltac:(destruct (foo Hn'));
    cohbox _ _ _ _ Hn' _ _ _ _ _ _ _ := ltac:(destruct (foo Hn'));
    cohlayer _ _ _ _ Hn' _ _ _ _ _ _ _ := ltac:(destruct (foo Hn'));
    cohcube _ _ _ _ Hn' _ _ _ _ _ _ _ _ _ := ltac:(destruct (foo Hn'));
    |}
  | S n => let cn := cubical (n := n) in
    let cspn {n'} (Hn':n'<=S n) := match le_leT Hn' in leT _ q return q = S n -> Type with
    | leT_n => fun _ => { D : cn.(csp) _ & box cn Hn' D -> Type@{l} }
    | leT_S n Hn' => fun eq => cn.(csp) (eq # Hn')
    end idpath in

    {| csp := @cspn;
    hd {n'} (Hn':S n'<=S n) := match le_leT Hn' in leT _ q return forall eq:q = S n, cspn Hn' -> cspn (⇓ (eq # Hn')) with
    | leT_n => fun _ D => D.1
    | leT_S n Hn' => fun eq D => cn.(hd) (eq # Hn')
    end idpath;
    tl {n'} Hn' := match Hn' with
    | le_n => fun D => D.2
    | le_S n' Hn' => fun D => cn.(tl) Hn'
    end;
    layer n' p Hn' Hp D d := (cn.(cube) (tl D)
    (cn.(subbox) L Hp d) * cube cn (cn.(tl) D) (cn.(subbox) R Hp d))%type
    |}
end.

End Section Cubical.
