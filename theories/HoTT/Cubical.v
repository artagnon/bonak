From HoTT Require Import HoTT.
From HoTT Require Import peano_naturals.

Section Cubical.
Universe l'.
Universe l.

Theorem LP {n n' : nat} : n' <= n -> pred n' <= n.
Admitted.

Record Cubical (n : nat) :=
{
  csp {n'} (Hn' : n' <= n) : Type@{l'} ;
  hd {n'} {Hn' : n' <= n} : csp Hn' -> csp (LP Hn') ;
  box {n' p} {Hn' : n' <= n} (Hp : p <= n) : csp Hn' -> Type@{l} ;
  layer {n' p} {Hn' : n' <= n} {Hp : p < n} : forall {D : csp Hn'}, box Hp D -> Type@{l} ;
  cube {n' p} {Hn' : n' <= n} {Hp : p <= n} : forall {D : csp Hn'}, box Hp D -> Type@{l} -> box Hp D -> Type@{l} ;
  subbox {n' p q} {Hn' : n' <= n} {Hp : p <= n} (Hq : q < n) : forall {D : csp Hn'}, box Hp D -> box Hp (hd D) ;
  sublayer {n' p q} {Hn' : n' <= n} {Hp : p <= n} (Hq : q < n) : forall {D : csp Hn'} (d : box Hp D), layer d -> layer (subbox Hq d) ;
  subcube {n' p q} {Hn' : n' <= n} {Hp : p <= n} (Hq : q < n) : forall {D : csp Hn'}, (box Hp D -> Type@{l}) -> box Hp D ;
  cohbox {n' p q r} {Hn' : n' <= n} {Hp : p <= n} (Hq : q < n) (Hr : r < n) : forall {D : csp Hn'}, box Hp D ;
  cohlayer {n' p q r} {Hn' : n' <= n} {Hp : p < n} (Hq : q < n) (Hr : r < n) : forall {D : csp Hn'}, box Hp D -> Type@{l} ;
  cohcube {n' p q r} {Hn' : n' <= n} {Hp : p <= n} (Hq : q < n) (Hr : r < n) : forall {D : csp Hn'}, (box Hp D -> Type@{l}) -> Type@{l}
}.

Fixpoint cubsetprefix (n : nat) : Cubical n :=
match n with
  | O => {| csp := unit; box := ; cube := fun ...; subbox := ; cohbox := |}
  | S n => { D : cubsetprefix (S n) & (mkBox n n D) -> Type@{l} }
end

with Box := mkBox {
  n : nat ;
  p : nat ;
  constr_np : n <=? p
}.

mkBox n p (p <= n) (D : cubsetprefix n) : Type@{l}.
mkBox n D : unit.
mkBox {n + 1, p + 1} D

Argument {n : nat} {p : nat} {q : nat} {r : nat}.

Definition layer (n + 1) p : Type@{l} := c.(cube) (n + 1) p D

Fixpoint CubeS m' (c : Cubical m') n (H n < S m') p (H p : p <= n) ('(D, E) : csp (S n) (d : box ...):=
match (n - p) with
  | O => E(d)
  | S n' => {| csp := cspS m' c n H ; box :=  |}
  end.
End Section Cubical.
