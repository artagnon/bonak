From HoTT Require Import HoTT.
From HoTT Require Import peano_naturals.

Section Cubical.
Universe l'.
Universe l.

Theorem less_refl (n : nat): n <= n.
  apply Peano.le_n.
Qed.
Theorem less_pred (n : nat): pred n <= n.
Abort.

Record Cubical (n : nat) :=
{
  csp {n'} (Hn' : n' <= n) : Type@{l'} ;
  box {n' p} (Hn' : n' <= n) (Hp : p <= n) : csp Hn' -> Type@{l} ;
  layer {n' p} (Hn' : n' <= n) (Hp : p < n) : forall D, box Hn' Hp D -> Type@{l} ;
  cube {n' p} (Hn' : n' <= n) (Hp : p <= n) : forall D, box Hn' Hp D -> Type@{l} -> box Hn' Hp D -> Type@{l} ;
  subbox {n' p q} (Hn' : n' <= n) (Hq : q < n) (Hp : p <= q) : forall (D : csp Hn'), box Hn' Hp D.1 -> box Hn' Hp D ;
  sublayer {n' p} (Hn' : n' <= n) (Hp : p <= n) : forall (D : csp Hn'), box Hn' Hp D -> Type@{l} ;
  subcube {n' p} (Hn' : n' <= n) (Hp : p <= n) : forall (D : csp Hn'), (box Hn' Hp D -> Type@{l}) -> box Hn' Hp D ;
  cohbox {n' p} (Hn' : n' <= n) (Hp : p <= n) : forall (D : csp Hn'), box Hn' Hp D ;
  cohlayer {n' p} (Hn' : n' <= n) (Hp : p <= n) : forall (D : csp Hn'), box Hn' Hp D -> Type@{l} ;
  cohcube {n' p} (Hn' : n' <= n) (Hp : p <= n) : forall (D : csp Hn'), (box Hn' Hp D -> Type@{l}) -> Type@{l}
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
