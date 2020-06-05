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
  csp : forall n', n' <= n, Type@{l'} ;
  box : forall n', n' <= n,forall p, p <= n -> csp -> Type@{l} ;
  cube : forall n', n' <= n, forall p (Hp : p <= n), forall D, (box p Hp D -> Type@{l}) -> box p Hp D -> Type@{l} ;
  layer : forall n', n' <= n, forall p (Hp : p <= n), forall D, box p Hp D -> Type@{l} ;
  subbox : forall n', n' <= n, forall q (Hq : q < n), forall p (Hp : p <= q), forall D, csp -> box p D.1 -> box (n - 1) p ;
  sublayer : forall n', n' <= n, forall p (Hp : p <= n), forall D, csp -> box p Hp D -> Type@{l} ;
  subcube : forall n', n' <= n, forall p (Hp : p <= n), forall D, csp -> (box p Hp D -> Type@{l}) -> box p Hp D ;
  cohbox : forall n', n' <= n, forall p (Hp : p <= n), forall D, csp -> box p Hp D ;
  cohlayer : forall n', n' <= n, forall p (Hp : p <= n), forall D, box p Hp D -> Type@{l} ;
  cohcube : forall n', n' <= n, forall p (Hp : p <= n), forall D, (box p Hp D -> Type@{l}) -> Type@{l}
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
