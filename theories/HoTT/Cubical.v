From HoTT Require Import HoTT.

Section Cubical.
Universe l.

Record Cubical@{l} n :=
{
  csp : Type@{l + 1} ;
  box : forall p, p <= n -> csp -> Type@{l} ;
  cube : forall p (Hp : p <= n), forall D, (box p Hp D -> Type@{l}) -> box p Hp D -> Type@{l} ;
  layer : forall p (Hp : p <= n), forall D, box p Hp D -> Type@{l} ;
  subbox : forall p, p <= n -> csp -> Type@{l} ;
  sublayer : csp -> box p Hp D -> layer
  subcube : forall p (Hp : p <= n), forall D, D -> (box p Hp D -> Type@{l}) -> box p Hp D
  cohbox : forall p (Hp : p <= n), forall D, D -> box p Hp D
  cohlayer : forall p (Hp : p <= n), forall D, box p Hp D -> layer D d
  cohcube : forall p (Hp : p <= n), forall D, (box p Hp D -> Type@{l}) -> Type@{l}
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
