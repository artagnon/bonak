From HoTT Require Import HoTT.

Section Cubical.
Universe l.

Record Cubical m :=
{
  csp : forall n, n <= m -> Type@{l + 1} ;
  box : forall n, (n <= m), forall p, p <= n -> (D : cubsetprefix (n + 1)) -> Type@{l} ;
  cube : forall n, n < m, forall p, p <= n -> (D : cubsetprefix (n + 1)) -> Type@{l} ;
  subbox : forall n, n < m, forall p, p <= n -> (D : cubsetprefix (n + 1)) -> Type@{l} ;
  cohbox :
}.

Fixpoint cubsetprefix (n : nat) : Type@{l + 1} :=
match (S n) with
  | S O => unit
  | n => { D : cubsetprefix (S n) & (mkBox n n D) -> Type@{l} }
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
