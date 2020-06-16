From HoTT Require Import HoTT.
From HoTT Require Import peano_naturals.

Section Cubical.
Universe l'.
Universe l.

Theorem LP {n n' : nat} : n' <= n -> pred n' <= n.
Admitted.

Theorem le_n: forall n, n <= n.
Admitted.

Theorem le_pred_weak {p n} : p <= pred n -> p <= n.
Admitted.

Lemma lt_succ {q n} : q < n -> q < S n.
Admitted.

Theorem le_pqn_trans {p q n} : p <= q -> q < n -> p <= pred n.
Admitted.

Definition le_pqn_trans_weak {p q n} (Hp : p <= q) (Hq : q < n) :=
  le_pqn_trans Hp (lt_succ Hq).

Theorem lt_weak {p n} : p < n -> p <= n.
Admitted.

Definition le_pqrn_trans {p q r n} (Hp : p <= r)
  (Hr : r < q) (Hq : q < n) :=
  le_pqn_trans_weak (le_pqn_trans_weak Hp Hr) Hq.

Record Cubical (n : nat) :=
{
  csp {n'} (Hn' : n' <= n) : Type@{l'} ;
  hd {n'} {Hn' : n' < n} : csp (lt_weak Hn') -> csp Hn' ;
  box {n' p} {Hn' : n' <= n} (Hp : p <= n') :
      csp Hn' -> Type@{l} ;
  tl {n'} {Hn' : n' < n} : forall (D : csp (lt_weak Hn')),
     box _ (hd D) -> Type@{l} ;
  layer {n' p} {Hn' : n' <= n} {Hp : p < n'} :
        forall {D : csp Hn'}, box Hp D -> Type@{l} ;
  cube {n' p} {Hn' : n' <= n} {Hp : p <= n'} :
       forall {D : csp Hn'},
       (box (le_n n') D -> Type@{l}) -> box Hp D -> Type@{l} ;
  subbox {n' p q} {Hn' : n' < n} {Hp : p <= q} (Hq : q <= n') :
         forall {D : csp (lt_weak Hn')},
         box (le_pqn_trans_weak Hp Hq) D ->
         @box n' p (lt_weak Hn') (le_pqn_trans_weak Hp Hq) (hd D) ;
  sublayer {n' p q} {Hn' : n' <= n} {Hp : p < q} (Hq : q < n') :
           forall {D : csp Hn'}
           (d : box (le_pqn_trans_weak (lt_weak Hp) Hq) D),
           layer d -> layer (subbox Hq d) ;
  subcube {n' p q} {Hn' : n' <= n} {Hp : p <= q}
          (Hq : q < n') :
          forall {D : csp Hn'} (E : box (le_n n') D -> Type@{l})
          (d : box (le_pqn_trans_weak Hp Hq) D) (b : cube E d),
          cube (tl D) (subbox Hq d);
  cohbox {n' p q r} {Hn' : n' <= n} {Hp : p <= r}
         (Hr : r < q) (Hq : q < n') :
         forall {D : csp Hn'} (d : box (le_pqrn_trans Hp Hr Hq) D),
         subbox _ (subbox _ d) = subbox _ (subbox _ d);
  cohlayer {n' p q r} {Hn' : n' <= n} {Hp : p < r}
           (Hr : r < q) (Hq : q < n') :
           forall {D : csp Hn'} (d : box (le_pqrn_trans Hp Hr Hq) D),
           Type@{l} ;
  cohcube {n' p q r} {Hn' : n' <= n} {Hp : p <= r}
          (Hr : r < q) (Hq : q < n') :
          forall {D : csp Hn'} (d : box (le_pqrn_trans Hp Hr Hq) D),
          Type@{l}
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
