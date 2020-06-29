From HoTT Require Import HoTT.
From HoTT Require Import peano_naturals.

Section Cubical.
Universe l'.
Universe l.

Inductive le (n:nat) : nat -> SProp :=
  | le_n : n <= n
  | le_S : forall m:nat, n <= m -> n <= S m
  where "n <= m" := (le n m).

Definition lt (n m:nat) := S n <= m.
Infix "<" := lt.

(* Constructor *)
Definition le_weaken {p n} : p <= n -> p <= S n := le_S p n.

(* Re-prove le_S_n *)
Theorem le_adjust {p n} : S p <= S n -> p <= n.
  intros G.
  change n with (pred (S n)).
  induction G.
  - apply le_n.
  - destruct m.
    * assumption.
    * apply (le_weaken IHG).
Defined.

(* Eval cbn in fun p n (H : p < S n) => (le_adjust (le_weaken H)). *)

(* No loss of information: primitive *)
Theorem trans {p q n} : p <= q -> q <= n -> p <= n.
  intros G H.
  induction H as [|r].
  - exact G.
  - apply le_weaken; exact IHle.
Defined.

Definition weaken_trans {p q n} (Hp : p <= q) (Hq : q <= n) :
  p <= S n :=
  le_weaken (trans Hp Hq).

Definition adjust_weaken {p n} (Hp : p < n) : p <= n := le_adjust (le_weaken Hp).

Theorem le_pqn_trans_weak_right {p q n} : p <= n -> n < q -> p <= q.
  intros G H.
  induction H as [|s].
  - apply le_weaken; exact G.
  - apply le_weaken; exact IHle.
Defined.

Theorem le_pqrn_trans {p q r n} (Hp : p <= r)
  (Hr : r < q) (Hq : q <= n) : p <= S n.
  eapply weaken_trans.
  2: exact Hq.
  eapply le_pqn_trans_weak_right.
  - exact Hp.
  - exact Hr.
Defined.

Theorem trans_weak_composite {p q r n} (Hp : p <= q) (Hr: q < r)
  (Hq : r <= S n) (Hp' : p <= r)
  Hq' : trans (le_pqn_trans_weak_right Hp Hr) Hq =
  trans Hp' (le_weaken Hq').
Admitted.

Record Cubical (n : nat) :=
{
  csp {n'} (Hn' : n' <= n) : Type@{l'} ;
  hd {n'} {Hn' : n' < n} : csp Hn' -> csp (adjust_weaken Hn') ;
  box {n' p} {Hn' : n' <= n} (Hp : p <= n') :
      csp Hn' -> Type@{l} ;
  tl {n'} {Hn' : S n' <= n} : forall (D : csp Hn'),
     box (le_n n') (hd D) -> Type@{l} ;
  layer {n' p} {Hn' : n' <= n} {Hp : p < n'} :
        forall {D : csp Hn'}, box (adjust_weaken Hp) D -> Type@{l} ;
  cube {n' p} {Hn' : n' <= n} {Hp : p <= n'} :
       forall {D : csp Hn'},
       (box (le_n n') D -> Type@{l}) -> box Hp D -> Type@{l} ;
  subbox {n' p q} {Hn' : S n' <= n} {Hp : p <= q} (Hq : q <= n') :
         forall {D : csp Hn'}, box (weaken_trans Hp Hq) D ->
         box (trans Hp Hq) (hd D) ;
  sublayer {n' p q} {Hn' : S n' <= n} {Hp : p < q} (Hq : q <= n') :
           forall {D : csp Hn'}
           (d : box (adjust_weaken (weaken_trans Hp Hq)) D),
           layer d -> layer (subbox Hq d) ;
  subcube {n' p q} {Hn' : S n' <= n} {Hp : p <= q}
          (Hq : q <= n') :
          forall {D : csp Hn'} (E : box (le_n (S n')) D -> Type@{l})
          (d : box (weaken_trans Hp Hq) D) (b : cube E d),
          cube (tl D) (subbox Hq d);
  cohbox {n' p q r} {Hn' : S (S n') <= n} {Hp : p <= r}
         (Hr : r < q) (Hq : q <= S n') :
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
