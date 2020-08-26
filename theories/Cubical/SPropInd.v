Module LeSPropInd <: Le.

Inductive le' (n:nat) : nat -> SProp :=
  | le_refl : n <= n
  | le_S_up : forall {m:nat}, n <= m -> n <= S m
  where "n <= m" := (le' n m) : nat_scope.

Definition le := le'.

Arguments le_S_up {n m}.

Notation "↑ h" := (le_S_up h) (at level 40).

(* No loss of information: primitive *)
Theorem le_trans {p q n} : p <= q -> q <= n -> p <= n.
  intros G H.
  induction H as [|r].
  - exact G.
  - apply le_S_up; exact IHle'.
Defined.

Infix "↕" := le_trans (at level 30).

(* Re-prove le_S_n *)

Theorem le_adjust {p n} : S p <= S n -> p <= n.
  intros G.
  change n with (pred (S n)).
  induction G.
  - apply le_refl.
  - destruct m.
    * assumption.
    * apply (↑ IHG).
Defined.

Definition le_S_down {p n} (Hp : S p <= n) : p <= n := le_adjust (↑ Hp).

Notation "⇓ p" := (le_S_down p) (at level 40).

End LeSPropInd.