Module LeSPropRec <: Le.

Inductive sFalse : SProp :=.
Inductive sTrue : SProp := sI.

Fixpoint le m n : SProp :=
  match m with
  | 0 => sTrue
  | S m =>
    match n with
    | 0 => sFalse
    | S n => le m n
    end
  end.

Definition le0 n : le 0 n := sI.
Definition leS m n l : le m n := l.

Fixpoint le_rect
  (P : forall m n : nat, (le m n) -> Type)
  (f0 : forall n : nat, P 0 n (le0 n))
  (fS : forall (m n : nat) (l : le m n),
           (P m n l) -> P (S m) (S n) (leS m n l))
  (m n : nat) : forall (l : le m n), P m n l :=
  match m with
  | 0 => fun _ => f0 n
  | S m =>
    match n with
    | 0 => sFalse_rect _
    | S n => fun l => fS m n l (le_rect P f0 fS m n l)
    end
  end.

End LeSPropRec.

