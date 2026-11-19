From Bonak.Lib Require Export Logic.
From Bonak.Lib Require Import Tactics EqDec.

Module Number.
Declare ML Module "rocq-runtime.plugins.number_string_notation".

Module Decimal.
  Inductive uint: Set :=
  | Nil
  | D0 (_: uint)
  | D1 (_: uint)
  | D2 (_: uint)
  | D3 (_: uint)
  | D4 (_: uint)
  | D5 (_: uint)
  | D6 (_: uint)
  | D7 (_: uint)
  | D8 (_: uint)
  | D9 (_: uint).

  Variant int: Set := Pos (d: uint) | Neg (d: uint).

  Variant decimal: Set :=
  | Decimal (i: int) (f: uint)
  | DecimalExp (i: int) (f: uint) (e: int).

  Register uint as num.uint.type.
  Register int as num.int.type.
  Register decimal as num.decimal.type.

  Fixpoint revapp (d d': uint): uint :=
    match d with
    | Nil => d'
    | D0 d => revapp d (D0 d')
    | D1 d => revapp d (D1 d')
    | D2 d => revapp d (D2 d')
    | D3 d => revapp d (D3 d')
    | D4 d => revapp d (D4 d')
    | D5 d => revapp d (D5 d')
    | D6 d => revapp d (D6 d')
    | D7 d => revapp d (D7 d')
    | D8 d => revapp d (D8 d')
    | D9 d => revapp d (D9 d')
    end.

  Definition rev (d: uint): uint := revapp d Nil.

  Fixpoint succ (d: uint): uint :=
    match d with
    | Nil => D1 Nil
    | D0 d => D1 d
    | D1 d => D2 d
    | D2 d => D3 d
    | D3 d => D4 d
    | D4 d => D5 d
    | D5 d => D6 d
    | D6 d => D7 d
    | D7 d => D8 d
    | D8 d => D9 d
    | D9 d => D0 (succ d)
    end.
End Decimal.

Module Hexadecimal.
  Inductive uint: Set :=
  | Nil
  | D0 (_: uint)
  | D1 (_: uint)
  | D2 (_: uint)
  | D3 (_: uint)
  | D4 (_: uint)
  | D5 (_: uint)
  | D6 (_: uint)
  | D7 (_: uint)
  | D8 (_: uint)
  | D9 (_: uint)
  | Da (_: uint)
  | Db (_: uint)
  | Dc (_: uint)
  | Dd (_: uint)
  | De (_: uint)
  | Df (_: uint).

  Variant int: Set := Pos (d: uint) | Neg (d: uint).

  Variant hexadecimal: Set :=
  | Hexadecimal (i: int) (f: uint)
  | HexadecimalExp (i: int) (f: uint) (e: Decimal.int).

  Register uint as num.hexadecimal_uint.type.
  Register int as num.hexadecimal_int.type.
  Register hexadecimal as num.hexadecimal.type.
End Hexadecimal.

Variant uint: Set :=
| UIntDecimal (u: Decimal.uint)
| UIntHexadecimal (u: Hexadecimal.uint).

Variant int: Set :=
| IntDecimal (i: Decimal.int)
| IntHexadecimal (i: Hexadecimal.int).

Variant number: Set :=
| Decimal (d: Decimal.decimal)
| Hexadecimal (h: Hexadecimal.hexadecimal).

Register uint as num.num_uint.type.
Register int as num.num_int.type.
Register number as num.number.type.

End Number.

Definition pred (n: nat): nat :=
  match n with
  | O => n
  | S u => u
  end.

Register pred as num.nat.pred.

Fixpoint add (n m: nat): nat :=
  match n with
  | O => m
  | S p => S (add p m)
  end.

Register add as num.nat.add.

Fixpoint sub (n m: nat): nat :=
  match n with
  | O => n
  | S k => match m with
           | O => n
           | S l => sub k l
           end
  end.

Register sub as num.nat.sub.

Fixpoint eqb (n m: nat): bool :=
  match n with
  | O => match m with
         | O => true
         | S _ => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Definition eq_dec (n m: nat): (n = m) + (n <> m).
Proof.
  revert m. induction n as [|n IHn]; intros [|m].
  - left. reflexivity.
  - right. intro H. discriminate H.
  - right. intro H. discriminate H.
  - destruct (IHn m) as [e|ne].
    + left. exact (f_equal S e).
    + right. intro H. exact (ne (f_equal pred H)).
Defined.

Fixpoint tail_add (n m: nat): nat :=
  match n with
  | O => m
  | S n => tail_add n (S m)
  end.

Fixpoint tail_addmul (r n m: nat): nat :=
  match n with
  | O => r
  | S n => tail_addmul (tail_add m r) n m
  end.

Definition tail_mul (n m: nat): nat := tail_addmul O n m.

Local Abbreviation S2 n := (S (S n)).
Local Abbreviation S4 n := (S2 (S2 n)).
Local Abbreviation S8 n := (S4 (S4 n)).
Local Abbreviation ten := (S8 (S2 O)).
Local Abbreviation sixteen := (S8 (S8 O)).

Fixpoint of_uint_acc (d: Number.Decimal.uint) (acc: nat): nat :=
  match d with
  | Number.Decimal.Nil => acc
  | Number.Decimal.D0 d => of_uint_acc d (tail_mul ten acc)
  | Number.Decimal.D1 d => of_uint_acc d (S (tail_mul ten acc))
  | Number.Decimal.D2 d => of_uint_acc d (S2 (tail_mul ten acc))
  | Number.Decimal.D3 d => of_uint_acc d (S (S2 (tail_mul ten acc)))
  | Number.Decimal.D4 d => of_uint_acc d (S4 (tail_mul ten acc))
  | Number.Decimal.D5 d => of_uint_acc d (S (S4 (tail_mul ten acc)))
  | Number.Decimal.D6 d => of_uint_acc d (S2 (S4 (tail_mul ten acc)))
  | Number.Decimal.D7 d => of_uint_acc d (S (S2 (S4 (tail_mul ten acc))))
  | Number.Decimal.D8 d => of_uint_acc d (S8 (tail_mul ten acc))
  | Number.Decimal.D9 d => of_uint_acc d (S (S8 (tail_mul ten acc)))
  end.

Definition of_uint (d: Number.Decimal.uint): nat := of_uint_acc d O.

Fixpoint of_hex_uint_acc (d: Number.Hexadecimal.uint) (acc: nat): nat :=
  match d with
  | Number.Hexadecimal.Nil => acc
  | Number.Hexadecimal.D0 d => of_hex_uint_acc d (tail_mul sixteen acc)
  | Number.Hexadecimal.D1 d => of_hex_uint_acc d (S (tail_mul sixteen acc))
  | Number.Hexadecimal.D2 d => of_hex_uint_acc d (S2 (tail_mul sixteen acc))
  | Number.Hexadecimal.D3 d =>
    of_hex_uint_acc d (S (S2 (tail_mul sixteen acc)))
  | Number.Hexadecimal.D4 d => of_hex_uint_acc d (S4 (tail_mul sixteen acc))
  | Number.Hexadecimal.D5 d =>
    of_hex_uint_acc d (S (S4 (tail_mul sixteen acc)))
  | Number.Hexadecimal.D6 d =>
    of_hex_uint_acc d (S2 (S4 (tail_mul sixteen acc)))
  | Number.Hexadecimal.D7 d =>
    of_hex_uint_acc d (S (S2 (S4 (tail_mul sixteen acc))))
  | Number.Hexadecimal.D8 d => of_hex_uint_acc d (S8 (tail_mul sixteen acc))
  | Number.Hexadecimal.D9 d =>
    of_hex_uint_acc d (S (S8 (tail_mul sixteen acc)))
  | Number.Hexadecimal.Da d =>
    of_hex_uint_acc d (S2 (S8 (tail_mul sixteen acc)))
  | Number.Hexadecimal.Db d =>
    of_hex_uint_acc d (S (S2 (S8 (tail_mul sixteen acc))))
  | Number.Hexadecimal.Dc d =>
    of_hex_uint_acc d (S4 (S8 (tail_mul sixteen acc)))
  | Number.Hexadecimal.Dd d =>
    of_hex_uint_acc d (S (S4 (S8 (tail_mul sixteen acc))))
  | Number.Hexadecimal.De d =>
    of_hex_uint_acc d (S2 (S4 (S8 (tail_mul sixteen acc))))
  | Number.Hexadecimal.Df d =>
    of_hex_uint_acc d (S (S2 (S4 (S8 (tail_mul sixteen acc)))))
  end.

Definition of_hex_uint (d: Number.Hexadecimal.uint): nat :=
  of_hex_uint_acc d O.

Definition of_num_uint (d: Number.uint): nat :=
  match d with
  | Number.UIntDecimal d => of_uint d
  | Number.UIntHexadecimal d => of_hex_uint d
  end.

Fixpoint to_little_uint (n: nat) (acc: Number.Decimal.uint):
  Number.Decimal.uint :=
  match n with
  | O => acc
  | S n => to_little_uint n (Number.Decimal.succ acc)
  end.

Definition to_uint (n: nat): Number.Decimal.uint :=
  Number.Decimal.rev (to_little_uint n (Number.Decimal.D0 Number.Decimal.Nil)).

Definition to_num_uint (n: nat): Number.uint :=
  Number.UIntDecimal (to_uint n).

Notation "x .+1" := (S x) (at level 1, left associativity, format "x .+1").
Notation "x .+2" := (S (S x)) (at level 1, left associativity, format "x .+2").
Notation "x .+3" := (S (S (S x)))
  (at level 1, left associativity, format "x .+3").

Number Notation nat of_num_uint to_num_uint (abstract after 5000):
  nat_scope.

Open Scope nat_scope.

Infix "+" := add: nat_scope.
Infix "-" := sub: nat_scope.

Definition f_equal_nat := f_equal (A := nat).

#[global] Hint Resolve f_equal_nat: core.

(** Addition *)

Lemma plus_n_O: forall n: nat, n = n + 0.
Proof.
  intro n; induction n; simpl; auto.
Qed.

#[global] Remove Hints eq_refl: core.
#[global] Hint Resolve plus_n_O eq_refl: core.

Lemma plus_n_Sm: forall n m: nat, S (n + m) = n + S m.
Proof.
  intros n m; induction n; simpl; auto.
Qed.

#[global] Hint Resolve plus_n_Sm: core.

(** False and True in SProp *)
Inductive SFalse: SProp :=.
Inductive STrue: SProp := sI.

(** A recursive definition of le *)
Fixpoint leR (n m: nat): SProp :=
  match n, m with
  | O, _ => STrue
  | S n, O => SFalse
  | S n, S m => leR n m
  end.

Lemma leR_refl {n}: leR n n.
Proof.
  now induction n.
Qed.

Lemma leR_O_contra {n}: leR n.+1 O -> SFalse.
Proof.
  now auto.
Qed.

Lemma leR_O {n}: leR O n.
Proof.
  now auto.
Qed.

Lemma leR_trans {n m p} (Hnm: leR n m) (Hmp: leR m p): leR n p.
Proof.
  revert n p Hnm Hmp. induction m, n, p. all: try now auto. simpl.
  now apply IHm.
Qed.

Infix "↕" := leR_trans (at level 45).

Lemma leR_up {n m} (Hnm: leR n m): leR n m.+1.
Proof.
  revert m Hnm. induction n. now auto. destruct m. intros H.
  now apply leR_O_contra in H. now apply IHn.
Qed.

Notation "↑ h" := (leR_up h) (at level 40).

Lemma leR_down {n m} (Hnm: leR n.+1 m): leR n m.
Proof.
  revert m Hnm. induction n. now auto. destruct m. intros H.
  now apply leR_O_contra in H. now apply IHn.
Qed.

Notation "↓ p" := (leR_down p) (at level 40).

Lemma leR_lower_both {n m} (Hnm: leR n.+1 m.+1): leR n m.
Proof.
  now auto.
Qed.

Notation "⇓ p" := (leR_lower_both p) (at level 40).

Lemma leR_raise_both {n m} (Hnm: leR n m): leR n.+1 m.+1.
Proof.
  now auto.
Qed.

Notation "⇑ p" := (leR_raise_both p) (at level 40).
Infix "<=" := leR: nat_scope.

Definition leR_eq {a b n: nat} (e: a = b): a <= n -> b <= n :=
  match e with eq_refl => fun H => H end.

Definition leR_eq_r {a n n': nat} (e: n = n'): a <= n -> a <= n' :=
  match e with eq_refl => fun H => H end.

Definition leR_add_shift {q p n: nat}: q + p.+1 <= n -> q.+1 + p <= n :=
  leR_eq (eq_sym (plus_n_Sm q p)).

Fixpoint leR_add_l (q: nat) {p: nat}: p <= q + p :=
  match q with
  | 0 => leR_refl
  | S q => ↑ (leR_add_l q)
  end.

Fixpoint leR_add_r (p L: nat) {struct L}: p <= p + L :=
  match L with
  | 0 => leR_eq_r (plus_n_O p) leR_refl
  | S L => leR_eq_r (plus_n_Sm p L) (↑ (leR_add_r p L))
  end.

Set Keyed Unification.

Inductive NatOrder (i j: nat): Type :=
| NatOrderLt: i.+1 <= j -> NatOrder i j
| NatOrderEq: i = j -> NatOrder i j
| NatOrderGt: j.+1 <= i -> NatOrder i j.

Arguments NatOrderLt {i j} _.
Arguments NatOrderEq {i j} _.
Arguments NatOrderGt {i j} _.

Fixpoint natOrder (i j: nat) {struct i}: NatOrder i j.
Proof.
  destruct i as [|i], j as [|j].
  - exact (NatOrderEq eq_refl).
  - exact (@NatOrderLt 0 j.+1 (@leR_O j)).
  - exact (@NatOrderGt i.+1 0 (@leR_O i)).
  - destruct (natOrder i j) as [H|e|H].
    + exact (@NatOrderLt i.+1 j.+1 H).
    + exact (NatOrderEq (f_equal S e)).
    + exact (@NatOrderGt i.+1 j.+1 H).
Defined.

Definition natUIP {a b: nat} (e e': a = b): e = e' :=
  UIP_dec eq_dec e e'.

Lemma sub0r (m: nat): m - 0 = m.
Proof.
  now destruct m.
Qed.

Lemma subSuccL {r m: nat}: r <= m -> m.+1 - r = (m - r).+1.
Proof.
  revert m; induction r; intros m H.
  - now destruct m.
  - destruct m. destruct (leR_O_contra H). now exact (IHr m H).
Qed.

Lemma subPos {j m: nat}: j.+1 <= m -> m - j = (m - j.+1).+1.
Proof.
  revert m; induction j; intros m H.
  - destruct m. destruct (leR_O_contra H). cbn. now rewrite sub0r.
  - destruct m. destruct (leR_O_contra H). now exact (IHj m H).
Qed.

Lemma subSuccR (a b: nat): a - b.+1 = pred (a - b).
Proof.
  revert b; induction a; intros b.
  - now reflexivity.
  - destruct b. cbn. now rewrite sub0r. now exact (IHa b).
Qed.

Lemma addSubCancel {q m: nat}: q <= m -> q + (m - q) = m.
Proof.
  revert m; induction q; intros m H.
  - now exact (sub0r m).
  - destruct m. destruct (leR_O_contra H). cbn. now rewrite (IHq m H).
Qed.

Lemma subSplit {r q m: nat}: r <= q -> q <= m -> m - r = (q - r) + (m - q).
Proof.
  revert q m; induction r; intros q m Hr Hq.
  - rewrite 2 sub0r. now rewrite (addSubCancel Hq).
  - destruct q. destruct (leR_O_contra Hr).
    destruct m. destruct (leR_O_contra Hq).
    now exact (IHr q m Hr Hq).
Qed.

Lemma sub_leR (a b: nat): a - b <= a.
Proof.
  revert b; induction a; intros b.
  - now exact leR_O.
  - destruct b. exact leR_refl. now exact (↑ (IHa b)).
Qed.

Lemma subDiag (a: nat): a - a = 0.
Proof.
  induction a. reflexivity. now exact IHa.
Qed.

Lemma subAntitone {i j n: nat}: i <= j -> n - j <= n - i.
Proof.
  revert i j; induction n; intros i j H.
  - now exact leR_refl.
  - destruct i as [|i], j as [|j].
    + exact leR_refl.
    + exact (↑ (sub_leR n j)).
    + now destruct (leR_O_contra H).
    + now exact (IHn i j H).
Qed.

Lemma addSubCancelL (a b: nat): (a + b) - a = b.
Proof.
  induction a; cbn.
  - now apply sub0r.
  - now exact IHa.
Qed.

Lemma subSubCancel {dim L: nat}: dim <= L -> L - (L - dim) = dim.
Proof.
  revert L; induction dim; intros L H.
  - rewrite sub0r. now exact (subDiag L).
  - destruct L. destruct (leR_O_contra H).
    rewrite (subSuccL (sub_leR L dim)).
    now rewrite (IHdim L H).
Qed.

(** Boolean equality tests under strict-proposition bounds.
    The proofs remain transparent for dependent case analysis on the test. *)

Fixpoint natEqbRefl (n: nat): eqb n n = true :=
  match n with 0 => eq_refl | S n => natEqbRefl n end.

Lemma natEqbEq: forall q n, eqb q n = true -> q = n.
Proof.
  induction q as [|q IHq]; intros [|n] E; simpl in E.
  - now reflexivity.
  - now discriminate E.
  - now discriminate E.
  - now exact (f_equal S (IHq n E)).
Defined.

Lemma leR0Eq {q}: q <= 0 -> q = 0.
Proof.
  destruct q as [|q]. now reflexivity. intro H. now destruct H.
Defined.

Lemma leRNeqS: forall q n, q <= n -> eqb q (S n) = false.
Proof.
  induction q as [|q IHq]; intros [|n] H; simpl.
  - now reflexivity.
  - now reflexivity.
  - now destruct H.
  - now exact (IHq n H).
Defined.

Lemma leRDown: forall q n, q <= S n -> eqb q (S n) = false -> q <= n.
Proof.
  induction q as [|q IHq]; intros [|n] H E.
  - now exact leR_O.
  - now exact leR_O.
  - simpl in E. rewrite (leR0Eq H) in E. now discriminate E.
  - now exact (IHq n H E).
Defined.
