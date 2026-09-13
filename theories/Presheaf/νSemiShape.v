(** The ν-semi-shape category, by normal forms.

    This is the category written ⬡ in Herbelin and Ramachandra, "A
    parametricity-based formalization of semi-simplicial and semi-cubical
    sets" (Definition II.0.14). Its objects are the natural numbers, and a
    morphism [n -> m] is a word of length [m] over the arity [A] extended by
    one letter ⋆, with exactly [n] occurrences of ⋆: a letter of [A] deletes
    a position of [Fin m] and labels the deletion, ⋆ keeps it. The deleted
    positions, read in order, are the coface indices of the unique normal
    decomposition of a labelled strictly monotone injection [Fin n -> Fin m],
    so strict increase is built into the representation. Composition is
    defined by structural recursion on the codomain size.

    A word is stored with its top letter first: [wskip ε] decides the top
    position of [Fin m] and [wkeep] keeps it. The paper reads the same word
    from the bottom position; reversal exchanges the two readings and respects
    composition. Words are defined by recursion on the codomain rather than as
    an inductive family, so case analysis on a word is case analysis on a sum
    and needs no dependent inversion. *)

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation LeSProp NatLemmas.
From Bonak.Category Require Import Category.

Set Primitive Projections.
Set Printing Projections.

Unset Universe Minimization ToSet.

Section νSemiShape.
Context (A: HSet).

(** [Word n m] is the type of morphisms [n -> m] of the ν-semi-shape
    category. *)

Fixpoint Word (n m: nat): Type :=
  match m with
  | 0 => match n with 0 => unit | S _ => Empty_set end
  | S m => (A * Word n m) + (match n with 0 => Empty_set | S n => Word n m end)
  end.

Definition wnil: Word 0 0 := tt.
Definition wskip {n m} (ε: A) (w: Word n m): Word n (S m) := inl (ε, w).
Definition wkeep {n m} (w: Word n m): Word (S n) (S m) := inr w.

(** Identities and composition. [wcomp g f] is [g] after [f]; the ν-semi-shape
    category is written in diagrammatic order, so it is the composite [f ⨟
    g]. *)

Fixpoint wid (n: nat): Word n n :=
  match n with 0 => wnil | S n => wkeep (wid n) end.

Fixpoint wcomp (p: nat) {struct p}:
  forall m n, Word m p -> Word n m -> Word n p :=
  match p as p return forall m n, Word m p -> Word n m -> Word n p with
  | 0 =>
    fun m =>
      match m as m return forall n, Word m 0 -> Word n m -> Word n 0 with
      | 0 => fun n _ f => f
      | S m => fun n g _ => match g return Word n 0 with end
      end
  | S p =>
    fun m n g f =>
      match g with
      | inl (ε, g) => wskip ε (wcomp p m n g f)
      | inr g =>
        (match m as m return
           (match m return Type with 0 => Empty_set | S m => Word m p end) ->
           Word n m -> Word n (S p)
         with
         | 0 => fun g _ => match g return Word n (S p) with end
         | S m => fun g f =>
           match f with
           | inl (ε, f) => wskip ε (wcomp p m n g f)
           | inr f =>
             (match n as n return
                (match n return Type with 0 => Empty_set | S n => Word n m end) ->
                Word n (S p)
              with
              | 0 => fun f => match f return Word 0 (S p) with end
              | S n => fun f => wkeep (wcomp p m n g f)
              end) f
           end
         end) g f
      end
  end.

Arguments wcomp {p m n} g f.

(** The three computation rules of composition, in the shape used below. *)

Lemma wcomp_skip {m n p} (ε: A) (g: Word m p) (f: Word n m):
  wcomp (wskip ε g) f = wskip ε (wcomp g f).
Proof. now reflexivity. Defined.

Lemma wcomp_keep_skip {m n p} (ε: A) (g: Word m p) (f: Word n m):
  wcomp (wkeep g) (wskip ε f) = wskip ε (wcomp g f).
Proof. now reflexivity. Defined.

Lemma wcomp_keep_keep {m n p} (g: Word m p) (f: Word n m):
  wcomp (wkeep g) (wkeep f) = wkeep (wcomp g f).
Proof. now reflexivity. Defined.

(** The hom-types are [HSet]s: a word is a finite tree of labels and
    decisions over the [HSet] of labels. *)

Fixpoint wordUIP (m n: nat) {struct m}:
  forall (w w': Word n m) (h g: w = w'), h = g.
Proof.
  destruct m as [|m].
  - destruct n as [|n]; intros w w' h g.
    + now apply unit_UIP.
    + now destruct w.
  - destruct n as [|n]; intros w w' h g.
    + now exact (@sumUIP (prodSet A {| Dom := Word 0 m; UIP := wordUIP m 0 |})
                         hEmpty w w' h g).
    + now exact (@sumUIP
        (prodSet A {| Dom := Word (S n) m; UIP := wordUIP m (S n) |})
        {| Dom := Word n m; UIP := wordUIP m n |} w w' h g).
Defined.

Definition wordSet (n m: nat): HSet := {|
  Dom := Word n m;
  UIP := wordUIP m n;
|}.

(** The category laws *)

Lemma wcompIdl {m n} (f: Word n m): wcomp (wid m) f = f.
Proof.
  revert n f; induction m as [|m IHm]; intros n f.
  - destruct n as [|n]; [now destruct f | now destruct f].
  - destruct f as [(ε, f)|f].
    + now exact (f_equal (wskip ε) (IHm n f)).
    + destruct n as [|n]; [now destruct f|].
      now exact (f_equal (@wkeep n m) (IHm n f)).
Defined.

Lemma wcompIdr {n p} (g: Word n p): wcomp g (wid n) = g.
Proof.
  revert n g; induction p as [|p IHp]; intros n g.
  - destruct n as [|n]; [now destruct g | now destruct g].
  - destruct g as [(ε, g)|g].
    + now exact (f_equal (wskip ε) (IHp n g)).
    + destruct n as [|n]; [now destruct g|].
      now exact (f_equal (@wkeep n p) (IHp n g)).
Defined.

Lemma wcompAssoc {q p m n} (h: Word p q) (g: Word m p) (f: Word n m):
  wcomp h (wcomp g f) = wcomp (wcomp h g) f.
Proof.
  revert p m n h g f; induction q as [|q IHq]; intros p m n h g f.
  - destruct p as [|p]; [|now destruct h].
    destruct m as [|m]; [|now destruct g].
    destruct n as [|n]; [|now destruct f].
    now destruct h, g, f.
  - destruct h as [(ε, h)|h].
    + now exact (f_equal (wskip ε) (IHq p m n h g f)).
    + destruct p as [|p]; [now destruct h|].
      destruct g as [(ε, g)|g].
      * now exact (f_equal (wskip ε) (IHq p m n h g f)).
      * destruct m as [|m]; [now destruct g|].
        destruct f as [(ε, f)|f].
        -- now exact (f_equal (wskip ε) (IHq p m n h g f)).
        -- destruct n as [|n]; [now destruct f|].
           now exact (f_equal (@wkeep n q) (IHq p m n h g f)).
Defined.

(** The object [n] represents [n] positions, corresponding to geometric
    dimension [n - 1] for positive [n]. Object [0] is the empty shape,
    giving the augmentation. *)

Definition νSemiShape: Category := {|
  CObj := nat;
  CHom := wordSet;
  cid := wid;
  ccomp a b c f g := wcomp g f;
  cidl a b f := wcompIdr f;
  cidr a b f := wcompIdl f;
  cassoc a b c d f g h := wcompAssoc h g f;
|}.

(** Generating cofaces

    [wgen n q ε] deletes position [q] when [q <= n]. It compares [q] with
    the current top position while keeping the positions above it, then
    deletes that position and keeps the remainder. The definition takes no
    bound proof; the two computation lemmas state its behavior under [q <= n]. *)

Fixpoint wgen (n q: nat) (ε: A) {struct n}: Word n (S n) :=
  match n with
  | 0 => wskip ε wnil
  | S n => if Nat.eqb q (S n) then wskip ε (wid (S n)) else wkeep (wgen n q ε)
  end.

Lemma wgenTop (n: nat) (ε: A): wgen n n ε = wskip ε (wid n).
Proof.
  destruct n as [|n]. now reflexivity. simpl. now rewrite natEqbRefl.
Defined.

Lemma wgenLift {n q} (Hq: q <= n) (ε: A): wgen (S n) q ε = wkeep (wgen n q ε).
Proof.
  simpl. now rewrite (leRNeqS q n Hq).
Defined.

(** The exchange relation for two generating cofaces, with the index shift
    accounting for the position removed by the first deletion. *)

Lemma wgenExchange: forall n q (Hq: q <= n) r (Hr: r <= q) (ε ω: A),
  wcomp (wgen (S n) r ω) (wgen n q ε)
  = wcomp (wgen (S n) (S q) ε) (wgen n r ω).
Proof.
  induction n as [|n IHn]; intros q Hq r Hr ε ω.
  - pose proof (leR0Eq Hq) as Eq; subst q.
    pose proof (leR0Eq Hr) as Er; subst r. now reflexivity.
  - destruct (Nat.eqb q (S n)) eqn:E.
    + pose proof (natEqbEq q (S n) E) as Eq; subst q.
      rewrite (wgenLift Hr ω), (wgenTop (S n) ε), (wgenTop (S (S n)) ε).
      rewrite wcomp_keep_skip, wcomp_skip, wcompIdl, wcompIdr.
      now reflexivity.
    + assert (Hq': q <= n) by now exact (leRDown q n Hq E).
      assert (Hrn: r <= n) by now exact (Hr ↕ Hq').
      refine (_ • (f_equal wkeep (IHn q Hq' r Hr ε ω) • _)).
      * rewrite (wgenLift (↑ Hrn) ω), (wgenLift Hq' ε).
        now exact (wcomp_keep_keep _ _).
      * rewrite (wgenLift (⇑ Hq') ε), (wgenLift Hrn ω).
        now exact (eq_sym (wcomp_keep_keep _ _)).
Defined.

(** Prefixing a word with the top coface is [wskip]. *)

Lemma wgenSkip {n m} (ε: A) (w: Word n m): wcomp (wgen m m ε) w = wskip ε w.
Proof.
  rewrite (wgenTop m ε). now exact (f_equal (wskip ε) (wcompIdl w)).
Defined.

(** The shift endofunctor on the opposite ν-semi-shape category raises
    each object by one and prefixes each word with [wkeep]. It preserves
    the indices of the deleted positions. *)

Definition νSemiShapeShift: Functor (Op νSemiShape) (Op νSemiShape) :=
  Build_Functor (Op νSemiShape) (Op νSemiShape) (fun n => S n) (fun a b w => wkeep w)
    (fun a => eq_refl) (fun a b c f g => eq_sym (wcomp_keep_keep f g)).

End νSemiShape.

Arguments wnil {A}.
Arguments wskip {A n m} ε w.
Arguments wkeep {A n m} w.
Arguments wid {A} n.
Arguments wcomp {A p m n} g f.
Arguments wgen {A} n q ε.
Arguments wordSet {A} n m.
Arguments wgenSkip {A n m} ε w.
Arguments wgenTop {A} n ε.
Arguments wgenLift {A n q} Hq ε.
Arguments wgenExchange {A} n q Hq r Hr ε ω.
Arguments wcompIdl {A m n} f.
Arguments wcompIdr {A n p} g.
Arguments wcompAssoc {A q p m n} h g f.
Arguments wcomp_skip {A m n p} ε g f.
Arguments wcomp_keep_skip {A m n p} ε g f.
Arguments wcomp_keep_keep {A m n p} g f.
Arguments wordSet {A} n m.
