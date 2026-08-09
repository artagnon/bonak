(** Chains: Moore-style composites of equalities

    A [Chain] is a list of composable equality steps — the discrete analogue of
    a Moore path. Concatenation [capp] recurses on its first argument, so
    [capp cnil C] is [C] *definitionally* for every [C], and on canonical
    cons-spines associativity and the right unit law hold definitionally too.
    For [•] all three laws are propositional only: [•] reduces on its second
    argument, so [p • eq_refl] is [p] while [eq_refl • q] is stuck, and neither
    bracketing of [p • q • e] reduces.

    [interp], written [⟦C⟧], collapses a chain to the single equality it
    denotes; [interp_capp] and [interp_cmap] are the bridge back to eq-land,
    where the chain structure is forgotten. *)

Set Warnings "-notation-overridden".
From Bonak Require Import Notation.

Inductive Chain {X: Type}: X -> X -> Type :=
| cnil {a}: Chain a a
| ccons {a b c}: a = b -> Chain b c -> Chain a c.

Notation "[: x ; .. ; y :]" := (ccons x .. (ccons y cnil) ..)
  (at level 0).

Fixpoint capp {X: Type} {a b c: X} (C: Chain a b): Chain b c -> Chain a c :=
  match C with
  | cnil => fun D => D
  | ccons e C => fun D => ccons e (capp C D)
  end.

Fixpoint cmap {X Y: Type} (f: X -> Y) {a b: X} (C: Chain a b):
  Chain (f a) (f b) :=
  match C with
  | cnil => cnil
  | ccons e C => ccons (f_equal f e) (cmap f C)
  end.

Fixpoint interp {X: Type} {a b: X} (C: Chain a b): a = b :=
  match C with
  | cnil => eq_refl
  | ccons e C => e • interp C
  end.

Notation "⟦ C ⟧" := (interp C) (at level 0, format "⟦ C ⟧").

Lemma interp_capp {X: Type} {a b c: X} (C: Chain a b) (D: Chain b c):
  ⟦capp C D⟧ = ⟦C⟧ • ⟦D⟧.
Proof.
  induction C as [|? ? ? e C IH]; cbn.
  - now destruct (interp D).
  - rewrite IH. now apply eq_trans_assoc.
Defined.

Lemma interp_cmap {X Y: Type} (f: X -> Y) {a b: X} (C: Chain a b):
  ⟦cmap f C⟧ = f_equal f ⟦C⟧.
Proof.
  induction C as [|? ? ? e C IH]; cbn.
  - reflexivity.
  - rewrite IH. now destruct (interp C).
Defined.
