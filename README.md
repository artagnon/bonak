# Bonak ![logo](assets/bonak.png)

Bonak is an active hobby-research project around formalizing simplicial and cubical sets in [Rocq](https://rocq-prover.org) as a particular case of iterated parametricity translation. The project started when Hugo met Ram in late 2019, and they continue to meet online weekly to continue this line of research.

The name _bonak_ comes from an imaginary monster in Daisy Johnson's novel [Everything Under](https://thebookerprizes.com/the-booker-library/books/everything-under), which was shortlisted for the Booker Prize in 2018. It happens to be an exciting read, and Ram had read the book at around the time this project started.

Some features of this project:

1. We do not make use of [HoTT](https://github.com/HoTT/HoTT), or any fancy libraries for that matter. Bonak is written is vanilla Rocq, making use of the core standard library. In particular, we make use of [SProp](https://rocq-prover.org/doc/master/refman/addendum/sprop.html) for definitional proof irrelevance.
2. Bonak has led to many bugs being filed and fixed in core Rocq. It pushes the boundaries of proof assistant technology, and can serve as a benchmark against which to improve core Rocq features. Rocq 9.0 is required to build the current version.
3. As the main contribution of Bonak is the Rocq code, we have placed high emphasis on code cleanliness and readability.
4. Bonak is tiny! In ~800 lines of Rocq code, we have managed to prove something remarkable.

## Axioms

```coq
Axioms:
  functional_extensionality_dep
    : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
      (forall x : A, f x = g x) -> f = g
```

Our approach is generic over the arity of the parametricity translation: we use functional extensionality for this, but it can, in principle, be done without this axiom for any fixed finite arity.

## Current status

The first paper describing our initial work can be found at [arXiv:2401.00512](https://arxiv.org/abs/2401.00512) (pre-print) or [10.1017/S096012952500009X](https://doi.org/10.1017/S096012952500009X) (published version), and the corresponding code can be found under the tag [hr25](https://github.com/artagnon/bonak/tree/962647e33cfe653eaac989bae16817b42dab3280). The coqdoc documentation is under the subdirectory [hr25](https://artagnon.github.io/bonak/hr25/).

`master` and other branches contain work-in-progress for future publications.
