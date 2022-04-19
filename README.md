# Bonak

Bonak is a research project that formalizes semi-cubical types in Coq. Prior to the start of the project, Hugo had worked out the rough type-theory of semi-cubical types on pen-and-paper, and hypothesized that it could be formalized in Coq. The project started when Hugo and Ram met to test the hypothesis. They then met once a week for the next 2.5 years, to commit time to work on the project. The first commit was made on August 15, 2019, and the formalization was completed on 22 February 2022. Indeed, it has been quite an adventure.

The name _bonak_ comes from an imaginary monster in Daisy Johnson's novel [Everything Under](https://thebookerprizes.com/the-booker-library/books/everything-under), which was shortlisted for the Man Booker Prize in 2018. It happens to be an exciting read, and Ram had read the book at around the time this project started.

Some features of this project:

1. We do not make use of [HoTT](https://github.com/HoTT/HoTT), or any fancy libraries for that matter. Bonak is written is vanilla Coq, making use of the core standard libarary. In particular, we make heavy use of [SProp](https://coq.inria.fr/refman/addendum/sprop.html) for proof irrelevance.
2. Bonak has led to many bugs being filed and fixed in core Coq. It pushes the boundaries of proof assistant technology, and can serve as as a benchmark against which to improve core Coq features.
3. As the main contribution of Bonak is the Coq code, we have placed high emphasis on code cleanliness and readability. As a result, it's quite plesant to step through the code, and have a succint goal at all times.
4. Bonak is tiny! In ~700 lines of Coq code, we have managed to prove something remarkable. We did have a lot of false starts, and tried various approaches, before settling on what we have today.

## Current status

Our approach naturally generalizes to (augmented) semi-simplicial types, as well as higher types: we use functional extensionality for this, but it can, in principle, be done without this axiom. `master` is a nominally complete version of our formalization, without any incomplete proofs, but we're currently working on minimizing the set of assumptions.
