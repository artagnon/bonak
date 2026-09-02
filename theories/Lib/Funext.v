Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak Require Import Notation.

(** Functional extensionality for functions out of a strict proposition.

    The standard library axiom does not cover this case:

      Axiom functional_extensionality_dep:
        forall (A: Type) (B: A -> Type) (f g: forall x: A, B x), ...

    is stated at [A: Type], and [SProp] is a separate sort with no coercion into
    [Type], so [functional_extensionality_dep (A := S)] is rejected outright for
    [S: SProp].

    [sBox] removes it by giving [S] a [Type]-level carrier: a one-field
    inductive holding a proof of [S]. Ordinary funext does apply at the boxed
    domain [forall b: sBox S, T (unbox b)], and the boxed and unboxed function
    spaces transfer into each other definitionally, because [SProp] proof
    irrelevance is: any [s s': S] are convertible, hence so are [T s] and [T
    s'], and in particular [T (unbox (sbox s))] is [T s]. So [spropFunext]
    boxes, applies funext, and pulls the result back along [sbox].

    This trick is needed for *empty* [S]. Were [S] inhabited by some [s0],
    irrelevance and eta would already settle it with no axiom at all: [u] is
    convertible with [fun s => u s0], so [f_equal (fun (t: T s0) (s: S) => t) (h s0)]
    proves [u = v]. For empty [S], there is no such [s0], and the general
    statement does rest on funext. *)

Inductive sBox (S: SProp): Type := sbox: S -> sBox S.
Arguments sbox {S} _.

Definition unbox {S: SProp} (b: sBox S): S :=
  match b with sbox s => s end.

Lemma spropFunext {S: SProp} {T: S -> Type} (u v: forall s, T s)
  (h: forall s, u s = v s): u = v.
Proof.
  (* [r w] is [w] transposed to the boxed domain; the [match] typechecks
     because [T (unbox (sbox s))] is convertible with [T s]. *)
  pose (r := fun (w: forall s, T s) (b: sBox S) =>
    match b as b0 return T (unbox b0) with sbox s => w s end).
  assert (R: r u = r v).
  { apply functional_extensionality_dep_good; intros [s]. now exact (h s). }
  (* Pull back along [sbox]: [fun s => r w (sbox s)] is convertible with [w]. *)
  now exact (f_equal
    (fun (w: forall b: sBox S, T (unbox b)) (s: S) => w (sbox s)) R).
Qed.
