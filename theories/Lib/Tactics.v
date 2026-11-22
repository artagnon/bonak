From Bonak.Lib Require Import Logic.

Ltac exfalso := Corelib.Init.Ltac.exfalso.

Ltac contradict H :=
  let save tac H := let x := fresh in intro x; tac H; rename x into H in
  let negpos H := case H; clear H in
  let negneg H := save negpos H in
  let pospos H :=
    let A := type of H in (exfalso; revert H; try fold (~A)) in
  let posneg H := save pospos H in
  let neg H :=
    match goal with
    | |- (~_) => negneg H
    | |- (_ -> Empty_set) => negneg H
    | |- _ => negpos H
    end in
  let pos H :=
    match goal with
    | |- (~_) => posneg H
    | |- (_ -> Empty_set) => posneg H
    | |- _ => pospos H
    end in
  match type of H with
  | (~_) => neg H
  | (_ -> Empty_set) => neg H
  | _ => (elim H; fail) || pos H
  end.

Ltac easy :=
  let rec use_hyp H :=
    match type of H with
    | _ * _ => exact H || destruct_hyp H
    | _ => try solve [inversion H]
    end
  with do_intro := let H := fresh in intro H; use_hyp H
  with destruct_hyp H := case H; clear H; do_intro; do_intro in
  let rec use_hyps :=
    match goal with
    | H: _ * _ |- _ => exact H || (destruct_hyp H; use_hyps)
    | H: _ |- _ => solve [inversion H]
    | _ => idtac
    end in
  let do_atom :=
    solve [ trivial | reflexivity | symmetry; trivial | contradiction ] in
  let rec do_ccl :=
    try do_atom;
    repeat (do_intro; try do_atom);
    solve [ split; do_ccl ] in
  solve [ do_atom | use_hyps; do_ccl ] ||
  fail "Cannot solve this goal".

Ltac Corelib.Init.Ltac.easy_forward_decl ::= easy.

Tactic Notation "now" tactic(t) := t; easy.

Definition f_equal_app (A B: Type) (f g: A -> B) (x y: A)
  (e: f = g) (e': x = y): f x = g y :=
  match e' in _ = a return f x = g a with
  | eq_refl => Logic.f_equal (fun h => h x) e
  end.

Ltac f_equal :=
  lazymatch goal with
  | |- ?f ?x = ?g ?y =>
    let T := type of f in
    let T := eval hnf in T in
    lazymatch T with
    | ?A -> ?B =>
      first
        [ refine (f_equal_app A B f g x y _ _);
          [ first [ reflexivity | f_equal ] | try reflexivity ]
        | idtac ]
    | _ =>
      first
        [ unify x y; refine (@Logic.f_equal T _ (fun h: T => h x) f g _);
          first [ reflexivity | f_equal ]
        | idtac ]
    end
  | |- _ => idtac
  end.
