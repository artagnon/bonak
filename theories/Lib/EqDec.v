From Bonak.Lib Require Import Logic.

Set Implicit Arguments.

Section EqdepDec.
  Variable A: Type.

  Let comp (x y y': A) (eq1: x = y) (eq2: x = y'): y = y' :=
    eq_ind _ (fun a => a = y') eq2 _ eq1.

  Remark trans_sym_eq (x y: A) (u: x = y): comp u u = eq_refl y.
  Proof.
    case u; trivial.
  Qed.

  Variable x: A.
  Variable eq_dec: forall y: A, (x = y) + (x <> y).

  Let nu (y: A) (u: x = y): x = y :=
    match eq_dec y with
    | inl eqxy => eqxy
    | inr neqxy => match neqxy u with end
    end.

  #[local] Lemma nu_constant (y: A) (u v: x = y): nu u = nu v.
  Proof.
    unfold nu.
    destruct (eq_dec y) as [Heq|Hneq].
    - reflexivity.
    - case Hneq; trivial.
  Qed.

  Let nu_inv (y: A) (v: x = y): x = y := comp (nu (eq_refl x)) v.

  Remark nu_left_inv_on (y: A) (u: x = y): nu_inv (nu u) = u.
  Proof.
    case u; unfold nu_inv.
    apply trans_sym_eq.
  Qed.

  Theorem eq_proofs_unicity_on (y: A) (p1 p2: x = y): p1 = p2.
  Proof.
    elim (nu_left_inv_on p1).
    elim (nu_left_inv_on p2).
    elim nu_constant with y p1 p2.
    reflexivity.
  Qed.
End EqdepDec.

Theorem UIP_dec (A: Type) (eq_dec: forall x y: A, (x = y) + (x <> y))
  (x y: A) (p1 p2: x = y): p1 = p2.
Proof.
  apply eq_proofs_unicity_on. exact (eq_dec x).
Qed.

Lemma UIP_refl_unit (x: tt = tt): x = eq_refl tt.
Proof.
  change (match tt as b return tt = b -> Type with
          | tt => fun x => x = eq_refl tt
          end x).
  destruct x; reflexivity.
Defined.

Lemma UIP_refl_bool (b: bool) (x: b = b): x = eq_refl.
Proof.
  destruct b.
  - change (match true as b return true = b -> Type with
            | true => fun x => x = eq_refl
            | _ => fun _ => unit
            end x).
    destruct x; reflexivity.
  - change (match false as b return false = b -> Type with
            | false => fun x => x = eq_refl
            | _ => fun _ => unit
            end x).
    destruct x; reflexivity.
Defined.
