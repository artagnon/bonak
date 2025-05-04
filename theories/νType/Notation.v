(** Miscellaneous notations *)

Notation "x .+1" := (S x) (at level 1, left associativity, format "x .+1").
Notation "x .+2" := (S (S x)) (at level 1, left associativity, format "x .+2").
Notation "x .+3" := (S (S (S x)))
  (at level 1, left associativity, format "x .+3").
Notation "x .-1" := (pred x) (at level 1, left associativity, format "x .-1").
Notation "x .-2" := (pred (pred x))
  (at level 1, left associativity, format "x .-2").

(** This is in Program.Basics for some strange reason *)
Arguments id {A} x.

(** Notations for rew *)
Notation "'rew' [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10,
    format "'[' 'rew'  [ P ]  '/    ' H  in  '/' H' ']'").
Notation "'rew' <- [ P ] H 'in' H'" := (eq_rect_r P H' H)
    (at level 10, H' at level 10,
    format "'[' 'rew'  <-  [ P ]  '/    ' H  in  '/' H' ']'").

Infix "•" := eq_trans (at level 65, left associativity).
Notation "[ x ⇒ f ] e" := (f_equal (fun x => f) e)
(at level 60, left associativity).
