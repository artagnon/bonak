(** Miscellaneous notations *)

Notation "( x 'as' z 'in' T ; y 'in' P )" := (existT (fun z : T => P) x y)
  (at level 0, only parsing).
Notation "( x ; y )" := (existT _ x y)
  (at level 0, format "'[' ( x ;  '/ ' y ) ']'").
Notation "x .1" := (projT1 x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (projT2 x) (at level 1, left associativity, format "x .2").
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

Notation "(= u ; v )" := (eq_existT_curried u v)
(at level 0, format "(= u ;  '/  ' v )").

Infix "•" := eq_trans (at level 65, left associativity).
Notation "[ x ⇒ f ] e" := (f_equal (fun x => f) e)
(at level 60, left associativity).
