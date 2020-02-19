From HoTT Require Import HoTT.

(* Checks that U and Q can simultanously be inhabited by P. *)
Definition check U V := forall X : U, V.

(* Prop is impredicative. *)
Definition PropImpr := check Prop Prop.

(* Set is predicative. *)
Fail Definition SetPred := (forall X : Set, X) : Set.

(* Is Type impredicative? This is misleading. *)
Definition TypeNaive := check Type Type.

(* In the previous definition, Type is really Type@{i},
 * and the following definition fails with: Universe {Predicativity.153} is unbound. *)
Fail Definition TypePred@{i} := check Type@{i} Type@{i}.

(* Fails due to a bug in Coq: Unable to handle arbitrary u+k <= v constraints? *)
Fail Definition TypePred'@{i} := check Type@{i + 1} Type@{i}.
