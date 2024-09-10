Section DepStream.

Context {A} (B:A->Type) (f:forall a, B a -> A).

CoInductive DepStream (a:A) : Type :=
  { this : B a ; next : DepStream (f a this) }.

Context (D:A->Type) (v : forall a, D a -> B a) (s : forall a d, D (f a (v a d))).

CoFixpoint g a (d:D a) : DepStream a :=
  {| this := v a d; next := g (f a (v a d)) (s a d) |}.

End DepStream.
