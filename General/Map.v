Inductive Map {A B} (map : A -> B -> Prop) :=
  mkMap: (forall a : A, exists b : B, map a b) ->
         (forall a b1 b2, map a b1 -> map a b2 -> b1 = b2) -> Map map.

Function func {A B} (f: A -> B) a b := f a = b.

Definition func_map {A B} (f: A -> B) : Map (func f).
  constructor; intros.
  - exists (f a). unfold func. trivial.
  - unfold func in *. subst. trivial.
Defined.