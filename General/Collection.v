Module Collection.

(* Collection (like a set but without any set axioms). *)
Record Coll := mkColl {
  universe : Set;
  contains : universe -> Prop;
  equiv : universe -> universe -> Prop;
  pf_equiv_refl : forall a, contains a -> equiv a a;
  pf_equiv_symm : forall a b, contains a -> contains b -> equiv a b -> equiv b a;
  pf_equiv_trans : forall a b c, contains a -> contains b -> contains c ->
                   equiv a b -> equiv b c -> equiv a c;
}.

Notation "a (in) A" := (contains A a) (at level 50, no associativity).
Notation "a ~= b (in A )" := (equiv A a b) (at level 50, no associativity).

Definition subset_coll (U : Set) (P : U -> Prop) : Coll.
  refine (mkColl U P (fun a b => a = b) _ _ _); intros; auto. subst. trivial.
Defined.

Function set_coll (A : Set) : Coll := subset_coll A (fun a => True).

Example foo: 0 ~= 0 (in set_coll nat).
  simpl. trivial. Qed.

End Collection.