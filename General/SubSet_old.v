Require Import Omega.

(* Isomorphism section *)

Definition surjective {X Y} (f : X -> Y) :=
  forall y : Y, exists x : X, f x = y.

Definition injective {X Y} (f : X -> Y) :=
  forall x1 x2 : X, f x1 = f x2 -> x1 = x2.

Definition bijective {X Y} (f : X -> Y) :=
  surjective f /\ injective f.

Definition isomorphic X Y :=
  exists f : X -> Y, bijective f.

Notation "X ~= Y" := (isomorphic X Y) (at level 70, no associativity) : type_scope.

Lemma iso_refl: forall X, X ~= X.
Proof.
  intros. exists (fun x => x). split.
  - (* surjective *) intros y. exists y. reflexivity.
  - (* injective *) intros x1 x2. intros. assumption.
Qed.

Lemma iso_trans: forall X Y Z, X ~= Y -> Y ~= Z -> X ~= Z.
Proof.
  intros X Y Z [f [Hf_surj Hf_inj]] [g [Hg_surj Hg_inj]].
  exists (fun x => g (f x)). split.
  - (* surjective *) intros z. destruct (Hg_surj z) as [y Hyz].
    destruct (Hf_surj y) as [x Hxy]. exists x. subst. trivial.
  - (* injective *) intros x1 x2 Heq. apply Hg_inj in Heq.
    apply Hf_inj in Heq. trivial.
Qed.

Definition inverse {X Y} (f : X -> Y) (g : Y -> X) :=
  forall x, g (f x) = x.

Lemma inverse_surjective: forall X Y (f : X -> Y) (g : Y -> X),
  inverse f g -> surjective g.
Proof.
  intros X Y f g Hinv. intros x. exists (f x). apply Hinv.
Qed.

Lemma inverse_injective: forall X Y (f : X -> Y) (g : Y -> X),
  surjective f -> inverse f g -> injective g.
Proof.
  intros X Y f g Hsurj Hinv. intros x1 x2 Heq.
  destruct (Hsurj x1) as [y1 Hxy1]. destruct (Hsurj x2) as [y2 Hxy2]. subst.
  rewrite Hinv in Heq. rewrite Hinv in Heq. subst. trivial.
Qed.

Lemma inverse_bijective: forall X Y (f : X -> Y) (g : Y -> X),
  surjective f -> inverse f g -> bijective g.
Proof.
  intros. split.
  - apply inverse_surjective with (f:=f). assumption.
  - apply inverse_injective with (f:=f); assumption.
Qed.

Lemma inverse_inverse_bijective: forall X Y (f : X -> Y) (g : Y -> X),
  inverse f g -> inverse g f -> bijective f.
Proof.
  intros. split.
  - apply inverse_surjective with (f:=g). assumption.
  - apply inverse_injective with (f:=g); try assumption.
    (* surjective g *) apply inverse_surjective with (f:=f). assumption.
Qed.

Definition bij_inv {X Y : Set} (f : X -> Y) : bijective f -> Y -> X.
  intros [Hsurj Hinj] y. pose (Hsurj y) as H. destruct H.

(* TODO *)
Lemma bijection_inverse: forall X Y (f : X -> Y),
  bijective f -> exists (g : Y -> X), inverse f g.
Proof.
  intros. destruct H as [Hsurj Hinj]. exists Hsurj.
Abort.

Lemma iso_comm: forall X Y, X ~= Y -> Y ~= X.
  intros X Y [f [Hsurj Hinj]].
Abort.

(* Isomorphism examples *)

Example nat_opnat_iso: nat ~= option nat.
  exists (fun n => match n with O => None | S m => Some m end). split.
  - (* surjective *) intros y. destruct y.
    + (* f (S n) = Some n *) exists (S n). trivial.
    + (* f O = None *) exists O. trivial.
  - (* injective *) intros x1 x2.
    destruct x1; destruct x2; intros; inversion H; trivial.
Qed.

Example opnat_nat_iso: option nat ~= nat.
  exists (fun on => match on with None => O | Some n => S n end). split.
  - (* surjective *) intros y. destruct y.
    + exists None. trivial.
    + exists (Some y). trivial.
  - (* injective *) intros x1 x2.
    destruct x1; destruct x2; intros; inversion H; trivial.
Qed.


(* Dependent types *)

(* We need Proof Irrelevance for sig. *)
Axiom sig_eq: forall A P (x y : {a : A | P a}), proj1_sig x = proj1_sig y -> x = y.

Lemma surjective_dep: forall X Y P (f : X -> {y : Y | P y}),
   (forall y, P y -> exists x, proj1_sig (f x) = y) <-> surjective f.
Proof.
  intros. split; intros.
  - (* ... -> surj *) intros y. destruct y as [y HPy]. apply H in HPy as Hex.
    destruct Hex as [x Heq]. exists x. apply sig_eq. simpl. assumption.
  - (* surj -> ... *) destruct (H (exist P y H0)) as [x Heq]. exists x.
    rewrite Heq. trivial.
Qed.

Definition nat_nat1_bij (n : nat) : {n : nat | n > 0}.
  refine (exist _ (S n) _). omega.
Defined.

Definition raise {X Y} (f : X -> Y) (P : Y -> Prop) (pf : forall x, P (f x))
  : X -> {y : Y | P y}.
  intros x. refine (exist _ (f x) _). apply pf.
Defined.

Lemma raise_eq: forall X Y (f : X -> Y) P pf (x : X),
  proj1_sig (raise f P pf x) = f x.
Proof.
  intros.
Abort.

Example nat_iso_ex1 : nat ~= {n : nat | n > 0}.
  exists nat_nat1_bij. split.
  - (* surjective *) intros n. destruct n as [n Hn0]. destruct n.
    + (* n -> O *) inversion Hn0.
    + (* n -> S n *) exists n. apply sig_eq. simpl. trivial.
  - (* injective *) intros x1 x2 Heq. destruct x1; destruct x2. trivial.














