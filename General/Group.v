Require Import Arith Le List.
Import ListNotations.
Set Implicit Arguments.

Module Group.

Record Magma := {
  mg_set :> Set;
  mg_op : mg_set -> mg_set -> mg_set;
}.

Infix "#" := (mg_op _) (at level 50, no associativity).

Record SemiGroup := {
  sg_set :> Magma;
  sg_pf_assoc : forall a b c : sg_set, (a # b) # c = a # (b # c)
}.

Record Monoid := {
  mn_set :> SemiGroup;
  mn_ident : mn_set;
  mn_pf_ident_left  : forall a, mn_ident # a = a;
  mn_pf_ident_right : forall a, a # mn_ident = a
}.

Theorem ident_unique_left : forall (M : Monoid) (ident' : M),
  (forall a : M, ident' # a = a) -> ident' = M.(mn_ident).
Proof.
  intros. rewrite <- (H M.(mn_ident)). rewrite M.(mn_pf_ident_right).
  reflexivity.
Qed.

Theorem ident_unique_right : forall (M : Monoid) (ident' : M),
  (forall a : M, a # ident' = a) -> ident' = M.(mn_ident).
Proof.
  intros. rewrite <- (H M.(mn_ident)). rewrite M.(mn_pf_ident_left).
  reflexivity.
Qed.

Record Group := {
  gp_set :> Monoid;
  gp_inv : gp_set -> gp_set;
  gp_pf_inv_left  : forall a, (gp_inv a) # a = gp_set.(mn_ident);
  gp_pf_inv_right : forall a, a # (gp_inv a) = gp_set.(mn_ident)
}.

Theorem inv_ident : forall G : Group, G.(gp_inv) G.(mn_ident) = G.(mn_ident).
Proof.
  pose (inv_left ident) as H. rewrite ident_right in H. exact H.
Qed.

Theorem inv_unique_left : forall a a', a' # a = ident -> a' = inv a.
Proof.
  intros. pose (op_assoc a' a (inv a)) as H1. rewrite H in H1.
  rewrite inv_right in H1. rewrite ident_left,ident_right in H1.
  symmetry. exact H1.
Qed.

Theorem inv_unique_right : forall a a', a # a' = ident -> a' = inv a.
Proof.
  intros. pose (op_assoc (inv a) a a') as H1. rewrite H in H1.
  rewrite inv_left in H1. rewrite ident_left,ident_right in H1.
  exact H1.
Qed.

Theorem inv_inv : forall a, inv (inv a) = a.
Proof.
  intros. symmetry. apply inv_unique_left. apply inv_right.
Qed.

Theorem div_unique_left : forall a b c, a # b = a # c -> b = c.
Proof.
  intros. rewrite <- (ident_left b). rewrite <- (ident_left c).
  rewrite <- (inv_left a). repeat rewrite op_assoc. rewrite H. reflexivity.
Qed.

Theorem div_unique_right : forall a b c, b # a = c # a -> b = c.
Proof.
  intros. rewrite <- (ident_right b). rewrite <- (ident_right c).
  rewrite <- (inv_right a). repeat rewrite <- op_assoc. rewrite H. reflexivity.
Qed.

Theorem inv_op_distr : forall a b, inv (a # b) = (inv b) # (inv a).
Proof.
  intros. apply div_unique_left with (a:=(a # b)). rewrite inv_right.
  rewrite op_assoc. rewrite <- (op_assoc b). rewrite inv_right.
  rewrite ident_left. rewrite inv_right. reflexivity.
Qed.

Fixpoint exp (a : X) (n : nat) : X :=
  match n with
    | O => ident
    | S p => a # (exp a p)
  end.

Infix "^" := exp.

Theorem exp_add : forall a n m, a^n # a^m = a^(n + m).
Proof.
  induction n; intros.
  - simpl. apply ident_left.
  - simpl. rewrite op_assoc. rewrite IHn. reflexivity.
Qed.

Theorem exp_mult : forall a n m, (a^n)^m = a^(n * m).
Proof.
  induction m; intros; simpl.
  - rewrite <- mult_n_O. simpl. reflexivity.
  - rewrite IHm. rewrite <- mult_n_Sm. rewrite plus_comm. apply exp_add.
Qed.

Lemma exp_right : forall a n, a^n # a = a # a^n.
Proof.
  induction n; intros; simpl.
  - rewrite ident_left,ident_right. reflexivity.
  - rewrite op_assoc. rewrite IHn. reflexivity.
Qed.

Theorem exp_distr : forall a b n, (a # b)^n = inv ((inv b # inv a)^n).
Proof.
  induction n; intros; simpl.
  - symmetry. apply inv_ident.
  - rewrite inv_op_distr. rewrite <- IHn. rewrite inv_op_distr.
    repeat rewrite inv_inv. rewrite exp_right. reflexivity.
Qed.

End Group.

Record Subset := {
  ss_universe :> Set;
  ss_restriction : ss_universe -> Prop
}.

Record Group

Definition evens := {|ss_universe := nat; ss_restriction := Even.even|}.

Definition subset 

Definition injection (X Y : Set) (f : X -> Y) : Prop :=
  forall x1 x2 : X, f x1 = f x2 -> x1 = x2.

Definition subgroup (H G : Group ...)