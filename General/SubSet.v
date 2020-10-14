Require Import Omega.
Require Import ArithRing Ring.

(* Isomorphism section *)

(* In all these examples a set/collection is defined by a
   universe U/V and a predicate P/Q. The elements of the
   collection are x : U, P x *)

(* Two collections are isomorphic if there are bijective mappings
   f, g such that: 1) They are closed (elements of P are only
   mapped into Q and vice versa) and 2) they are inverses over
   the domains P and Q. *)
(* Note: This limits us to isomorphisms where the mapping is
   a Coq function. *)
Definition isomorphic U V (P : U -> Prop) (Q : V -> Prop) :=
  exists f g,
    (forall x, P x -> Q (f x)) /\
    (forall x, P x -> g (f x) = x) /\
    (forall y, Q y -> P (g y)) /\
    (forall y, Q y -> f (g y) = y).

(* Predicate which allows entire universe *)
Definition universal_pred {X} : X -> Prop :=
  fun x : X => True.

Notation "{ X | P } ~= { Y | Q }" := (isomorphic X Y P Q)
  (at level 70, no associativity) : type_scope.
Notation "X ~= Y" := (isomorphic X Y universal_pred universal_pred)
  (at level 70, no associativity) : type_scope.

Lemma iso_refl: forall X P, {X|P} ~= {X|P}.
Proof.
  intros. exists (fun x => x). exists (fun x => x).
  repeat split; intros; trivial.
Qed.

Lemma iso_comm: forall X Y P Q, {X|P} ~= {Y|Q} -> {Y|Q} ~= {X|P}.
Proof.
  intros. destruct H as [f [g H]]. exists g. exists f. intuition.
Qed.

Lemma iso_trans: forall X Y Z P Q R,
  {X|P} ~= {Y|Q} -> {Y|Q} ~= {Z|R} -> {X|P} ~= {Z|R}.
Proof.
  intros. destruct H as [f [f' Hf]]. destruct H0 as [g [g' Hg]].
  exists (fun x => g (f (x))). exists (fun z => f' (g' z)).
  intuition.
  - (* f' g' g f *) rewrite H0; intuition.
  - (* g f f' g' *) rewrite H6; intuition.
Qed.

(* Isomorphism examples *)

Example nat_opnat_iso: nat ~= option nat.
  exists (fun n => match n with O => None | S m => Some m end).
  exists (fun on => match on with None => O | Some n => S n end). repeat split.
  - (* nat -> op nat *) intros n _. destruct n; trivial.
  - (* op nat -> nat *) intros op_n _. destruct op_n; trivial.
Qed.

(* nat ~= nat + nat *)
Fixpoint bij_nat_2nat (n : nat) : nat + nat :=
  match n with
    | O => inl O
    | S O => inr O
    | S (S m) => match (bij_nat_2nat m) with
                   | inl k => inl (S k)
                   | inr k => inr (S k)
                 end
  end.

Fixpoint double (n : nat) : nat :=
  match n with
    | O => O
    | S m => S (S (double m))
  end.

Function bij_2nat_nat (x : nat + nat) : nat :=
  match x with
    | inl n => double n
    | inr n => S (double n)
  end.

Lemma nat_2nat_inv2: forall n,
  bij_2nat_nat (bij_nat_2nat n) = n /\ bij_2nat_nat (bij_nat_2nat (S n)) = (S n).
Proof.
  induction n; intuition.
  remember (bij_nat_2nat n) as x. destruct x as [k | k]; simpl.
  - (* x = inl k *) rewrite <- Heqx. simpl. simpl in H. subst. trivial.
  - (* x = inr k *) rewrite <- Heqx. simpl. simpl in H. subst. trivial.
Qed.

Example nat_2nat_iso: nat ~= (nat + nat).
  exists bij_nat_2nat. exists bij_2nat_nat. intuition.
  - apply nat_2nat_inv2.
  - destruct y; unfold bij_2nat_nat.
    + (* bij_nat_2nat (double n) = inl n *) induction n; intuition.
      simpl. rewrite H0. trivial.
    + (* bij_nat_2nat (S (double n)) = inr n *) induction n; intuition.
      simpl. simpl in H0. rewrite H0. trivial.
Qed.


Example not_empty_iso: forall X (x : X), ~ (X ~= Empty_set).
  intros X x [f _]. pose (f x). contradiction.
Qed.


Example not_bool_unit_iso: ~ (bool ~= unit).
  intros [f [g [_ [Hgf [_ Hfg]]]]].
  remember (Hgf true I) as Htrue. clear HeqHtrue.
  remember (Hgf false I) as Hfalse. clear HeqHfalse.
  remember (f true) as ft. remember (f false) as ff. destruct ft. destruct ff.
  rewrite Hfalse in Htrue. inversion Htrue.
Qed.


Fixpoint bij_nat_nat2 (n : nat) : nat * nat :=
  match n with
    | O => (O, O)
    | S m => match (bij_nat_nat2 m) with
               | (x, O) => (O, S x)
               | (x, S y) => (S x, y)
             end
  end.

Lemma bij_nat_nat2_zero: forall n, bij_nat_nat2 (S n) <> bij_nat_nat2 O.
Proof.
  intros. intro contra. simpl in contra. destruct (bij_nat_nat2 n) as [x y].
  destruct y; inversion contra.
Qed.

Lemma bij_nat_nat2_inj: forall n m,
  bij_nat_nat2 n = bij_nat_nat2 m -> n = m.
Proof.
  induction n; intros.
  - (* n = 0 *) destruct m; trivial. symmetry in H. apply bij_nat_nat2_zero in H. contradiction.
  - (* S n *) destruct m.
    + (* m = 0 *) apply bij_nat_nat2_zero in H. contradiction.
    + (* S m *) simpl in H.
      remember (bij_nat_nat2 n) as bn. destruct bn as [n1 n2].
      remember (bij_nat_nat2 m) as bm. destruct bm as [m1 m2].
      destruct n2; destruct m2; inversion H; subst.
      * apply IHn in Heqbm as Heq. subst. trivial.
      * apply IHn in Heqbm as Heq. subst. trivial.
Qed.

Lemma bij_nat_nat2_diag: forall n y p,
  bij_nat_nat2 n = (O, y + p) -> bij_nat_nat2 (n + p) = (p, y).
Proof.
  intros n y p. generalize dependent n. generalize dependent y. induction p; intros.
  - replace (n + 0) with (n); try ring. replace (y + 0) with (y) in H; try ring. trivial.
  - replace (y + S p) with ((S y) + p) in H; try ring. apply IHp in H.
    replace (n + S p) with (S (n + p)); try ring. simpl. rewrite H. trivial.
Qed.


Lemma bij_nat_nat2_reset: forall n y,
  bij_nat_nat2 n = (O, y) -> bij_nat_nat2 (n + y + 1) = (O, S y).
Proof.
  intros. replace (n + y + 1) with (S (n + y)); try ring. simpl.
  replace (bij_nat_nat2 (n + y)) with (y, O). trivial. symmetry.
  apply bij_nat_nat2_diag. simpl. trivial.
Qed.

Lemma bij_nat_nat2_surj_right: forall y, exists n, bij_nat_nat2 n = (O, y).
Proof.
  induction y; intros; simpl.
  - exists O. trivial.
  - destruct IHy as [m Heq]. exists (m + y + 1). apply bij_nat_nat2_reset. trivial.
Qed.

Lemma bij_nat_nat2_surj: forall a, exists n, bij_nat_nat2 n = a.
Proof.
  intros [x y]. destruct (bij_nat_nat2_surj_right (y + x)) as [m Heq0].
  exists (m + x). apply bij_nat_nat2_diag. trivial.
Qed.

Fixpoint triangle (n : nat) : nat :=
  match n with
    | O => O
    | S m => (triangle m) + m
  end.

Function bij_nat2_nat (a : nat * nat) : nat :=
  match a with
    | (x, y) => (triangle (y + x)) + x
  end.

Example nat_nat2_iso: nat ~= (nat * nat).
  exists bij_nat_nat2. exists bij_nat2_nat. intuition.
  - destruct x; simpl; trivial. remember (bij_nat_nat2 x) as bx.
    destruct bx as [a b]. destruct b; simpl.
    + 
Abort.


(* Can I restate these in another way so that I don't need function equality? *)
Example unit_powunit_iso: forall X (x : X), unit ~= (unit -> X).
  intros. exists (fun tt => (fun tt => x)). exists (fun _ => tt). intuition.
  - destruct x0. trivial.
  - (* TODO: Need function equality axiom. *)
Abort.


Example not_nat_pownat_iso: ~ (nat ~= (nat -> nat)).
Abort.


Example pownat_iso: (nat -> nat) ~= (bool -> nat).
Abort.
























