Require Import Arith ZArith Div2.

Class Monoid {A : Type} (dot : A -> A -> A) (unit : A) : Prop := {
  dot_assoc : forall x y z : A, (dot (dot x y) z) = (dot x (dot y z));
  unit_left : forall x : A, dot unit x = x;
  unit_right : forall x : A, dot x unit = x
}.

Check Monoid.

Instance ZMult : Monoid Zmult 1%Z.
Proof. split; intros; ring. Qed.

Check ZMult.

Fixpoint power {A : Type} {dot : A -> A -> A} {unit : A} {M : Monoid dot unit}
               (a : A) (n : nat) : A :=
  match n with
    | O => unit
    | S p => dot a (power a p)
  end.

Compute power 2%Z 10%nat.

Require Import Recdef.

Function binary_power_mult (A : Type) (dot : A -> A -> A) (unit : A)
                           (M : Monoid dot unit)
                           (acc x : A) (n : nat) {measure (fun i=>i) n} : A :=
  (* acc * (x ** n) *)
  match n with
    | O => acc
    | _ => if Even.even_odd_dec n
             then binary_power_mult A dot unit M acc (dot x x) (div2 n)
             else binary_power_mult A dot unit M (dot acc x) (dot x x) (div2 n)
  end.
Proof.
  - intros. apply lt_div2. auto with arith.
  - intros. apply lt_div2. auto with arith.
Defined.

Definition binary_power {A : Type} {dot : A -> A -> A} {unit : A}
                        {M : Monoid dot unit} (x : A) (n : nat) :=
  binary_power_mult A dot unit M unit x n.

Compute binary_power 2%Z 10%nat.

Section About_power.

Variable A : Type.
Variable dot : A -> A -> A.
Variable unit : A.
Generalizable Variables A dot unit.
Context `{M : @Monoid A dot unit}.

Ltac monoid_rw :=
  rewrite (@unit_left A dot unit M) ||
  rewrite (@unit_right A dot unit M) ||
  rewrite (@dot_assoc A dot unit M).

Ltac monoid_simpl := repeat monoid_rw.

Local Infix "*" := dot.
Local Infix "**" := power (at level 30, no associativity).

Lemma power_x_plus : forall x n p, x ** (n + p) = x ** n * x ** p.
Proof.
  induction n; intros; simpl.
  - monoid_simpl. trivial.
  - rewrite IHn. monoid_simpl. trivial.
Qed.

Ltac power_simpl := repeat (monoid_rw || rewrite <- power_x_plus).

Lemma power_commute : forall x n p, x ** n * x ** p = x ** p * x ** n.
Proof. intros. power_simpl. auto with arith. Qed.

Lemma power_one : forall x, x ** 1%nat = x.
Proof. intros. simpl. monoid_simpl. trivial. Qed.

Lemma power_commute_with_x : forall x n, x * (x ** n) = (x ** n) * x.
Proof. intros. rewrite <- (power_one x) at 1 4. apply power_commute. Qed.

Lemma power_of_power : forall x n p, (x ** n) ** p = x ** (n * p)%nat.
Proof.
  induction p; intros; simpl.
  - rewrite mult_0_r. simpl. trivial.
  - rewrite IHp. power_simpl. replace (n + n * p)%nat with (n * S p)%nat.
    trivial. ring.
Qed.

Lemma power_S : forall x n, x * (x ** n) = x ** (S n).
Proof.
  intros. rewrite <- (power_one x) at 1. power_simpl.
  replace (1 + n) with (S n). trivial. ring.
Qed.

Lemma sqr : forall x, x ** 2%nat = x * x.
Proof. intros. rewrite <- (power_one x) at 2 3. power_simpl. simpl. trivial. Qed.

Ltac factorize := repeat (
  rewrite <- power_commute_with_x ||
  rewrite <- power_x_plus ||
  rewrite <- sqr ||
  rewrite power_S ||
  rewrite power_of_power).

Lemma power_of_square : forall x n, (x * x) ** n = x ** n * x ** n.
Proof.
  intros. factorize. replace (2 * n)%nat with (n + n). trivial. ring.
Qed.

Lemma binary_power_mult_ok : forall n a x,
  binary_power_mult _ _ _ M a x n = a * x ** n.
Proof.
  intros n; pattern n; apply lt_wf_ind. intros. Abort.