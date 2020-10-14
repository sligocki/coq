Require Import Arith.

(* This function takes a function f and repeats it b times to a *)
Fixpoint repeat (f : nat -> nat -> nat) (a b : nat) :=
  match b with
  | O => 1
  | S b' => f a (repeat f a b')
  end.

Fixpoint up (n a b : nat) : nat :=
  match n with
  | O => b * a
  | S n' => repeat (up n') a b
  end.

Example up_ex0: up 0 2 3 = 6. (* 2 * 3 *)
reflexivity. Qed.

Example up_ex1: up 1 2 3 = 8. (* 2^3 *)
reflexivity. Qed.

Example up_ex2: up 2 2 3 = 16. (* 2^^3 *)
reflexivity. Qed.

Theorem up_b0: forall n a : nat, up (S n) a 0 = 1.
Proof. intros. reflexivity. Qed.

Theorem up_b1: forall n a : nat, up n a 1 = a.
Proof.
  induction n.
  - intros. simpl. apply plus_0_r.
  - intros. simpl. apply IHn.
Qed.

Theorem up_a0: forall n b : nat, up n 0 (S b) = 0.
Proof.
  induction n.
  - intros. simpl. apply mult_0_r.
  - intros. simpl. destruct b.
    + simpl. apply up_b1.
    + 

Theorem up_a2b2: forall n : nat, up n 2 2 = 2 * 2.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite -> up_b1. apply IHn.
Qed.

Lemma up_mono_b: forall n a b : nat, up n a b <= up n a (S b).
Proof.
  induction n.
  - intros. simpl. assert (H: forall x y : nat, y <= x + y). {
      intros.
      induction x.
      + left.
      + right. apply IHx. }
    apply H.
  - induction b.
    + rewrite up_b0. rewrite up_b1.

ge
le

Lemma up_mono_n: forall n a b : nat, up (S n) a b >= up n a b.
Proof.
  intros.
  simpl.
  unfold repeat.

Theorem up2_base_3_10_lower: forall n,
  up 2 10 (S (S n)) < up 2 3 (S (S (S n))).
Proof.
  induction n.
  - simpl. reflexivity.
  - 
