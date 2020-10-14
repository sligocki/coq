Require Import Arith.

(* This function takes a function f and repeats it reps times 
   starting with initial value init. *)
Fixpoint repeat {X} (f : X -> X) (reps : nat) (init : X) :=
  match reps with
  | O => init
  | S reps' => f (repeat f reps' init)
  end.

Fixpoint fast (k n : nat) : nat :=
  match k with
  | O => S n
  | S k' => repeat (fast k') (S n) n
  end.

Example fast_ex0: fast 0 13 = 14. (* S 13 *)
reflexivity. Qed.

Example fast_ex1: fast 1 13 = 27. (* 2 * 13 + 1 *)
simpl. reflexivity. Qed.

Example fast_ex2: fast 1 0 = 1.
simpl. reflexivity. Qed.

Lemma plus_n_1: forall n, n + 1 = S n.
Proof.
  intros. rewrite <- plus_Snm_nSm. rewrite plus_0_r. reflexivity.
Qed.

Lemma fast_k0: forall n, fast 0 n = n + 1.
Proof. intros. simpl. rewrite plus_n_1. reflexivity. Qed.

Lemma repeat_fast_k0: forall reps init,
  repeat (fast 0) reps init = reps + init.
Proof.
  intros. simpl.
  induction reps.
  - reflexivity.
  - simpl. rewrite -> IHreps. reflexivity.
Qed.

Lemma fast_k1: forall n, fast 1 n = 2 * n + 1.
Proof.
  unfold fast. intros. rewrite -> repeat_fast_k0. simpl.
  rewrite plus_0_r. rewrite plus_n_1. reflexivity.
Qed.

Example fast_ex3: fast 2 0 = 1.  (* 2^1 * 0 + (2^1 - 1) *)
reflexivity. Qed.

Example fast_ex4: fast 2 1 = 7.  (* 2^2 * 1 + (2^2 - 1) *)
reflexivity. Qed.

Example fast_ex5: fast 2 2 = 23.  (* 2^3 * 2 + (2^3 - 1) *)
reflexivity. Qed.

Lemma fast_n0: forall k, fast k 0 = 1.
Proof.
  induction k.
  - reflexivity.
  - simpl. apply IHk.
Qed.

Lemma gen_mono: forall f : nat -> nat,
  (forall x, f x <= f (S x)) -> (forall x y, x <= y -> f x <= f y).
Proof.
  intros.
  apply le_plus_minus in H0.
  rewrite -> H0.
  generalize (y - x).  
  induction n.
  - rewrite plus_0_r. reflexivity.
  - rewrite <- plus_Snm_nSm. simpl.
    apply le_trans with (m:=f (x + n)). apply IHn. apply H.
Qed.

Lemma repeat_mono_init: forall f reps init_x init_y,
  (forall x y, x <= y -> f x <= f y)
  -> init_x <= init_y
  -> repeat f reps init_x <= repeat f reps init_y.
Proof.
  intros.
  induction reps.
  - simpl. apply H0.
  - simpl. apply H. apply IHreps.
Qed.

Lemma repeat_mono_reps: forall f reps_x reps_y init,
  (forall x, x <= f x)
  -> reps_x <= reps_y
  -> repeat f reps_x init <= repeat f reps_y init.
Proof.
  intros f reps_x reps_y init H_f_incr.
  apply gen_mono with (f:=fun reps => repeat f reps init).
  induction x.
   - simpl. apply H_f_incr.
   - simpl. simpl in IHx. apply H_f_incr.
Qed.

Theorem fast_incr: forall k n : nat, n <= fast k n.
Proof.
  induction k.
  - intros. simpl. apply le_n_Sn.
  - intros. simpl. induction n.
    + apply le_0_n.
    + simpl. apply le_trans with (m:=repeat (fast k) n (S n)).
      * { apply le_trans with (m:=repeat (fast k) 0 (S n)).
        - simpl. apply le_refl.
        - apply repeat_mono_reps.
          + apply IHk.
          + apply le_0_n. }
      * { apply le_trans with (m:=fast k (repeat (fast k) n (S n))).
        - apply IHk.
        - apply IHk. }
Qed.

Theorem fast_mono_n: forall k nx ny : nat,
  nx <= ny -> fast k nx <= fast k ny.
Proof.
  intros k.
  induction k.
  - intros. simpl. apply le_n_S. apply H.
  - apply gen_mono. intros. simpl.
    apply le_trans with (m:=fast k (repeat (fast k) x (S x))).
    + apply IHk. apply repeat_mono_init.
      * exact IHk.
      * apply le_n_Sn.
    + apply IHk. apply fast_incr.
Qed.

Theorem fast_mono_k: forall kx ky n : nat,
  kx <= ky -> fast kx n <= fast ky n.
Proof.
  intros kx ky n.
  generalize dependent ky.
  generalize dependent kx.
  apply gen_mono.
  simpl.
  intros.
  destruct n.
  - simpl. reflexivity.
  - simpl. apply fast_mono_n.
    apply le_trans with (m:=repeat (fast x) n (S n)).
    + apply le_trans with (m:=repeat (fast x) 0 (S n)).
      * simpl. apply le_refl.
      * { apply repeat_mono_reps.
        - apply fast_incr.
        - apply le_0_n. }
    + apply fast_incr.
Qed.

Function succ (f : nat -> nat) : nat -> nat := 
  fun n => repeat f (S n) n.

Function limit (seq : nat -> nat -> nat) : nat -> nat :=
  fun n => seq n n.

Function plus_K (f : nat -> nat) (k : nat) : nat -> nat :=
  match k with
  | O => f
  | S k' => succ (plus_K f k')
  end.

Theorem plus_K_eq: forall k n, plus_K S k n = fast k n.
Proof.
  induction k.
  - reflexivity.
  - intros. simpl. unfold succ.

Function plus_w f := limit (plus_K f).
Function plus_2w f := limit (plus_K (plus_w f)).

Function plus_Kw f k :=
  match k with
  | O => f
  | S k' => limit (plus_K (plus_Kw f k'))
  end.

Function plus_w2 f := limit (plus_Kw f).
Function plus_2w2 f := limit (plus_Kw (plus_w2 f)).

Function plus_Kw2 f k :=
  match k with
  | O => f
  | S k' => limit (plus_Kw (plus_Kw2 f k'))
  end.

Function plus_Kw2' f k := repeat (fun g => limit (plus_Kw g)) k f.

Lemma func_eq: forall X Y Z (f g : X -> Y),
  (forall x, f x = g x)
  -> (forall meta : (X -> Y) -> Z, meta f = meta g).
Proof.
  intros.
Abort.  (* Probably requires Coq.Logic.FunctionExtensionality *)

Axiom functional_extensionality : forall A B (f g : A -> B),
  (forall x, f x = g x) -> f = g.

Theorem plus_Kw2_eq: forall f k n, plus_Kw2 f k n = plus_Kw2' f k n.
Proof.
  induction k.
  - intros. reflexivity.
  - intros. simpl. unfold plus_Kw2'. simpl. unfold plus_Kw2' in IHk.
    apply functional_extensionality in IHk. rewrite <- IHk.
    reflexivity.
Qed.

Function plus_KwA f a k :=
  match a with
  | O => plus_K f k
  | S a' => repeat (fun g => limit (plus_KwA g a')) k f
  end.

Theorem plus_KwA_dominance_k1: forall a f,
  (forall x, x <= f x) ->
  (forall x y, x <= y -> f x <= f y) ->
  forall k, exists n0, forall n, n0 <= n ->
  plus_KwA f a k n <= plus_KwA f a (S k) n.
Proof.
  intros. exists 0. intros. induction a.
  - simpl. unfold succ.
    apply le_trans with (m:=repeat (plus_K f k) 1 n).
    + reflexivity.
    + apply repeat_mono_reps. apply plus_

Theorem plus_KwA_dominance_k: forall a f,
  (forall x, x <= f x) ->
  (forall x y, x <= y -> f x <= f y) ->
  forall k1 k2, k1 <= k2 ->
  exists n0, forall n, n0 <= n ->
  plus_KwA f a k1 n <= plus_KwA f a k2 n.
Proof.
  intros. exists 0. intros. apply le_plus_minus in H1. rewrite -> H1.
  generalize (k2 - k1) as dk.
  induction dk.
  - rewrite plus_0_r. reflexivity.
  - rewrite <- plus_n_Sm.
    apply le_trans with (m:=plus_KwA f a (k1 + dk) n).
    + apply IHdk.
    + generalize (k1 + dk) as k. intros k.