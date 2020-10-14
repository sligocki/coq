Require Import Arith.
Require Import List.
Require Import Omega.

Lemma plus_1 : forall n, S n = n + 1.
intros. rewrite <- plus_n_Sm. rewrite plus_0_r. reflexivity. Qed.

Lemma contrapositive : forall (P Q : Prop), (P -> Q) -> (~Q -> ~P).
intros. intros contra. apply H in contra. contradiction. Qed.

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~P -> reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros. destruct b.
  - apply ReflectT. apply H. reflexivity.
  - apply ReflectF. intros contra. apply H in contra. inversion contra.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros. inversion H.
  - split; intros.
    + reflexivity.
    + trivial.
  - split; intros.
    + contradiction.
    + inversion H2.
Qed.

Theorem reflect_not_iff : forall P b, reflect P b -> (~P <-> b = false).
Proof.
  intros. inversion H.
  - split; intros.
    + contradiction.
    + inversion H2.
  - split; intros.
    + reflexivity.
    + trivial.
Qed. 

Theorem eq_reflect : forall x y, reflect (x = y) (beq_nat x y).
Proof.
  intros. destruct (beq_nat x y) eqn:H; constructor.
  - apply beq_nat_eq. symmetry. apply H.
  - intros contra. rewrite contra in H. rewrite <- beq_nat_refl in H.
    inversion H.
Qed.



Definition divides (n m : nat) : Prop := exists k, n * k = m.
Definition prime (p : nat) : Prop := p > 1 /\ forall n, n > 1 -> n < p -> ~(divides n p).

(* Find k' such that m / (n + 1) = k' and k' <= k. *)
Fixpoint divide_helper n m k :=
  if beq_nat ((S n) * k) m
    then Some k
    else match k with
         | 0 => None
         | S k' => divide_helper n m k'
         end.

Function divide n m := 
  match n with
  | 0 => None
  | S n => divide_helper n m m
  end.

Lemma divide_helper_equiv: forall n m k k',
  divide_helper n m k = Some k' -> (S n) * k' = m /\ k' <= k.
Proof.
  induction k; intros. simpl.
  - destruct m.
    + simpl in H. rewrite mult_0_r in H. rewrite <- beq_nat_refl in H.
      inversion H. omega.
    + simpl in H. destruct (beq_nat (n * 0) (S m)) eqn:H0.
      * symmetry in H0. apply beq_nat_eq in H0. rewrite mult_0_r in H0. inversion H0.
      * inversion H.
  - simpl in H. destruct m.
    + apply IHk in H. destruct H. split; try trivial. constructor. trivial.
    + destruct (beq_nat (k + n * S k) m) eqn:Heq.
      * symmetry in Heq. apply beq_nat_eq in Heq. inversion H. split; trivial.
        simpl. rewrite Heq. reflexivity.
      * apply IHk in H. destruct H. split; try trivial. constructor. apply H0.
Qed.

Lemma divide_helper_equiv2: forall n m k k',
  (S n) * k' = m -> k' <= k -> divide_helper n m k = Some k'.
Proof.
  intros. induction H0.
  - rewrite <- H. clear H m. destruct k'; simpl; rewrite <- beq_nat_refl; reflexivity.
  - rename m0 into k. simpl. destruct m; try trivial.
    destruct (beq_nat (k + n * S k) m) eqn:Heq; try trivial.
    symmetry in Heq. apply beq_nat_eq in Heq. apply mult_le_compat_l with (p:=S n) in H0.
    rewrite H in H0. rewrite <- Heq in H0. assert (contra: ~ (S (k + n * S k) <= S n * k)). {
      clear Heq IHle H0 H k'. apply lt_not_le. rewrite mult_succ_r. rewrite plus_assoc.
      rewrite (plus_comm k). rewrite <- mult_succ_l. generalize (S n * k). 
      intros. unfold lt. apply le_n_S. apply le_plus_l. } contradiction.
Qed.

Theorem divide_mult : forall n m k,
  (divide n m = Some k <-> n > 0 /\ n * k = m).
Proof.
  unfold divide. intros. split; intros.
  - destruct n. inversion H. split. apply gt_Sn_O.
    apply divide_helper_equiv in H. destruct H. trivial.
  - destruct H. destruct n. inversion H. apply divide_helper_equiv2; try trivial.
    rewrite <- H0. unfold gt in H. unfold lt in H.
    apply mult_le_compat_r with (p:=k) in H. rewrite mult_1_l in H. trivial.
Qed.

Function dividesb (n m : nat) : bool :=
  match m, n with
  | 0, 0 => true
  | _, _ => match divide n m with
         | Some _ => true
         | None => false
         end
  end.

Theorem divides_reflect: forall n m, reflect (divides n m) (dividesb n m).
Proof.
  intros. unfold dividesb. destruct m.
  - destruct n.
    + constructor. exists 0. apply mult_0_r.
    + unfold divide. unfold divide_helper. rewrite mult_0_r.
      rewrite <- beq_nat_refl. constructor. exists 0. apply mult_0_r.
  - destruct (divide n (S m)) as [k|] eqn:H; constructor.
    + apply divide_mult in H. destruct H. exists k. trivial.
    + intros contra. destruct contra as [k contra].
      assert (H': divide n (S m) = Some k). {
        apply divide_mult. split; try trivial. destruct n.
        * rewrite mult_0_l in contra. inversion contra.
        * apply gt_Sn_O. } rewrite H' in H. inversion H.
Qed.

Theorem divides_iff: forall n m, divides n m <-> dividesb n m = true.
intros. apply reflect_iff. apply divides_reflect. Qed.

Fixpoint smallest_factor_helper n k :=
  match k with
  | 0 => None
  | S k' =>
    match divide (S k) n with
    | Some x => Some (x, (S k))
    | None => smallest_factor_helper n k'
    end
  end.

Function smallest_factor n :=
  match n with
  | 0 => None
  | 1 => None
  | S (S n') => smallest_factor_helper n n'
  end.

Example smallest_factor_ex1: smallest_factor 13 = None.
reflexivity. Qed.

Example smallest_factor_ex2: smallest_factor (2 * 3) = Some (2, 3).
reflexivity. Qed.

Example smallest_factor_ex3: smallest_factor 0 = None.
reflexivity. Qed.

Example smallest_factor_ex4: smallest_factor 1 = None.
reflexivity. Qed.

Example smallest_factor_ex5: smallest_factor 35 = Some (5, 7).
reflexivity. Qed.

Lemma smallest_factor_helper_mult: forall n k x y,
  smallest_factor_helper n k = Some (x, y) -> y > 1 /\ y <= S k /\ x * y = n.
Proof.
  induction k; intros.
  - simpl in H. inversion H.
  - simpl in H. destruct (divide_helper (S k) n n) eqn:Hdiv.
    + apply divide_helper_equiv in Hdiv. destruct Hdiv. inversion H.
      rewrite <- H3. rewrite mult_comm. split; try split; trivial. omega.
    + apply IHk in H. destruct H as [Hy1 [HySk Hmult]]. split; try split; trivial. omega.
Qed.

Theorem smallest_factor_mult: forall n x y,
  smallest_factor n = Some (x, y) -> x > 1 /\ y > 1 /\ x * y = n.
Proof.
  intros. unfold smallest_factor in H. destruct n as [|[|n']]; inversion H; try reflexivity.
  clear H1. apply smallest_factor_helper_mult in H. destruct H as [Hy1 [HySn Hmult]].
  split; try split; trivial. apply not_le. intros contra.
  apply (mult_le_compat x 1 y (S n')) in contra; trivial. rewrite Hmult in contra. omega.
Qed.

Lemma smallest_factor_helper_none: forall n k,
  smallest_factor_helper n k = None ->
  ~ exists x y, x * y = n /\ x > 1 /\ y > 1 /\ y <= S k.
Proof.
  intros. intros contra. destruct contra as [x [y [contra [Hx1 [Hy1 HySk]]]]].
  induction k.
  - omega.
  - apply IHk.
    + simpl in H. destruct (divide_helper (S k) n n).
       * inversion H.
       * trivial.
    + apply not_gt. intros Hgt. unfold gt in Hgt. unfold lt in Hgt.
      apply (le_antisym _ _ Hgt) in HySk. simpl in H.
      remember (divide_helper (S k) n n) as div. destruct div.
      * inversion H.
      * assert (Hdiv: divide_helper (S k) n n = Some x). {
          apply divide_helper_equiv2.
          - rewrite HySk. rewrite mult_comm. trivial.
          - rewrite <- contra. assert (H': x * 1 <= x * y). {
              apply mult_le_compat_l. apply lt_le_weak. trivial. }
            rewrite mult_1_r in H'. trivial. }
        rewrite Hdiv in Heqdiv. inversion Heqdiv.
Qed.

Theorem smallest_factor_none: forall n,
  smallest_factor n = None ->
  ~ exists x y, x * y = n /\ x > 1 /\ y > 1.
Proof.
  intros. intros contra. destruct contra as [x [y [contra [Hx1 Hy1]]]].
  unfold smallest_factor in H. destruct n as [|[|n']].
  - apply mult_is_O in contra. destruct contra.
    + rewrite H0 in Hx1. inversion Hx1.
    + rewrite H0 in Hy1. inversion Hy1.
  - apply mult_is_one in contra. destruct contra. rewrite H0 in Hx1.
    apply lt_irrefl in Hx1. contradiction.
  - apply smallest_factor_helper_none in H. apply H. exists x. exists y.
    split; try split; try split; trivial. apply not_gt. intros Hgt.
    unfold gt in *. unfold lt in *. apply (mult_le_compat _ _ _ _ Hx1) in Hgt.
    rewrite contra in Hgt. assert (H': 2 * S (S n') > 1 * S (S n')). {
      apply mult_lt_compat_r.
      + repeat constructor.
      + unfold lt. apply le_n_S. apply le_O_n. }
    apply lt_not_le in H'. rewrite mult_1_l in H'. contradiction.
Qed.

Lemma mult_lt_reg_l: forall n m p, n * m < n * p -> m < p.
Proof.
  intros. apply not_ge. unfold ge. intros contra.
  apply mult_le_compat_l with (p:=n) in contra. apply lt_not_le in H. contradiction.
Qed.

Lemma mult_lt_compat: forall n m p q, n < m -> p < q -> n * p < m * q.
Proof.
  intros. destruct n. 
  - rewrite mult_0_l. apply (mult_lt_compat_r 0 m q) in H; omega.
  - apply lt_trans with (m:=(S n)*q).
    + apply mult_lt_compat_l; trivial. omega.
    + apply mult_lt_compat_r; trivial. omega.
Qed.

Lemma smallest_factor_helper_none2: forall n k,
  (forall x y, x > 1 -> y > 1 -> x * y <> n) -> S (S k) <= n ->
  smallest_factor_helper n k = None.
Proof.
  induction k; intros.
  - simpl. reflexivity.
  - simpl. destruct (divide_helper (S k) n n) eqn:Hdiv.
    + apply divide_helper_equiv in Hdiv. destruct Hdiv as [Hdiv _].
      apply le_lt_n_Sm in H0. apply lt_S_n in H0. rewrite <- Hdiv in H0.
      assert (contra: S (S k) * 1 < S (S k) * n0). { rewrite mult_1_r. trivial. }
      apply mult_lt_reg_l in contra. apply H in Hdiv.
      * contradiction.
      * apply lt_n_S. apply lt_0_Sn.
      * trivial.
    + apply IHk. trivial. apply le_Sn_le. trivial.
Qed.

Theorem smallest_factor_none2: forall n,
  (forall x y, x > 1 -> y > 1 -> x * y <> n) ->
  smallest_factor n = None.
Proof.
  intros. unfold smallest_factor. destruct n as [|[|k]]; try reflexivity.
  apply smallest_factor_helper_none2; trivial.
Qed.

Theorem smallest_factor_prime: forall p, prime p <-> (p > 1 /\ smallest_factor p = None).
Proof.
  split; intros.
  - destruct H. split; trivial. apply smallest_factor_none2. intros. intros contra.
    apply H0 in H1.
    + apply H1. exists y. trivial.
    + rewrite <- contra. apply mult_lt_compat_l with (p:=x) in H2.
      * rewrite mult_1_r in H2. trivial.
      * apply lt_trans with (m:=1); trivial. constructor.
  - destruct H. apply smallest_factor_none in H0. split; trivial. intros. intros contra.
    apply H0. destruct contra. exists n. exists x. split; try split; trivial.
    rewrite <- H3 in H2. apply mult_lt_reg_l with (n:=n). rewrite mult_1_r. trivial.
Qed.

Lemma smallest_factor_prime2: forall p, p > 1 -> smallest_factor p = None -> prime p.
intros. apply smallest_factor_prime. split; assumption. Qed.

Lemma le_eq_or_lt: forall x y, x <= S y -> x = S y \/ x <= y.
Proof.
  intros. inversion H.
  - left. reflexivity.
  - right. trivial.
Qed.

Lemma smallest_factor_helper_largest: forall n k x y,
  smallest_factor_helper n k = Some (x, y) ->
  forall z, divides z n -> z <= S k -> z <= y.
Proof.
  induction k; intros.
  - simpl in H. inversion H.
  - simpl in H. destruct (divide_helper (S k) n n) eqn:Hdiv.
    + inversion H. trivial.
    + apply IHk with (x:=x); try trivial. apply le_eq_or_lt in H1.
      destruct H1; try trivial. destruct H0 as [w H0]. rewrite H1 in H0.
      apply divide_helper_equiv2 with (k:=n) in H0.
      * rewrite H0 in Hdiv. inversion Hdiv.
      * rewrite <- H0. destruct (mult_O_le w (S (S k))). inversion H2. trivial.
Qed.

Lemma smallest_factor_largest: forall n x y,
  smallest_factor n = Some (x, y) -> forall k, divides k n -> k < n -> k <= y.
Proof.
  intros. unfold smallest_factor in H. destruct n as [|[|n']]; try inversion H.
  apply smallest_factor_helper_largest with (z:=k) in H; trivial. omega.
Qed.

Lemma plus_reg_r: forall n m p, n + p = m + p -> n = m.
Proof. intros. rewrite plus_comm in H. rewrite (plus_comm m) in H.
apply plus_reg_l in H. trivial. Qed.

Lemma mult_reg_l: forall a b c, a > 0 -> a * b = a * c -> b = c.
Proof.
  induction b; intros c Ha0 H.
  - rewrite mult_0_r in H. symmetry in H. apply mult_is_O in H. destruct H.
    + rewrite H in Ha0. inversion Ha0.
    + symmetry. trivial.
  - destruct c.
    + rewrite mult_0_r in H. apply mult_is_O in H. destruct H; trivial.
      rewrite H in Ha0. inversion Ha0.
    + rewrite mult_succ_r in H. rewrite mult_succ_r in H. apply plus_reg_r in H.
      apply IHb in H; trivial. rewrite H. reflexivity.
Qed.

Lemma factoring_size: forall a b c d, a > 0 -> a * b = c * d -> a <= c -> d <= b.
Proof.
  intros a b c d Ha0 H Hac. destruct (le_or_lt d b); trivial.
  apply le_lt_or_eq in Hac. destruct Hac.
  - apply (mult_lt_compat a c b d) in H1; trivial. rewrite <- H in H1.
    apply lt_irrefl in H1. contradiction.
  - rewrite <- H1 in H. apply mult_lt_compat_l with (p:=a) in H0; trivial.
    rewrite H in H0. apply lt_irrefl in H0. contradiction.
Qed.

Lemma gt_0_ne_0: forall n, n > 0 <-> n <> 0.
Proof.
  split; intros.
  - intros contra. rewrite contra in H. inversion H.
  - destruct n.
    + assert (contra: 0 = 0). { reflexivity. } contradiction.
    + apply gt_Sn_O.
Qed.

Lemma mult_is_not_O: forall n m, n * m <> 0 -> n <> 0 /\ m <> 0.
Proof.
  intros. split; intros contra; rewrite contra in H.
  - rewrite mult_0_l in H. pose (eq_refl 0) as H'. contradiction.
  - rewrite mult_0_r in H. pose (eq_refl 0) as H'. contradiction.
Qed.

Theorem smallest_factor_smallest: forall n x y, n > 0 ->
  smallest_factor n = Some (x, y) -> forall k, divides k n -> k > 1 -> x <= k.
Proof.
  intros n x y Hn0 Hsmall k Hdiv Hk1. destruct Hdiv as [m Hdiv].
  apply gt_0_ne_0 in Hn0. rewrite <- Hdiv in Hn0. apply mult_is_not_O in Hn0.
  destruct Hn0 as [Hk0 Hm0]. apply (factoring_size m _ y).
  - apply gt_0_ne_0. trivial.
  - apply smallest_factor_mult in Hsmall. rewrite mult_comm. rewrite Hdiv.
    rewrite mult_comm. destruct Hsmall as [_ [_ Hmult]]. rewrite Hmult. reflexivity.
  - apply smallest_factor_largest with (n:=n) (x:=x); trivial.
    + exists k. rewrite mult_comm. trivial.
    + rewrite <- Hdiv. unfold gt in Hk1. apply mult_lt_compat_r with (p:=m) in Hk1.
      * rewrite mult_1_l in Hk1. trivial.
      * apply gt_0_ne_0 in Hm0. unfold gt in Hm0. trivial.
Qed.

Theorem smallest_factor_is_prime: forall n x y,
  smallest_factor n = Some (x, y) -> prime x.
Proof.
  intros. split.
  - apply smallest_factor_mult in H. destruct H as [Hx1 [Hy1 Hn]]. apply Hx1.
  - intros z Hz1 Hzn Hdiv. destruct Hdiv as [w Hx]. assert (Hdiv: divides z n). { 
      exists (w * y). rewrite mult_assoc. rewrite Hx.
      apply smallest_factor_mult in H. destruct H as [_ [_ Hn]]. trivial. }
    apply smallest_factor_smallest with (k:=z) in H; try omega; trivial.
    apply not_le. intros contra. apply le_n_0_eq in contra.
    rewrite <- contra in H. simpl in H. inversion H.
Qed.

Fixpoint prod ns :=
  match ns with
  | nil => 1
  | n :: ns' => n * prod ns'
  end.

Lemma divides_mult: forall n m x, divides n m -> divides n (m * x).
Proof.
  intros. destruct H as [k H]. exists (k * x). rewrite <- H. rewrite mult_assoc.
  reflexivity.
Qed.

Lemma divides_prod: forall n ns, In n ns -> divides n (prod ns).
Proof.
  induction ns; intros.
  - inversion H.
  - simpl in H. destruct H.
    + rewrite H. simpl. exists (prod ns). reflexivity.
    + simpl. rewrite mult_comm. apply divides_mult. apply IHns. apply H.
Qed.

Lemma divides_plus: forall n x y, divides n x -> divides n y -> divides n (x + y).
Proof.
  intros. destruct H as [k H]. destruct H0 as [j H0]. exists (k + j).
  rewrite mult_plus_distr_l. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma divides_minus: forall n x y, divides n x -> divides n (x + y) -> divides n y.
Proof.
  intros. destruct H as [k H]. destruct H0 as [j H0]. exists (j - k).
  rewrite mult_minus_distr_l. rewrite H. rewrite H0. apply minus_plus.
Qed.

Lemma divides_1: forall n, n > 1 -> ~divides n 1.
Proof.
  intros. intros contra. destruct contra as [k contra].
  apply mult_is_one in contra. destruct contra. rewrite H0 in H.
  inversion H. inversion H3.
Qed.

Lemma divides_plus_1: forall n m, n > 1 -> divides n m -> ~divides n (m + 1).
Proof.
  intros. intros contra.
  apply divides_minus with (y:=1) in H0; try apply contra.
  apply divides_1 in H. contradiction.
Qed.

Lemma le_prod_one: forall xs, 
  (forall y, In y xs -> y >= 1) ->
  (prod xs) >= 1.
Proof.
  induction xs; intros.
  - simpl. constructor.
  - simpl. replace (1) with (1 * 1); try reflexivity. apply mult_le_compat.
    + apply H. simpl. left. reflexivity.
    + apply IHxs. intros. apply H. simpl. right. trivial.
Qed.

Lemma le_prod: forall xs, 
  (forall y, In y xs -> y >= 1) ->
  forall x, In x xs -> x <= (prod xs).
Proof.
  intros. generalize dependent x. induction xs; intros.
  - inversion H0.
  - simpl in H0. destruct H0.
    + simpl. rewrite H0. assert (Hprod: x * 1 <= x * prod xs). {
        apply mult_le_compat_l. apply le_prod_one. intros. apply H.
        simpl. right. trivial. }
      rewrite mult_1_r in Hprod. trivial.
    + simpl. assert (Hprod: 1 * x <= a * prod xs). { apply mult_le_compat.
      * apply H. simpl. left. reflexivity.
      * apply IHxs; trivial. intros. apply H. simpl. right. trivial. }
      rewrite mult_1_l in Hprod. trivial.
Qed.

Theorem infinite_primes: forall ps : list nat, 
  (forall p, In p ps -> prime p) ->
  exists q, ~(In q ps) /\ prime q.
Proof.
  intros. remember ((prod ps) + 1) as big. remember (smallest_factor big) as f.
  destruct f.
  - (* big is composite *) destruct p as [x y]. symmetry in Heqf. exists x. split.
    + intros contra. apply smallest_factor_mult in Heqf. destruct Heqf as [Hx1 [Hy1 Hmult]].
      assert (div: divides x (prod ps)). { apply divides_prod. trivial. }
      apply divides_plus_1 in div; trivial. apply div. exists y. rewrite <- Heqbig. trivial.
    + apply smallest_factor_is_prime in Heqf. trivial.

  - (* big is prime *) symmetry in Heqf. exists big. split.
    + intros contra. apply le_prod in contra.
      * rewrite Heqbig in contra. rewrite <- plus_1 in contra.
        apply le_Sn_n in contra. contradiction.
      * intros. apply H in H0. destruct H0. apply lt_le_weak. trivial.
    + (* prime big *) apply smallest_factor_prime. split; trivial. rewrite Heqbig.
      (* prod ps + 1 > 1 *) assert (Hprod: prod ps >= 1). { apply le_prod_one.
        intros p Hin. apply H in Hin. apply not_le. intros contra.
        apply le_n_0_eq in contra. rewrite <- contra in Hin.
        (* ~ prime 0 *) destruct Hin. omega. } omega.
Qed.

Notation "[ x ]" := (x :: nil). (* TODO: Why is this needed? *)

Theorem gen_nat_induction: forall P,
  (forall n, (forall m, m < n -> P m) -> P n) -> forall n, P n.
Proof.
  intros P Hind n. apply Hind. induction n.
  - intros. omega.
  - intros. apply Hind. intros. apply IHn. omega.
Qed.

Inductive prime_factor : nat -> list nat -> Prop :=
  | pfact_prime : forall p, smallest_factor p = None -> prime_factor p [p]
  | pfact_comp : forall n p m ps,
      smallest_factor n = Some (p, m) -> prime_factor m ps -> prime_factor n (p :: ps).

Theorem prime_factor_exists: forall n, exists ps, prime_factor n ps.
Proof.
  apply gen_nat_induction. intros. destruct (smallest_factor n) as [[p m] |] eqn:Hsmall.
  - destruct (H m) as [ps Hprime].
    + apply smallest_factor_mult in Hsmall.
      destruct Hsmall as [Hp1 [Hm1 Hmult]].
      apply mult_lt_compat_r with (p:=m) in Hp1; omega.
    + exists (p :: ps). apply pfact_comp with (m:=m); assumption.
  - exists [n]. apply pfact_prime. assumption.
Qed.

Theorem prime_factor_mult: forall n ps, prime_factor n ps -> n = prod ps.
Proof.
  intros n ps. generalize dependent n. induction ps.
  - intros. inversion H.
  - intros. simpl. inversion H.
    + simpl. rewrite mult_1_r. reflexivity.
    + apply IHps in H4. rewrite <- H4. apply smallest_factor_mult in H3.
      destruct H3 as [_ [_ Hmult]]. symmetry. assumption.
Qed.

Theorem prime_factor_prime: forall n ps,
  n > 1 -> prime_factor n ps -> (forall p, In p ps -> prime p).
Proof.
  intros n ps. generalize dependent n. induction ps as [| q ps]; intros.
  - inversion H1.
  - simpl in H1. destruct H1.
    + subst. inversion H0.
      * subst. apply smallest_factor_prime. split; assumption.
      * subst. apply smallest_factor_is_prime in H4. assumption.
    + inversion H0.
      * subst. inversion H1.
      * subst. apply (IHps m); try assumption.
        apply smallest_factor_mult in H5. destruct H5 as [_ [Hm1 _]]. apply Hm1.
Qed.

Theorem prime_factor_singular: forall n ps1 ps2,
  prime_factor n ps1 -> prime_factor n ps2 -> ps1 = ps2.
Proof.
  intros n ps. generalize dependent n. induction ps as [| p ps]; intros
  ; inversion H; inversion H0; subst.
  - (* ps1 = [p] = ps2 *) reflexivity.
  - (* ps1 = [p]; ps2 = p1 :: ps0 *) rewrite H5 in H3. inversion H3.
  - (* ps1 = p :: ps; ps2 = [p] *) rewrite H6 in H4. inversion H4.
  - (* ps1 = p :: ps; ps2 = p1 ::ps1 *) rewrite H6 in H4. inversion H4. subst.
    apply (IHps m ps1) in H5. rewrite H5. reflexivity. assumption.
Qed.

Inductive InOrder : list nat -> Prop :=
  | in_order_nil : InOrder nil
  | in_order_one : forall n, InOrder [n]
  | in_order_cons : forall x n ns, x <= n -> InOrder (n :: ns) -> InOrder (x :: n :: ns).

Theorem prime_factor_in_order: forall n ps, prime_factor n ps -> InOrder ps.
Proof.
  intros n ps. generalize dependent n. induction ps as [| p1 [| p2 ps]]; intros.
  - apply in_order_nil.
  - apply in_order_one.
  - inversion H. subst. apply in_order_cons.
    + destruct n as [|[|n']]; inversion H3. clear H1.
      apply (smallest_factor_smallest (S (S n')) p1 m).
      * (* n > 0 *) omega. 
      * assumption.
      * apply prime_factor_mult in H. rewrite H. apply divides_prod. simpl.
        right. left. reflexivity.
      * (* p2 > 1 *) { apply prime_factor_prime with (p:=p2) in H.
        - destruct H. assumption.
        - omega.
        - simpl. right. left. reflexivity. }
    + apply (IHps m). assumption.
Qed.

Theorem prime_divides_factor: forall p ns,
  prime p -> divides p (prod ns) -> exists n, In n ns /\ divides p n.
Proof.
Abort.

Theorem prime_factor_unique: forall n ps qs,
  n > 1 -> prime_factor n ps ->
  n = prod qs -> (forall q, In q qs -> prime q) -> InOrder qs ->
  ps = qs.
Proof.
  intros n ps qs. generalize dependent ps. generalize dependent n.
  induction qs as [| q1 [| q2 qs]]; intros.
  - simpl in H1. rewrite H1 in H. omega.
  - simpl in H1. rewrite mult_1_r in H1. subst. inversion H0; subst; try reflexivity.
    assert (Hprime: prime q1). { apply H2. simpl. left. reflexivity. }
    apply smallest_factor_prime in Hprime. destruct Hprime. rewrite H6 in H1.
    inversion H1.
  - inversion H0.
    + admit.
    + 
Abort.

Lemma prime_gt_1: forall p, prime p -> p > 1.
intros. destruct H. assumption. Qed.

Lemma prod_prime_gt_1: forall p ps,
  (forall q, In q (p :: ps) -> prime q) -> prod (p :: ps) > 1.
Proof.
  intros. apply le_trans with (m:=p).
  - apply prime_gt_1. apply H. left. reflexivity.
  - apply le_prod.
    + intros. apply lt_le_weak. apply prime_gt_1. apply H. apply H0.
    + left. reflexivity.
Qed.

(* divmod k n d m <-> n = k * d + m /\ m < k *)
Inductive divmod : nat -> nat -> nat -> nat -> Prop :=
  | divmod_base : forall k n, n < k -> divmod k n 0 n
  | divmod_incr : forall k n d m, divmod k n d m -> divmod k (n + k) (S d) m.

Theorem divmod_complete: forall k n, k > 0 -> exists d m, divmod k n d m.
Proof.
  intros k n. apply gen_nat_induction with (n:=n). clear n. intros.
  destruct (le_or_lt k n).
  - (* k <= n *) assert (Hdiv: exists d m, divmod k (n - k) d m). {
      apply H; [|assumption]. apply lt_minus; assumption. }
    destruct Hdiv as [d [m Hdiv]]. exists (S d). exists m.
    remember (n - k) as n'. replace (n) with (n' + k).
    + apply divmod_incr. assumption.
    + omega.
  - (* n < k *) exists 0. exists n. apply divmod_base. assumption.
Qed.

Theorem divmod_equiv: forall k n d m, divmod k n d m <-> n = k * d + m /\ m < k.
Proof.
  split.
  - generalize dependent n. induction d; intros.
    + inversion H. split. ring. assumption.
    + inversion H. subst. apply IHd in H3. destruct H3. split; [| assumption].
      rewrite H0. ring.
  - generalize dependent n. induction d; intros.
    + destruct H. rewrite mult_0_r in H. rewrite plus_0_l in H. rewrite H.
      apply divmod_base. assumption.
    + destruct H. rewrite H. replace (k * S d + m) with ((k * d + m) + k).
      * apply divmod_incr. apply IHd. split; trivial.
      * ring.
Qed.

Theorem divmod_divides: forall k n, k > 0 ->
  ((exists d, divmod k n d 0) <-> divides k n).
Proof.
  intros k n Hk0. split; intros.
  - destruct H as [d H]. exists d. apply divmod_equiv in H. destruct H. rewrite H. ring.
  - destruct H as [d H]. exists d. apply divmod_equiv. split; [|assumption].
    rewrite H. ring.
Qed.

Theorem divmod_not_divides: forall k n, k > 0 ->
  ((~ exists d, divmod k n d 0) <-> ~ divides k n).
Proof.
  intros. split; intros.
  - intros contra. apply divmod_divides in contra. contradiction. assumption.
  - intros contra. apply divmod_divides in contra. contradiction. assumption.
Qed.

Theorem divmod_not_divides2: forall k n, k > 0 ->
  ~ divides k n -> exists d m, m <> 0 /\ divmod k n d m.
Proof.
  intros. assert (Hdiv: exists d m, divmod k n d m). { apply divmod_complete.
    assumption. } destruct Hdiv as [d [m Hdiv]]. exists d. exists m. split; [|assumption].
    intros Hm0. rewrite Hm0 in Hdiv. apply H0. apply divmod_divides. assumption.
    exists d. assumption.
Qed.

(* n1 = m1 (mod k) /\ n2 = m2 (mod k) -> n1 * n2 = m1 * m2 (mod k) *)
Theorem divmod_mult: forall k n1 n2 m1 m2 m3 d1 d2 d3,
  divmod k n1 d1 m1 -> divmod k n2 d2 m2 -> divmod k (m1 * m2) d3 m3 ->
  exists d4, divmod k (n1 * n2) d4 m3.
Proof.
  intros. apply divmod_equiv in H. destruct H as [Hn1 _].
  apply divmod_equiv in H0. destruct H0 as [Hn2 _].
  apply divmod_equiv in H1. destruct H1 as [Hmult Hm3]. subst n1 n2.
  exists (k * d1 * d2 + d1 * m2 + d2 * m1 + d3). apply divmod_equiv.
  split; [|assumption]. ring_simplify. rewrite Hmult. ring.
Qed.

Theorem lt_minus: forall n m, n < m -> m - n > 0.
Proof.
  intros. apply plus_lt_reg_l with (p:=n). replace (n + (m - n)) with m.
  - omega.
  - apply le_plus_minus. omega.
Qed.

Lemma divmod_unique_helper: forall k d1 d2 m1 m2,
  k * d1 + m1 = k * d2 + m2 -> m1 < k -> d1 < d2 -> False.
Proof.
  intros k d1 d2 m1 m2 Heq Hm1 Hlt. apply le_plus_minus in Hlt.
  remember (d2 - S d1) as x. rewrite Hlt in Heq. ring_simplify in Heq.
  repeat rewrite <- plus_assoc in Heq. apply plus_reg_l with (p:=k*d1) in Heq.
  rewrite Heq in Hm1.  assert (contra: k + (k * x + m2) < k + 0). { omega. }
  apply plus_lt_reg_l in contra. apply lt_n_0 in contra. contradiction.
Qed.

Theorem divmod_unique: forall k n d1 d2 m1 m2, k > 0 ->
  divmod k n d1 m1 -> divmod k n d2 m2 -> d1 = d2 /\ m1 = m2.
Proof.
  intros. rename H into Hk0. apply divmod_equiv in H0. destruct H0 as [Hn1 Hm1].
  apply divmod_equiv in H1. destruct H1 as [Hn2 Hm2]. rewrite Hn1 in Hn2.
  destruct (le_or_lt d1 d2). apply le_lt_or_eq in H. destruct H.
  - (* d1 < d2 *) apply divmod_unique_helper in Hn2; trivial. contradiction.
  - (* d1 = d2 *) subst d2. apply plus_reg_l in Hn2. split; trivial.
  - (* d1 > d2 *) symmetry in Hn2. apply divmod_unique_helper in Hn2; trivial.
    contradiction.
Qed.

(* gcd n m k <-> gcd(n, m) == k *)
Inductive gcd : nat -> nat -> nat -> Prop :=
  | gcd_zero : forall n, gcd n 0 n
  | gcd_comm : forall n m k, gcd n m k -> gcd m n k
  | gcd_step : forall n m k, gcd n m k -> gcd n (m+n) k.

Theorem gcd_divides: forall n m k, gcd n m k -> divides k n /\ divides k m.
Proof.
  intros. induction H.
  - (* gcd n 0 n *) split.
    + exists 1. omega.
    + exists 0. omega.
  - (* gcd n m k -> gcd m n k *) destruct IHgcd as [Hkn Hkm]. split; assumption.
  - (* gcd n m k -> gcd n (m+n) k *) destruct IHgcd as [Hkn Hkm]. split.
    + assumption.
    + destruct Hkn as [x Hkn]. destruct Hkm as [y Hkm]. exists (x + y). rewrite <- Hkn. rewrite <- Hkm. ring.
Qed.

Theorem gcd_reverse: forall n m k, gcd n m k -> exists x y, k + y * m = x * n \/ k + x * n = y * m.
Proof.
  intros. induction H.
  - (* gcd n 0 n *) exists 1. exists 0. left. omega.
  - (* gcd n m k -> gcd m n k *) destruct IHgcd as [x [y [Hxy | Hyx]]]; exists y; exists x.
    + right. assumption.
    + left. assumption.
  - (* gcd n m k -> gcd n (m+n) k *) destruct IHgcd as [x [y [Hxy | Hyx]]]; exists (x + y); exists y.
    + left. ring_simplify. rewrite Hxy. ring.
    + right. ring_simplify. rewrite Hyx. ring.
Qed.

Theorem gcd_complete: forall n m, exists k, gcd n m k.
Proof.
  intros. (* TODO: Need general induction... *)
Admitted.

Theorem divides_prime: forall k p, prime p -> divides k p -> k = 1 \/ k = p.
Proof.
  intros. destruct H as [Hp1 Hprime]. (* TODO *)
Admitted.

(* Euclid's Theorem *)
Theorem prime_atomic: forall p n m,
  prime p -> divides p (n * m) -> divides p n \/ divides p m.
Proof.
  intros. destruct (gcd_complete p n) as [k Hgcd]. apply gcd_reverse in Hgcd as Hxy. destruct Hxy as [x [y Hxy]].
  apply gcd_divides in Hgcd as [Hkp Hkn]. destruct (divides_prime _ _ H Hkp); subst.
  - (* k = 1 *) right. destruct Hxy.
    + assert ((1 + y * n) * m = (x * p) * m); auto. ring_simplify in H2. apply (divides_minus p (y * n * m) m).
      * apply (divides_mult _ _ y) in H0. assert (n * m * y = y * n * m). ring. rewrite <- H3. assumption.
      * rewrite H2. rewrite mult_comm. apply divides_mult. exists 1. ring.
    + assert ((1 + x * p) * m = (y * n) * m); auto. ring_simplify in H2. apply (divides_minus p (x * p * m) m).
      * rewrite (mult_comm x p). rewrite <- mult_assoc. apply divides_mult. exists 1. ring.
      * rewrite H2. apply (divides_mult _ _ y) in H0. assert (n * m * y = m * y * n). ring. rewrite <- H3. assumption.
  - (* k = p *) left. assumption.
Qed.

Theorem prime_atomic_list: forall p ns, prime p -> divides p (prod ns) -> exists n, In n ns /\ divides p n.
Proof.
  intros. induction ns.
  - simpl in H0. apply prime_gt_1 in H. apply divides_1 in H. contradiction.
  - simpl in H0. apply prime_atomic in H0; [|assumption]. destruct H0.
    + exists a. split; auto. constructor. reflexivity.
    + apply IHns in H0. destruct H0 as [n [Hin Hdiv]]. exists n. split; auto. right. assumption.
Qed.

Lemma prime_atomic_list_primes: forall p qs, 
  prime p -> (forall q, In q qs -> prime q) -> divides p (prod qs) -> In p qs.
Proof.
  intros. apply prime_atomic_list in H1; auto. destruct H1 as [n [Hin Hdiv]]. apply divides_prime in Hdiv; auto.
  destruct Hdiv; subst; auto.
  - (* prime 1 *) apply prime_gt_1 in H. apply lt_irrefl in H. contradiction.
Qed.

(* SameElements xs ys <-> xs and ys have same elements (but potentially in different order) *)
Inductive SameElements : list nat -> list nat -> Prop :=
  | same_elements_equal : forall xs, SameElements xs xs
  | same_elements_insert : forall a xs1 xs2 ys1 ys2,
      SameElements (xs1 ++ xs2) (ys1 ++ ys2) -> SameElements (xs1 ++ a :: xs2) (ys1 ++ a :: ys2).

Theorem same_elements_comm: forall xs ys, SameElements xs ys -> SameElements ys xs.
Proof.
  intros. induction H; try constructor; auto.
Qed.

Theorem prod_split: forall xs ys, prod (xs ++ ys) = prod xs * prod ys.
Proof.
  induction xs; intros; simpl; auto. rewrite IHxs. ring.
Qed.

Lemma mult_reg: forall a b c, a <> 0 -> a * b = a * c -> b = c.
Proof.
  intros. destruct a; try contradiction. simpl in H0. generalize dependent c.
  induction b; intros.
  - ring_simplify in H0. symmetry in H0. apply plus_is_O in H0. destruct H0. auto.
  - ring_simplify in H0. (* TODO *)
Admitted.

Theorem prime_factor_unique: forall ps qs,
  prod ps = prod qs -> (forall p, In p ps -> prime p) -> (forall q, In q qs -> prime q) -> 
  SameElements ps qs.
Proof.
  intros. generalize dependent ps. induction qs as [|q qs]; intros.
  - simpl in H. destruct ps as [|p ps]. constructor. assert (Hp: prime p). { apply H0. left. reflexivity. }
    apply prime_gt_1 in Hp. simpl in H. apply mult_is_one in H. destruct H. subst.
    apply lt_irrefl in Hp. contradiction.
  - assert (Hdiv: divides q (prod ps)). {simpl in H. exists (prod qs). auto. }
    apply prime_atomic_list_primes in Hdiv.
    + (* main *) apply in_split in Hdiv as [ps1 [ps2 Hin]]. subst. rewrite prod_split in H. simpl in H.
      assert (prod (ps1 ++ ps2) = prod qs). { rewrite prod_split. apply (mult_reg q). admit. (* TODO q <> 0 *)
        rewrite <- H. ring. } apply IHqs in H2; auto.
      * (* main *) replace (q :: qs) with (nil ++ q :: qs); auto. constructor. auto.
      * intros. apply H1. right. assumption.
      * intros. apply H0. apply in_app_or in H3. apply in_or_app. destruct H3. left. assumption.
        right. right. assumption.
    + (* prime q *) apply H1. left. auto.
    + (* In p ps -> prime p *) apply H0.
Admitted.
