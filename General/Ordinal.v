Require Import Bool.
Require Import Decidable.
Require Import Setoid.

Module CNF.

Delimit Scope cnf_scope with cnf_scope.
Open Scope cnf_scope.

(* A notation for Cantor Normal Form.
 *   w^a + w^b + ... + w^z which w = omega and a-z are recursively CNFs.
 *   1 = w^0, 2 = w^0 + w^0, w = w^w^0
 * For ordinals, CNFs should also have the restriction that a >= b >= ... >= z
 *   but we cannot guarantee that for this inductive definition.
 * CNF can represent all ordinals < epsilon_0 *)
Inductive cnf :=
  | zero : cnf
  | comb : cnf -> cnf -> cnf.  (* (comb a b)  represents w^a + b *)

Inductive gt_cnf : cnf -> cnf -> Prop :=
  | gt_zero : forall a b, comb a b > zero
    (* w^a + b > 0 *)
  | gt_head : forall a1 a2 b1 b2, a1 > b1 -> comb a1 a2 > comb b1 b2
    (* a1 > b1 -> w^a1 + a2 > w^b1 + b2 *)
  | gt_tail : forall x a b, a > b -> comb x a > comb x b
    (* a > b -> w^x + a > w^x + b *)

where "x > y" := (gt_cnf x y) : cnf_scope.

Definition ge_cnf (a b : cnf) := a = b \/ a > b.

Notation "x >= y" := (ge_cnf x y) : cnf_scope.

Inductive is_ordinal : cnf -> Prop :=
  | ord_zero : is_ordinal zero
  | ord_single : forall a, is_ordinal a -> is_ordinal (comb a zero)
  | ord_mult : forall a b c, is_ordinal a -> is_ordinal (comb b c) ->
                             a >= b -> is_ordinal (comb a (comb b c)).

Definition ordinal := { a : cnf | is_ordinal a }. (* Not sure about this syntax. *)

Theorem gt_irrefl : forall a, ~ a > a.
Proof.
  induction a; intros Hgt.
  - (* zero > zero *) inversion Hgt.
  - (* comb a b > comb a b *) inversion Hgt; subst.
    + contradiction.
    + contradiction.
Qed.

Theorem gt_asym : forall a b, a > b -> ~ b > a.
Proof.
  intros a b Hab Hba. induction Hab.
  - (* zero > comb a b *) inversion Hba.
  - (* a1 > b1 /\ comb b1 b2 > comb a1 a2 *) inversion Hba; subst.
    + (* b1 > a1 *) contradiction.
    + (* b1 = a1 *) contradiction.
  - (* a > b /\ comb x a > comb x b *) inversion Hba; subst.
    + (* x > x *) apply gt_irrefl in H0. contradiction.
    + (* b > a *) contradiction.
Qed.

Fixpoint beq_cnf a b :=
  match a, b with
    | zero, zero => true
    | zero, comb _ _ => false
    | comb _ _, zero => false
    | comb a1 a2, comb b1 b2 => beq_cnf a1 b1 && beq_cnf a2 b2
  end.

Theorem eq_reflect : forall a b, reflect (a = b) (beq_cnf a b).
Proof.
  intros. destruct (beq_cnf a b) eqn:Heq.
  - (* beq_cnf a b = true -> a = b *) constructor. generalize dependent b.
    induction a; intros.
    + destruct b. reflexivity. inversion Heq.
    + destruct b. inversion Heq. simpl in Heq. apply andb_true_iff in Heq.
      destruct Heq. apply IHa1 in H. apply IHa2 in H0. subst. reflexivity.
  - (* beq_cnf a b = false -> a <> b *) constructor. intros contra. subst.
    induction b.
    + simpl in Heq. inversion Heq.
    + apply not_false_is_true in IHb1. apply not_false_is_true in IHb2.
      simpl in Heq. rewrite IHb1 in Heq. rewrite IHb2 in Heq. inversion Heq.
Qed.

Theorem dec_reflect : forall P b, reflect P b -> decidable P.
Proof.
  intros. inversion H.
  - left. assumption.
  - right. assumption.
Qed.

Lemma dec_eq : forall (a b : cnf), decidable (a = b).
Proof. intros. eapply dec_reflect. apply eq_reflect. Qed.

Lemma ne_parts : forall a b c d,
  comb a b <> comb c d -> a <> c \/ b <> d.
Proof.
  intros. apply not_and. apply dec_eq. intros [Hac Hbd]. apply H. subst.
  reflexivity.
Qed.

Theorem not_eq : forall a b, a <> b -> a > b \/ b > a.
Proof.
  induction a; intros.
  - (* a = 0 *) destruct b.
    + (* ~ 0 <> 0 *) exfalso. apply H. reflexivity.
    + (* w^b1 + b2 > 0 *) right. constructor.
  - (* a = w^a1 + a2 *) destruct b.
    + (* w^a1 + a2 > 0 *) left. constructor.
    + destruct (eq_reflect a1 b1).
      * { destruct (eq_reflect a2 b2); subst.
        - (* a1 = b1, a2 = b2 *) exfalso. apply H. reflexivity.
        - (* a1 = b1, a2 <> b2 *) rename n into Hne. apply IHa2 in Hne.
          destruct Hne; [left|right]; apply gt_tail; assumption. }
      * (* a1 <> b1 *) rename n into Hne. apply IHa1 in Hne.
        destruct Hne; [left|right]; apply gt_head; assumption.
Qed.

Theorem gt_trans : forall a b c, a > b -> b > c -> a > c.
Proof.
  intros a b c Hab. generalize dependent c. induction Hab; intros c Hbc.
  - (* a > 0 > c *) inversion Hbc.
  - (* w^a1 + a2 > w^b1 + b2 > c *) destruct c. apply gt_zero. inversion Hbc; subst.
    + apply gt_head. apply IHHab. assumption.
    + apply gt_head. assumption.
  - (* w^x + a > w^x + b > c *) inversion Hbc; subst.
    + apply gt_zero.
    + apply gt_head. assumption.
    + apply gt_tail. apply IHHab. assumption.
Qed.

Require Import Relation_Definitions.

(* <= is a total order. *)
Theorem ge_total : reflexive _ ge_cnf /\ transitive _ ge_cnf /\ antisymmetric _ ge_cnf.
Proof.
  split; try split.
  - (* Reflexive *) intros a. left. reflexivity.
  - (* Transitive *) intros a b c Hab Hbc.
      destruct Hab. subst. assumption.
      destruct Hbc. subst. right. assumption.
      right. apply gt_trans with b; assumption.
  - (* Antisymmetric *) intros a b Hab Hba.
      destruct Hab. assumption.
      destruct Hba. symmetry. assumption.
      apply gt_asym in H. contradiction.
Qed.

Lemma ge_not_gt : forall a b, a >= b -> ~ b > a.
Proof.
  intros. destruct H.
  - subst. apply gt_irrefl.
  - apply gt_asym. assumption.
Qed.

Lemma not_ge : forall a b, ~ a >= b -> b > a.
Proof.
  intros. destruct (eq_reflect a b).
  - exfalso. apply H. left. apply e.
  - apply not_eq in n. destruct n.
    + exfalso. apply H. right. apply H0.
    + apply H0.
Qed.

Lemma not_gt : forall a b, ~ a > b -> b >= a.
Proof.
  intros. destruct (eq_reflect b a).
  - left. assumption.
  - apply not_eq in n. destruct n.
    + right. assumption.
    + contradiction.
Qed.

(* Ordinals are well-ordered, so all sets of ordinals attain a minimum.
   But cnf includes non-ordinals, so it is not well-ordered. *)

(* A non-ordinal CNF sequence which never attains it's minimum. *)
Inductive minless_cnf : cnf -> Prop :=
  | minless_init : minless_cnf (comb (comb zero zero) zero)  (* w^1 *)
  | minless_pred : forall a, minless_cnf a -> minless_cnf (comb zero a). 
    (* w^0 + w^0 + ... + w^0 + w^1 *)

Lemma minless_no_min : forall a,
  minless_cnf a -> exists b, minless_cnf b /\ a > b.
Proof.
  intros. eexists. split. apply minless_pred. apply H. induction H.
  - apply gt_head. apply gt_zero.
  - apply gt_tail. apply IHminless_cnf.
Qed.

Lemma minless_non_ordinal : exists a, minless_cnf a /\ ~ is_ordinal a.
Proof.
  exists (comb zero (comb (comb zero zero) zero)).  (* w^0 + w^1 *)
  split. apply minless_pred. apply minless_init.
  intros H. inversion H; subst. apply ge_not_gt in H5. apply H5. apply gt_zero.
Qed.

(* Ordinal sequence which never attains it's maximum.
   This is Cantor's construction of the natural numbers. *)
Inductive nat_cnf : cnf -> Prop :=
  | nat_cnf_zero : nat_cnf zero
  | nat_cnf_succ : forall n, nat_cnf n -> nat_cnf (comb zero n). (* w^0 + n = n + 1 *)

Lemma nat_no_max : forall a,
  nat_cnf a -> exists b, nat_cnf b /\ b > a.
Proof.
  intros. eexists. split. apply nat_cnf_succ. apply H. induction H.
  - apply gt_zero.
  - apply gt_tail. assumption.
Qed.

Lemma nat_ordinal : forall a, nat_cnf a -> is_ordinal a.
Proof.
  intros. induction H as [|[|]].
  - apply ord_zero.
  - apply ord_single. apply ord_zero.
  - inversion H; subst. apply ord_mult. apply ord_zero. apply IHnat_cnf.
    left. reflexivity.
Qed.

(* Returns the ordinal (w^a * n) *)
Fixpoint repeat_cnf (a : cnf) (n : nat) : cnf :=
  match n with
    | 0 => zero  (* w^a * 0 = 0 *)
    | S n' => comb a (repeat_cnf a n')  (* w^a + (n+1) = w^a + (w^a * n) *)
  end.


(* All non-zero ordinals are either successors or limits of smaller ordinals. *)
Inductive cnf_ancestry_type :=
  | cnf_succ : cnf -> cnf_ancestry_type
  | cnf_limit : (nat -> cnf) -> cnf_ancestry_type.

Inductive cnf_ancestry : cnf -> cnf_ancestry_type -> Prop :=
    (* 1 = succ 0 *)
  | one_ancestry : cnf_ancestry (comb zero zero) (cnf_succ zero)
    (* b = succ c -> w^a + b = succ w^a + c *)
  | tail_succ_ancestry : forall a b c, cnf_ancestry b (cnf_succ c) ->
      cnf_ancestry (comb a b) (cnf_succ (comb a c))

    (* a = succ b -> w^a = limit w^b * n *)
  | head_succ_ancestry : forall a b, cnf_ancestry a (cnf_succ b) ->
      cnf_ancestry (comb a zero) (cnf_limit (repeat_cnf b))
    (* a = limit bs -> w^a = limit w^bs *)
  | head_limit_ancestry : forall a a_lim, cnf_ancestry a (cnf_limit a_lim) ->
      cnf_ancestry (comb a zero) (cnf_limit (fun n => (comb (a_lim n) zero)))
    (* b = limit cs -> w^a + b = limit w^a + cs *)
  | tail_limit_ancestry : forall a b b_lim, cnf_ancestry b (cnf_limit b_lim) ->
      cnf_ancestry (comb a b) (cnf_limit (fun n => (comb a (b_lim n)))).

Lemma no_zero_ancestry : forall anc, ~ cnf_ancestry zero anc.
Proof. intros. intros contra. inversion contra. Qed.

(* Get exponent for last term in w^a + b *)
Fixpoint last_term (a b : cnf) : cnf :=
  match b with
    | zero => a
    | comb c d => last_term c d
  end.

(* All successors end in w^0 *)
Lemma succ_last_term : forall a b c,
  cnf_ancestry (comb a b) (cnf_succ c) -> last_term a b = zero.
Proof.
  intros a b. generalize dependent a. induction b; intros.
  - (* w^a *) inversion H; subst.
    + (* one *) reflexivity.
    + (* tail_succ *) inversion H1.
  - (* w^a + b *) simpl. inversion H; subst. apply IHb2 with c0. assumption.
Qed.

(* All limits don't end in w^0 *)
Lemma limit_last_term : forall a b cs,
  cnf_ancestry (comb a b) (cnf_limit cs) -> last_term a b <> zero.
Proof.
  intros a b. generalize dependent a. induction b; intros.
  - (* w^a *) intros HC. simpl in HC. subst.
    inversion H; subst; try inversion H2. inversion H1.
  - inversion H; subst. apply IHb2 with b_lim. apply H1.
Qed.

Fixpoint cnf_ancestry_func (x : cnf) : option cnf_ancestry_type :=
  match x with
    | zero => None
    | comb a b => Some
      match cnf_ancestry_func b with
        | None => (* b = 0 *)
          match cnf_ancestry_func a with
            | None => cnf_succ zero  (* 1 = succ 0 *)
              (* w^(succ a') = limit w^a' * n *)
            | Some (cnf_succ a') => cnf_limit (repeat_cnf a')
              (* w^(limit a_n) = limit w^a_n *)
            | Some (cnf_limit a_lim) => cnf_limit (fun n => comb (a_lim n) zero)
          end
          (* w^a + (succ b') = succ w^a + b' *)
        | Some (cnf_succ b') => cnf_succ (comb a b')
          (* w^a + (limit b_n) = limit w^a + b_n *)
        | Some (cnf_limit b_lim) => cnf_limit (fun n => comb a (b_lim n))
      end
  end.

Theorem cnf_ancestry_equiv : forall a res,
  cnf_ancestry a res <-> cnf_ancestry_func a = Some res.
Proof.
  split; intros.
  - induction H; simpl.
    + (* one *) reflexivity.
    + (* tail_succ *) rewrite IHcnf_ancestry. reflexivity.
    + (* head_succ *) rewrite IHcnf_ancestry. reflexivity.
    + (* head_limit *) rewrite IHcnf_ancestry. reflexivity.
    + (* tail_limit *) rewrite IHcnf_ancestry. reflexivity.
  - generalize dependent res. induction a; intros; simpl in H.
    + (* a = 0 *) inversion H.
    + destruct (cnf_ancestry_func a2) as [[a2'|a2_lim]|] eqn:Ha2.
      * (* Some succ a2' *) inversion H; subst. apply tail_succ_ancestry.
        apply IHa2. reflexivity.
      * (* Some limit a2_lim *) inversion H; subst. apply tail_limit_ancestry.
        apply IHa2. reflexivity.
      * (* None *) destruct a2; inversion Ha2. (* a2 = 0 *)
        { destruct (cnf_ancestry_func a1) as [[a1'|a1_lim]|] eqn:Ha1.
        - (* Some succ a1' *) inversion H; subst. apply head_succ_ancestry.
          apply IHa1. reflexivity.
        - (* Some limit a1_lim *) inversion H; subst. apply head_limit_ancestry.
          apply IHa1. reflexivity.
        - (* None *) destruct a1; inversion Ha1. (* a1 = 0 *)
          inversion H; subst. apply one_ancestry. }
Qed.

Lemma cnf_succ_gt : forall a b, cnf_ancestry a (cnf_succ b) -> a > b.
Proof.
  induction a; intros.
  - inversion H.
  - inversion H; subst.
    + apply gt_zero.
    + apply gt_tail. apply IHa2. assumption.
Qed.

Lemma cnf_limit_gt : forall a a_lim, cnf_ancestry a (cnf_limit a_lim) ->
  forall n, a > a_lim n.
Proof.
  induction a.
  - (* a = 0 *) intros. inversion H.
  - (* a = w^a1 + a2 *) intros. inversion H; subst.
    + (* w^a > w^a' * n *) destruct n.
      * simpl. apply gt_zero.
      * simpl. apply gt_head. apply cnf_succ_gt. assumption.
    + (* w^a > w^a_n *) apply gt_head. apply IHa1. assumption.
    + (* w^a + b > w^a + b_n *) apply gt_tail. apply IHa2. assumption.
Qed.

Lemma ge_zero: forall a, a >= zero.
Proof. intros. destruct a. left. reflexivity. right. apply gt_zero. Qed.

Lemma ge_tail: forall x a b, a >= b -> comb x a >= comb x b.
Proof.
  intros. destruct H. subst. left. reflexivity. right. apply gt_tail. assumption.
Qed.

Theorem cnf_succ_max : forall a b, cnf_ancestry a (cnf_succ b) ->
  forall c, a > c -> b >= c.
Proof.
  induction a; intros. inversion H. destruct a2.
  - (* w^a1 *) inversion H; subst.
    + (* w^0 *)inversion H0; subst.
      * left. reflexivity.
      * inversion H4.
      * inversion H4.
    + inversion H2.
  - (* w^a1 + w^a2_1 + a2_2 *) inversion H0; subst.
    + (* b >= 0 *) apply ge_zero.
    + (* b >= w^b1 + b2 /\ a1 > b1 *) inversion H; subst. right. apply gt_head. assumption.
    + inversion H; subst. apply ge_tail. apply IHa2. assumption. assumption.
Qed.

Lemma repeat_overtakes : forall a b,
  is_ordinal (comb a b) -> exists n, repeat_cnf a n > comb a b.
Proof.
  intros. induction b.
  - (* rep w^a > w^a *) exists 2. apply gt_tail. apply gt_zero.
  - (* rep w^a > w^a + w^b1 + b2 *) inversion H; subst. destruct H5.
    + (* a = b1 *) subst b1. apply IHb2 in H4. destruct H4 as [n Hgt].
      exists (S n). simpl. apply gt_tail. apply Hgt.
    + (* a > b1 *) exists 2. apply gt_tail. apply gt_head. apply H0.
Qed.

Lemma one_gt : forall a, comb zero zero > a -> a = zero.
Proof.
  intros. inversion H; subst. reflexivity. inversion H3. inversion H3.
Qed.

Lemma gt_nonzero : forall a b, a > b -> a <> zero.
Proof. intros. intros HC. subst. inversion H. Qed.

Lemma ne_zero_gt : forall a, a <> zero -> a > zero.
Proof. intros. destruct a. exfalso. apply H. reflexivity. apply gt_zero. Qed.

Lemma repeat_monotonic : forall a n, repeat_cnf a (S n) > repeat_cnf a n.
Proof.
  induction n.
  - simpl. apply gt_zero.
  - simpl. apply gt_tail. apply IHn.
Qed.

Lemma limit_monotonic : forall a a_lim, cnf_ancestry a (cnf_limit a_lim) ->
  forall n, a_lim (S n) > a_lim n.
Proof.
  induction a; intros. inversion H. inversion H; subst.
  - (* rep b (S n) > rep b n *) apply repeat_monotonic.
  - (* a1_lim (S n) > a1_lim n *) apply gt_head. apply IHa1. apply H1.
  - (* a2_lim (S n) > a2_lim n *) apply gt_tail. apply IHa2. apply H1.
Qed.

Lemma ord_head : forall a b, is_ordinal (comb a b) -> is_ordinal a.
Proof. intros. inversion H. assumption. assumption. Qed.

Lemma ord_tail : forall a b, is_ordinal (comb a b) -> is_ordinal b.
Proof. intros. inversion H. apply ord_zero. assumption. Qed.

Theorem cnf_limit_max : forall a a_lim, cnf_ancestry a (cnf_limit a_lim) ->
  forall c, is_ordinal c -> a > c -> exists n, a_lim n > c.
Proof.
  induction a; intros a_lim Hanc c Hord Hac; inversion Hanc; subst.
  - (* head_succ a = w^a1 /\ a1 = succ b *) rename H0 into Hanc_a1.
    inversion Hac; subst.
    + (* a > 0 *) exists 1. apply gt_zero.
    + (* w^a1 > w^c1 + c2 /\ a1 > c1 *) rename b1 into c1. rename b2 into c2.
      rename H2 into Ha1c1. eapply cnf_succ_max in Hanc_a1; [|apply Ha1c1].
      destruct Hanc_a1.
      * (* rep w^c1 > w^c1 + c2 *) subst. apply repeat_overtakes. assumption.
      * (* rep w^b > w^c1 + c2 /\ b > c1 *) exists 1. apply gt_head. assumption.
    + (* w^a1 > w^a1 + c2 *) inversion H2.
  - (* head_limit a = w^a1 /\ a1 = limit a1_lim *) rename a_lim0 into a1_lim.
    rename H0 into Hanc_a1. inversion Hac; subst.
    + exists 0. apply gt_zero.
    + rename b1 into c1. rename b2 into c2. rename H2 into Ha1c1.
      apply IHa1 with (c:=c1) in Hanc_a1.
      * destruct Hanc_a1 as [n Hgt]. exists n. apply gt_head. apply Hgt.
      * eapply ord_head. apply Hord.
      * assumption.
    + inversion H2.
  - (* tail_limit a = w^a1 + a2 /\ a2 = limit a2_lim *) rename b_lim into a2_lim.
    rename H0 into Hanc_a2. inversion Hac; subst.
    + exists 0. apply gt_zero.
    + exists 0. apply gt_head. assumption.
    + eapply IHa2 in Hanc_a2. Focus 3.
      * apply H2.
      * destruct Hanc_a2 as [n Hgt]. exists n. apply gt_tail. assumption.
      * eapply ord_tail. apply Hord.
Qed.

(* Maybe simpler proof this way?
Theorem cnf_limit_max2 : forall a a_lim, cnf_ancestry a (cnf_limit a_lim) ->
  forall c, is_ordinal c -> a > c -> exists n, a_lim n > c.
Proof.
  induction a; intros a_lim Hanc c Hord Hac; inversion Hac; subst.
  - (* a_lim n > 0 *) exists 1. apply ne_zero_gt. eapply gt_nonzero.
    eapply limit_monotonic. apply Hanc.
  - (* a1 > b1 *) inversion Hanc; subst.
  - (* a2 > b2 *) inversion Hanc; subst.
    + inversion H2.
    + inversion H2.
    + eapply IHa2 in H0. Focus 3.
      * apply H2.
      * destruct H0. exists x. apply gt_tail. assumption.
      * eapply ord_tail. apply Hord.
*)

Definition one := comb zero zero.
Definition omega := comb one zero.

Lemma zero_ge : forall a, zero >= a -> a = zero.
Proof. intros. destruct H. symmetry. assumption. inversion H. Qed.



Lemma nat_succ : forall a, is_ordinal (comb zero a) ->
  cnf_ancestry (comb zero a) (cnf_succ a).
Proof.
  induction a; intros.
  - apply one_ancestry.
  - inversion H; subst. apply zero_ge in H5; subst. apply tail_succ_ancestry.
    apply IHa2. assumption.
Qed.

Lemma gen_cnf_ind_omega : forall P : cnf -> Prop,
  (forall a, (forall b, a > b -> P b) -> P a) ->
  forall a, is_ordinal a -> omega > a -> P a.
Proof.
  intros P Hind a Hord Hgt. inversion Hgt; subst.
  - apply Hind. intros. inversion H.
  - apply one_gt in H2. subst. apply Hind. induction b2; intros.
    + apply one_gt in H. subst. apply Hind. intros. inversion H.
    + inversion Hord; subst. destruct H5; [|inversion H0]. subst.
      apply nat_succ in Hord. eapply cnf_succ_max in Hord. Focus 2. apply H.
      destruct Hord.
      * subst.
      admit.
  - inversion H2.

Theorem gen_cnf_ind : forall P : cnf -> Prop,
  (forall a, (forall b, a > b -> P b) -> P a) ->
  forall a, is_ordinal a -> P a.
Proof.
  intros P Hind a. destruct a.
  - (* P 0 *) admit.
  - (* P (w^a1 + a2) *) induction a2. induction a1.
Abort.

(* TODO: Prove well-ordered for Ordinals ... or that any descending sequence is finite ... *)

(* TODO: Goodstein sequences, function, theorem. *)











