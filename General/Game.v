Require Import List Le Arith.

Import ListNotations.

Inductive game := Game {
  left_games : list game;
  right_games : list game
}.

(* TODO: Get mutual induction between game and (list game).
Scheme game_gen_ind := Induction for game Sort Prop
with list_gen_ind := Induction for (list game) Sort Prop.
Section game_general_induction.

Variable P : game -> Prop.
Variable P_list : list game -> Prop.

Hypothesis game_case : forall left_g right_g,
  P_list left_g -> P_list right_g -> P (Game left_g right_g).
Hypothesis nil_case : P_list [].
Hypothesis list_case : forall g gs, P g -> P_list gs -> P_list (g :: gs).

Fixpoint game_gen_ind (g : game) : P g :=
  match g with Game left_g right_g =>
    game_case left_g right_g (list_game_ind left_g) (list_game_ind right_g)
  end

with list_game_ind (gs : list game) : P_list gs :=
  match gs with
    | [] => nil_case
    | g :: gs' => list_case g gs' (game_gen_ind g) (list_game_ind gs')
  end.

*)

Notation "{ x | y }" := (Game x y).

Fail Inductive le : game -> game -> Prop :=
  | le_def : forall x y,
      (forall yr, In yr (right_games y) -> ~ yr <= x) ->
      x <= y

where "x <= y" := (le x y).
(* Error: Non strictly positive occurrence of "le" in
 "forall x y : game,
  (forall yr : game, In yr (right_games y) -> ~ le yr x) -> le x y". *)

Parameter leG : game -> game -> Prop.

Notation "x <= y" := (leG x y).

Axiom le_def: forall x y,
  x <= y <->
  (forall yr, In yr (right_games y) -> ~ yr <= x) /\
  (forall xl, In xl (left_games x) -> ~ y <= xl).

Definition number (g : game) : Prop :=
  forall l r, In l (left_games g) -> In r (right_games g) ->
  ~ r <= l.

Theorem le_refl: forall g, number g -> g <= g.
Proof.
  intros. apply le_def. intros.
Abort.

Notation "[]" := nil.
Notation "[ x ]" := (cons x nil).

Fixpoint nat_to_game (n : nat) : game :=
  match n with
    | O => Game [] []
    | S n' => Game [nat_to_game n'] []
  end.

Theorem nat_valid : forall n, number (nat_to_game n).
Proof.
  unfold number. intros. destruct n; simpl in H0; contradiction.
Qed.

Lemma left_S_nat: forall n g,
  In g (left_games (nat_to_game (S n))) -> g = nat_to_game n.
Proof.
  intros. simpl in H. destruct H.
  - symmetry. assumption.
  - contradiction.
Qed.

Lemma left_0: forall g, In g (left_games (nat_to_game 0)) -> False.
Proof. intros. simpl in H. contradiction. Qed.

Lemma right_nat: forall n g, In g (right_games (nat_to_game n)) -> False.
Proof. intros. destruct n; simpl in H; contradiction. Qed.

Theorem nat_le: forall n m,
  (nat_to_game (S n)) <= (nat_to_game m) <-> ~ (nat_to_game m) <= (nat_to_game n).
Proof.
  split; intros.
  - apply le_def in H. destruct H. apply H0. simpl. left. reflexivity.
  - apply le_def. split; intros.
    + apply right_nat in H0. contradiction.
    + apply left_S_nat in H0. rewrite H0. assumption.
Qed.

Lemma leG_0_n: forall n, (nat_to_game 0) <= (nat_to_game n).
Proof.
  intros. apply le_def. split; intros.
  - apply right_nat in H. contradiction.
  - apply left_0 in H. contradiction.
Qed.

Theorem nat_order: forall n m : nat,
  (n <= m)%nat -> (nat_to_game n) <= (nat_to_game m).
Proof.
  induction n; intros m Hnm.
  - apply leG_0_n.
  - apply nat_le. intros contra. destruct m.
    + apply le_n_0_eq in Hnm. inversion Hnm.
    + apply nat_le in contra. apply contra. apply IHn. apply le_S_n. assumption.
Qed.

Parameter ltG: game -> game -> Prop.
Notation "x < y" := (ltG x y).

Axiom lt_def: forall x y, x < y <-> x <= y /\ ~ y <= x.

Parameter eqG: game -> game -> Prop.
Notation "x == y" := (eqG x y) (at level 50).

Axiom eq_def: forall x y, x == y <-> x <= y /\ y <= x.

Theorem nat_order_rev: forall n m,
  (nat_to_game n) <= (nat_to_game m) -> (n <= m)%nat.
Proof.
  induction n; intros m Hnm.
  - apply le_0_n.
  - apply nat_le in Hnm. destruct m.
    + exfalso. apply Hnm. apply leG_0_n.
    + apply not_lt. intros contra. apply Hnm. apply nat_le. intros Hnm'.
      apply IHn in Hnm'. generalize dependent contra. apply le_not_lt.
      apply le_n_S. assumption.
Qed.

Lemma nat_unique: forall n m, (nat_to_game n) == (nat_to_game m) -> n = m.
Proof.
  intros. apply eq_def in H. destruct H. apply nat_order_rev in H.
  apply nat_order_rev in H0. apply le_antisym; assumption.
Qed.

Axiom game_induction: forall P : game -> Prop,
  (forall x,
    (forall xl, In xl (left_games x) -> P xl) ->
    (forall xr, In xr (right_games x) -> P xr) ->
    P x) ->
  forall x, P x.

(* Theorem double_induction: forall P : game -> game -> Prop,
  (forall x y,
    (forall xl, in xl (left_games x) -> P xl y *)

Theorem leG_refl: forall x, x <= x.
Proof.
  intros x. apply game_induction with (x:=x). clear x. intros. apply le_def.
  split; intros.
  - rename yr into xr. intros contra. apply le_def in contra. destruct contra.
    unfold not in H2. apply (H2 xr); [assumption|]. apply H0. assumption.
  - intros contra. apply le_def in contra. destruct contra.
    unfold not in H3. apply (H3 xl); [assumption|]. apply H. assumption.
Qed.

Theorem leG_trans: forall x y z, x <= y -> y <= z -> x <= z.
Proof.
  intros x. apply game_induction with (x:=x). clear x. intros. apply le_def. split; intros.
  - admit.
  - 
Abort.

Theorem leG_total: forall x y, x <= y \/ y <= x.
Abort.

Theorem leG_desideable: forall x y, x <= y \/ ~ x <= y.
Abort.









