Require Import Arith.
Require Import Le.
Require Import List.
Require Import Omega.

Inductive state : Set :=
  | Halt : state
  | State : nat -> state.

Definition start_state := State 0.

Inductive symbol : Set :=
  | Symbol : nat -> symbol.

Definition empty_symbol := Symbol 0.

Inductive dir : Set :=
  | Left : dir
  | Right : dir.

(* Transition table. *)
Definition turing_machine := state -> symbol -> symbol * dir * state.

Inductive config : Set := Config {
  curr_state : state;
  curr_symb : symbol;
  left_tape : list symbol;
  right_tape : list symbol
}.

Definition start_config := Config start_state empty_symbol nil nil.

Function top_symbol (t : list symbol) : symbol :=
  match t with
    | top :: rest => top
    | nil => empty_symbol
  end.

Function tail {X} (t : list X) : list X :=
  match t with
    | top :: rest => rest
    | nil => nil
  end.

Function step (tm : turing_machine) (c : config) : config :=
  match curr_state c with
    | Halt => c (* No change if already halted. *)
    | State _ =>
      match tm (curr_state c) (curr_symb c) with
        | (new_symbol, new_dir, new_state) =>
          match new_dir with
            | Left => Config new_state
                             (top_symbol (left_tape c))
                             (tail (left_tape c))
                             (new_symbol :: right_tape c)
            | Right => Config new_state
                              (top_symbol (right_tape c))
                              (new_symbol :: left_tape c)
                              (tail (right_tape c))
          end
      end
  end.

(* eval tm c c' <-> tm can reach c' from c through a series of steps. *)
Inductive eval : turing_machine -> config -> config -> Prop :=
  | EvalRefl : forall tm c, eval tm c c
  | EvalStep : forall tm c c', eval tm c c' -> eval tm c (step tm c').

Definition halts_from tm c :=
  exists c_halt, eval tm c c_halt /\ curr_state c_halt = Halt.

Definition halts tm := halts_from tm start_config.

Definition no_result := (empty_symbol, Right, start_state).

Definition bb22 st symb :=
  match st, symb with
    | State 0, Symbol 0 => (Symbol 1, Right, State 1)  (* A0 -> 1RB *)
    | State 0, Symbol 1 => (Symbol 1, Left, State 1)   (* A1 -> 1LB *)
    | State 1, Symbol 0 => (Symbol 1, Left, State 0)   (* B0 -> 1LA *)
    | State 1, Symbol 1 => (Symbol 1, Right, Halt)     (* B1 -> 1RH *)
    | _, _ => no_result
  end.

Fixpoint run tm c steps :=
  match steps with
    | 0 => c
    | S s => run tm (step tm c) s
  end.

Lemma run_step_permute : forall tm c n,
  step tm (run tm c n) = run tm (step tm c) n.
Proof.
  intros. generalize dependent c. induction n; intros.
  - reflexivity.
  - simpl. apply IHn.
Qed.

Lemma eval_run : forall tm c c', eval tm c c' <-> exists n, c' = run tm c n.
Proof.
  split; intros.
  - induction H.
    + exists 0. reflexivity.
    + destruct IHeval. exists (S x). simpl. rewrite H0. apply run_step_permute.
  - destruct H as [n H]. generalize dependent c'. induction n; intros.
    + rewrite H. simpl. apply EvalRefl.
    + rewrite H. simpl. rewrite <- run_step_permute. apply EvalStep.
      apply IHn. reflexivity.
Qed. 

Theorem halts_run : forall tm,
  halts tm <-> exists n, curr_state (run tm start_config n) = Halt.
Proof.
  split; intros.
  - destruct H as [c [Heval Hhalt]]. apply eval_run in Heval.
    destruct Heval as [n Hrun]. exists n. rewrite <- Hrun. assumption.
  - destruct H as [n H]. exists (run tm start_config n). split.
    + apply eval_run. exists n. reflexivity.
    + assumption.
Qed.

Example bb22_halts: halts bb22.
Proof. apply halts_run. exists 6. reflexivity. Qed.

Function tape_dir d c :=
  match d with
    | Left => left_tape c
    | Right => right_tape c
  end.

Lemma a_rep: forall tm st s d c,
  tm st empty_symbol = (s, d, st) ->
  curr_state c = st /\ curr_symb c = empty_symbol /\ tape_dir d c = nil ->
  curr_state (step tm c) = st /\
  curr_symb (step tm c) = empty_symbol /\ tape_dir d (step tm c) = nil.
Proof.
  intros. destruct H0 as [H0 [H1 H2]]. unfold step. rewrite H0. destruct st.
  - (* Halt *) split; try split; assumption.
  - rewrite H1. rewrite H. destruct d.
    + simpl in H2. split. reflexivity. split; simpl.
      * rewrite H2. simpl. reflexivity.
      * rewrite H2. simpl. reflexivity.
    + simpl in H2. split. reflexivity. split; simpl.
      * rewrite H2. simpl. reflexivity.
      * rewrite H2. simpl. reflexivity.
Qed.

(* All TMs with A0 -> ??A will never halt. *)
Theorem a_no_halt : forall tm s d,
  tm start_state empty_symbol = (s, d, start_state) ->
  ~ halts tm.
Proof.
  intros. intros contra. destruct contra as [c [Heval Hhalt]].
  assert (Hstate: curr_state c = start_state /\ curr_symb c = empty_symbol /\
                  tape_dir d c = nil). {
    clear Hhalt. remember start_config as c_start. induction Heval.
    - subst. split. reflexivity. split. reflexivity. destruct d; reflexivity. 
    - apply a_rep with (s:=s) (d:=d); try assumption.
      apply IHHeval; assumption. }
  destruct Hstate. rewrite H0 in Hhalt. inversion Hhalt.
Qed.

Function score_symbol symb :=
  match symb with
    | Symbol 0 => 0
    | Symbol _ => 1
  end.

Fixpoint score_tape t :=
  match t with
    | nil => 0
    | s :: rest => (score_symbol s) + score_tape rest
  end.

Function score_config c :=
  score_symbol (curr_symb c) + score_tape (left_tape c) +
  score_tape (right_tape c).

(* Number of non-empty symbols on halting tape which is busy beaver "score" *)
Definition score tm value := exists c,
  eval tm start_config c /\ curr_state c = Halt /\ score_config c = value.

Definition valid_trans nstates nsymbols (trans : symbol * dir * state) :=
  match trans with
    | (Symbol new_symb, _, State new_state) =>
        new_symb < nsymbols /\ new_state < nstates
    | (Symbol new_symb, _, Halt) => new_symb < nsymbols
  end.


Definition tm_size nstates nsymbols (tm : turing_machine) := forall st symb,
  st < nstates -> symb < nsymbols ->
  valid_trans nstates nsymbols (tm (State st) (Symbol symb)).

Function check_tm_size_cell nstates nsymbols (tm : turing_machine) st sym :=
  match tm (State st) (Symbol sym) with
    | (Symbol new_symb, _, State new_state) =>
        andb (leb new_symb nsymbols) (leb new_state nstates)
    | (Symbol new_symb, _, Halt) => leb new_symb nsymbols
  end.

Fixpoint check_tm_size_row nstates nsymbols tm st S_sym :=
  match S_sym with
    | 0 => true
    | S sym => andb (check_tm_size_cell nstates nsymbols tm st sym)
                    (check_tm_size_row nstates nsymbols tm st sym)
  end.

Fixpoint check_tm_size_helper nstates nsymbols tm S_st :=
  match S_st with
    | 0 => true
    | S st => andb (check_tm_size_row nstates nsymbols tm st nsymbols)
                   (check_tm_size_helper nstates nsymbols tm st)
  end.

Function check_tm_size nstates nsymbols tm :=
  check_tm_size_helper nstates nsymbols tm nstates.

Theorem tm_size_iff : forall nstates nsymbols tm,
  tm_size nstates nsymbols tm <-> check_tm_size nstates nsymbols tm = true.
Proof. Admitted. (* TODO *)

(* Busy Beaver function *)
Definition sigma nstates nsymbols value :=
  (exists tm, tm_size nstates nsymbols tm /\ score tm value) /\
  forall tm val', tm_size nstates nsymbols tm -> score tm val' ->
    val' <= value.

Definition bb1 st symb := 
  match st, symb with
    | State 0, Symbol 0 => (Symbol 1, Right, Halt)  (* A0 -> 1RH *)
    | _, _ => no_result
  end.

Lemma score_halt : forall tm val, score tm val -> halts tm.
Proof.
  intros. destruct H as [c [Heval [Hhalt _]]]. exists c. split; assumption.
Qed.

Lemma halt_score : forall tm, halts tm -> exists val, score tm val.
Proof.
  intros. destruct H as [c [Heval Hhalt]]. exists (score_config c).
  exists c. split; try split; try assumption. reflexivity.
Qed.

Lemma run_done : forall tm c n m,
  curr_state (run tm c n) = Halt -> n <= m -> run tm c m = run tm c n.
Proof.
  intros. induction H0.
  - reflexivity.
  - simpl. rewrite <- run_step_permute. rewrite IHle. unfold step.
    rewrite H. reflexivity.
Qed.

(* Busy Beaver 1x2 proof! *)
Theorem sigma12 : sigma 1 2 1.
Proof.
  unfold sigma. split.
  - exists bb1. split.
    + (* tm_size 1 2 bb1 *) apply tm_size_iff. reflexivity.
    + (* score bb1 1 *) exists (run bb1 start_config 1). simpl.
      split; try split; try reflexivity. apply EvalStep. apply EvalRefl.
  - intros. destruct (tm start_state empty_symbol) as [[[sym] d] st] eqn:Htrans.
    destruct st as [|[|st]].
    + (* A0 -> Halt *) destruct H0 as [c [Heval [Hhalt Hscore]]].
      apply eval_run in Heval. destruct Heval as [n Hrun]. destruct n.
      * (* 0 steps *) subst. simpl in Hhalt. inversion Hhalt.
      * (* >= 1 steps *) assert (curr_state (run tm start_config 1) = Halt). {
          simpl. unfold step. simpl. rewrite Htrans. destruct d; reflexivity. }
        apply run_done with (m:=(S n)) in H0; [|omega]. rewrite H0 in Hrun. subst.
        simpl. unfold step. simpl. rewrite Htrans.
        destruct d; destruct sym; unfold score_config; simpl; omega.
    + (* A0 -> ??A *) apply a_no_halt in Htrans. apply score_halt in H0.
      contradiction.
    + (* A0 -> ??B+ *)
      assert (valid_trans 1 2 (tm start_state empty_symbol)). { apply H; omega. }
      unfold valid_trans in H1. rewrite Htrans in H1. omega.
Qed.


(* Compressed tape format *)
Inductive repeat_config := RepeatConfig {
  RC_curr_state : state;
  RC_curr_dir : dir;
  RC_tape : list (symbol * nat) * list (symbol * nat)
}.

Function rep_tape (rt : list (symbol * nat) * list (symbol * nat)) (d : dir) :=
  match rt with
    | (left_rep, right_rep) =>
      match d with
        | Left => left_rep
        | Right => right_rep
      end
  end.

Function other_dir d :=
  match d with
    | Left => Right
    | Right => Left
  end.

Fixpoint repeat {X} (x : X) (count : nat) : list X :=
  match count with
    | 0 => nil
    | S n => x :: repeat x n
  end.

Fixpoint repeat_tape_to_tape (repeat_tape : list (symbol * nat)) : list symbol :=
  match repeat_tape with
    | nil => nil
    | (symb, pcount) :: rest => (repeat symb (S pcount)) ++ repeat_tape_to_tape rest
  end.

Function rep2config rc :=
  match rc with
  | RepeatConfig st d rt =>
    match d with
    | Left => Config st
                     (top_symbol (repeat_tape_to_tape (rep_tape rt d)))
                     (tail (repeat_tape_to_tape (rep_tape rt Left)))
                     (repeat_tape_to_tape (rep_tape rt Right))
    | Right => Config st
                     (top_symbol (repeat_tape_to_tape (rep_tape rt d)))
                     (repeat_tape_to_tape (rep_tape rt Left))
                     (tail (repeat_tape_to_tape (rep_tape rt Right)))
    end
  end.

Lemma combine_rep : forall symb pn pm rest,
  repeat_tape_to_tape ((symb, pn) :: (symb, pm) :: rest) =
  repeat_tape_to_tape ((symb, S (pn + pm)) :: rest).  (* n + m - 1 = (n - 1) + (m - 1) + 1 *)
Proof.
  induction pn; intros.
  - (* n = 1 *) simpl. reflexivity.
  - simpl. simpl in IHpn. rewrite IHpn. reflexivity.
Qed.

Theorem eval_trans : forall tm c1 c2 c3,
  eval tm c1 c2 -> eval tm c2 c3 -> eval tm c1 c3.
Proof.
  intros. induction H0. assumption. apply EvalStep. apply IHeval. assumption.
Qed.

Theorem long_step : forall tm st st_num d in_symb out_symb pcount front_rest back_rest rt rt',
  d = Right -> (* TODO *)
  st = State st_num ->
  tm st in_symb = (out_symb, d, st) ->                  (* A1 -> 2RA *)
  rt = (back_rest, (in_symb, pcount) :: front_rest) ->    (* rc:  ... A> 1^n ... *)
  rt' = ((out_symb, pcount) :: back_rest, front_rest) ->  (* rc': ... 2^n A> ... *)
  eval tm (rep2config (RepeatConfig st d rt))
          (rep2config (RepeatConfig st d rt')).
Proof.
  induction pcount; intros.
  - (* count = 1 *) replace (rep2config (RepeatConfig st d rt')) with
                            (step tm (rep2config (RepeatConfig st d rt))).
    + apply EvalStep. apply EvalRefl.
    + subst. simpl. unfold step. simpl. rewrite H1. reflexivity.
  - (* count = n+1 *)
    remember ((out_symb, 0) :: back_rest, (in_symb, pcount) :: front_rest) as new_rt.
    remember ((out_symb, pcount) :: (out_symb, 0) :: back_rest, front_rest) as new_rt'.
    apply eval_trans with (rep2config (RepeatConfig st d new_rt)).
    + (* rt -> new_rt *) replace (rep2config (RepeatConfig st d new_rt)) with
                                 (step tm (rep2config (RepeatConfig st d rt))).
      * apply EvalStep. apply EvalRefl.
      * subst. simpl. unfold step. simpl. rewrite H1. reflexivity.
    + (* new_rt -> new_rt' *) replace (rep2config (RepeatConfig st d rt')) with
                                      (rep2config (RepeatConfig st d new_rt')).
      * apply IHpcount with front_rest ((out_symb, 0) :: back_rest); try assumption.
      * subst. unfold rep2config. unfold rep_tape. rewrite (combine_rep out_symb).
        rewrite plus_0_r. reflexivity.
Qed.

Lemma infinite_step_helper : forall tm st st_num d out_symb back_rest rt c,
  d = Right -> (* TODO *)
  st = State st_num ->
  tm st empty_symbol = (out_symb, d, st) ->  (* B0 -> 1RB *)
  rt = (back_rest, nil) ->                   (* rc:  ... B> 0^Inf *)
  eval tm (rep2config (RepeatConfig st d rt)) c ->
  exists back_rest', c = rep2config (RepeatConfig st d (back_rest', nil)).
Proof.
  intros. remember (rep2config (RepeatConfig st d rt)) as c_init. induction H3.
  - exists back_rest. rewrite <- H2. assumption.
  - destruct IHeval; try assumption. exists ((out_symb, 0) :: x). subst. simpl.
    unfold step. simpl. rewrite H1. reflexivity.
Qed.

Theorem infinite_step : forall tm st st_num d out_symb back_rest rt,
  d = Right -> (* TODO *)
  st = State st_num ->
  tm st empty_symbol = (out_symb, d, st) ->  (* B0 -> 1RB *)
  rt = (back_rest, nil) ->                   (* rc:  ... B> 0^Inf *)
  ~ halts_from tm (rep2config (RepeatConfig st d rt)).
Proof.
  intros. intros Hhalt. unfold halts_from in Hhalt. destruct Hhalt as [c_halt [Heval Hhalt]].
  apply infinite_step_helper with (st_num:=st_num) (out_symb:=out_symb) (back_rest:=back_rest)
    in Heval; try assumption. destruct Heval as [back_rest' Hc_halt]. subst. simpl in Hhalt.
  inversion Hhalt.
Qed.

Function mirror_tm (tm : turing_machine) st symb :=
  match tm st symb with (out_symb, d, out_state) =>
    (out_symb, other_dir d, out_state)
  end.

Function mirror_config c :=
  match c with Config st symb left_tape right_tape =>
    Config st symb right_tape left_tape
  end.

Require Import FunctionalExtensionality.

Lemma other_other_dir : forall d, other_dir (other_dir d) = d.
Proof. intros. destruct d; reflexivity. Qed.

Lemma double_mirror_tm : forall tm, mirror_tm (mirror_tm tm) = tm.
Proof.
  intros. apply functional_extensionality. intros st.
  apply functional_extensionality. intros symb. unfold mirror_tm.
  destruct (tm st symb) as [[out_symb out_dir] out_state].
  rewrite other_other_dir. reflexivity.
Qed.

Lemma double_mirror_config : forall c, mirror_config (mirror_config c) = c.
Proof. intros. destruct c. simpl. reflexivity. Qed.

Theorem mirror_step : forall tm c c',
  step tm c = c' -> step (mirror_tm tm) (mirror_config c) = mirror_config c'.
Proof.
  intros. destruct c. unfold step in *. destruct curr_state0; simpl in *.
  - (* Halt *) subst. reflexivity.
  - subst. unfold mirror_tm, mirror_config.
    destruct (tm (State n) curr_symb0) as [[out_symb out_dir] out_state].
    destruct out_dir; reflexivity.
Qed.

Theorem mirror_eval : forall tm c c',
  eval tm c c' -> eval (mirror_tm tm) (mirror_config c) (mirror_config c').
Proof.
  intros. induction H.
  - (* EvalRefl *) apply EvalRefl.
  - (* EvalStep *) rewrite <- mirror_step with tm c' (step tm c'); [|reflexivity].
    apply EvalStep. assumption.
Qed.

Lemma mirror_eval_rev : forall tm c c',
  eval (mirror_tm tm) (mirror_config c) (mirror_config c') -> eval tm c c'.
Proof.
  intros. apply mirror_eval in H. rewrite double_mirror_tm in H.
  rewrite double_mirror_config in H. rewrite double_mirror_config in H. assumption.
Qed.

Lemma mirror_repeat_config : forall st d left_tape right_tape,
  mirror_config (rep2config (RepeatConfig st d (left_tape, right_tape))) =
  rep2config (RepeatConfig st (other_dir d) (right_tape, left_tape)).
Proof. intros. simpl. destruct d; reflexivity. Qed.

Lemma long_step_left : forall tm st st_num d in_symb out_symb pcount front_rest back_rest rt rt',
  d = Left ->
  st = State st_num ->
  tm st in_symb = (out_symb, d, st) ->
  rt = ((in_symb, pcount) :: front_rest, back_rest) ->
  rt' = (front_rest, (out_symb, pcount) :: back_rest) ->
  eval tm (rep2config (RepeatConfig st d rt))
          (rep2config (RepeatConfig st d rt')).
Proof.
  intros. apply mirror_eval_rev. subst. rewrite mirror_repeat_config.
  rewrite mirror_repeat_config. eapply long_step; try reflexivity.
  unfold mirror_tm. rewrite H1. reflexivity.
Qed.

(* Christmas Tree TM *)
Definition tree st symb :=
  match st, symb with
    | State 0, Symbol 0 => (Symbol 1, Right, State 1)  (* A0 -> 1RB *)
    | State 0, Symbol 1 => (Symbol 2, Left, State 0)   (* A1 -> 2LA *)
    | State 0, Symbol 2 => (Symbol 1, Right, Halt)     (* A2 -> Halt *)
    | State 1, Symbol 0 => (Symbol 2, Left, State 0)   (* B0 -> 2LA *)
    | State 1, Symbol 1 => (Symbol 1, Right, Halt)     (* B1 -> Halt *)
    | State 1, Symbol 2 => (Symbol 1, Right, State 1)  (* B2 -> 1RB *)
    | _, _ => no_result
  end.

Lemma tree_rep : forall pn,
  eval tree (rep2config (RepeatConfig (State 0) Left (nil, (Symbol 2, pn) :: nil)))
            (rep2config (RepeatConfig (State 0) Left (nil, (Symbol 2, S (S pn)) :: nil))).
Proof.
  intros.
  remember (rep2config (RepeatConfig (State 0) Left (nil, (Symbol 2, pn) :: nil))) as A0.
  remember (rep2config (RepeatConfig (State 1) Right ((Symbol 1, 0) :: nil,
                                                      (Symbol 2, pn) :: nil))) as B2.
  remember (rep2config (RepeatConfig (State 1) Right ((Symbol 1, S pn) :: nil, nil))) as B0.
  remember (rep2config (RepeatConfig (State 0) Left ((Symbol 1, S pn) :: nil,
                                                     (Symbol 2, 0) :: nil))) as A1.
  remember (rep2config (RepeatConfig (State 0) Left (nil, (Symbol 2, S (S pn)) :: nil)))
    as A0'.

  apply eval_trans with A1. apply eval_trans with B0. apply eval_trans with B2.
  - (* <A 2^n -> 1 B> 2^n *) replace B2 with (step tree A0).
    + apply EvalStep. apply EvalRefl.
    + subst. reflexivity.
  - (* 1 B> 2^n -> 1^(n+1) B> *)
    replace B0 with (rep2config (RepeatConfig (State 1) Right
                                   ((Symbol 1, pn) :: (Symbol 1, 0) :: nil, nil))); subst.
    + eapply long_step; try reflexivity. simpl. reflexivity.
    + unfold rep2config, rep_tape. rewrite combine_rep. rewrite plus_0_r. reflexivity.
  - (* 1^(n+1) B> -> 1^(n+1) <A 2 *) replace A1 with (step tree B0).
    + apply EvalStep. apply EvalRefl.
    + subst. reflexivity.
  - (* 1^(n+1) <A 2 -> <A 2^(n+2) *)
    replace A0' with (rep2config (RepeatConfig (State 0) Left
                                    (nil, (Symbol 2, S pn) :: (Symbol 2, 0) :: nil))); subst.
    + eapply long_step_left; simpl; try reflexivity. simpl. reflexivity.
    + unfold rep2config, rep_tape. rewrite combine_rep. rewrite plus_0_r. reflexivity.
Qed.

Theorem rep_no_halt : forall tm,
  (forall c, exists c', eval tm c c' /\ c <> c' /\ config_state c' <> Halt) ->
  ~ halts_from tm c.

Theorem tree_no_halt : ~ halts tree.
Proof.
  intros [c [Heval Hhalt]].

Function beq_dir d1 d2 :=
  match d1, d2 with
    | Left, Left => true
    | Right, Right => true
    | _, _ => false
  end.

Inductive opt_infinite :=
  | Finite: nat -> opt_infinite
  | Inf: opt_infinite.

Function top_repeat rt :=
  match rt with
    | nil => (empty_symbol, Inf)
    | (symb, pcount) :: rest => (symb, Finite pcount)
  end.

Inductive running_state :=
  | Running : repeat_config -> running_state
  | Halted : repeat_config -> running_state
  | ProvenInfinite : running_state.

Function new_rep_tape d t1 t2 : list (symbol * nat) * list (symbol * nat) :=
  match d with
    | Left => (t1, t2)
    | Right => (t2, t1)
  end.

Function beq_state s1 s2 :=
  match s1, s2 with
    | Halt, Halt => true
    | State s1, State s2 => beq_nat s1 s2
    | _, _ => false
  end.

Function beq_symb s1 s2 :=
  match s1, s2 with
    | Symbol s1, Symbol s2 => beq_nat s1 s2
  end.

Function push_repeat new_symb new_pcount d rt :=
  match top_repeat (rep_tape rt d) with
    | (symb, pcount) =>
      if beq_symb symb new_symb
        then match pcount with
             | Inf => rt (* No change if we push 0^n onto 0^Inf *)
             | Finite pcount => (* Note pcount is rep_count - 1. Thus +1. *)
               new_rep_tape d ((symb, pcount + new_pcount + 1) :: tail (rep_tape rt d))
                              (rep_tape rt (other_dir d))
             end
        else new_rep_tape d ((new_symb, new_pcount) :: rep_tape rt d)
                            (rep_tape rt (other_dir d))
  end.

Function remove_top_repeat d rt :=
  new_rep_tape d (tail (rep_tape rt d)) (rep_tape rt (other_dir d)).

Function remove_top_symb d rt :=
  match top_repeat (rep_tape rt d) with
    | (symb, Inf) => rt (* No change if we remove 0 from 0^Inf *)
    | (symb, Finite 0) => remove_top_repeat d rt (* 1 left -> remove whole repeat. *)
    | (symb, Finite (S pcount)) =>
      new_rep_tape d ((symb, pcount) :: (tail (rep_tape rt d))) (rep_tape rt (other_dir d))
  end.

Function repeat_step tm rc :=
match rc with | RepeatConfig st d rt =>
  match st with
  | Halt => Halted rc
  | State _ =>
    match top_repeat (rep_tape rt d) with
    | (symb, pcount) =>
      match tm st symb with
      | (new_symb, new_dir, new_state) =>
        match beq_dir d new_dir, beq_state st new_state with
        | true, true => (* A> 1^n -> 2^n A> *)
          match pcount with
          | Inf => ProvenInfinite
          | Finite pcount => Running (RepeatConfig new_state new_dir
(push_repeat new_symb pcount (other_dir new_dir)
  (remove_top_repeat d rt)))
          end
        | _, _ => Running (RepeatConfig new_state new_dir 
(push_repeat new_symb 0 (other_dir new_dir) (* Push new symb in ~ new dir *)
  (remove_top_symb d rt))) (* Remove top symb in old dir *)
        end
      end
    end
  end
end.

(*
Lemma repeat_step_inf_spec : forall tm rc,
  repeat_step tm rc = ProvenInifinte ->
  match rc with
    | RepeatConfig st d rt =>
      rep_tape rt d = nil /\ ...
*)

Theorem repeat_step_inf : forall tm rc c',
  repeat_step tm rc = ProvenInfinite -> eval tm (rep2config rc) c' ->
  (rep2config rc) = c'.
Proof.
  intros.
Abort.

Theorem repeat_step_eval : forall tm rc rc',
  repeat_step tm rc = Running rc' \/ repeat_step tm rc = Halted rc' ->
  eval tm (rep2config rc) (rep2config rc').
Proof.
  intros. destruct rc. destruct RC_curr_state0.
  - (* Halt *) simpl in H. destruct H; inversion H. subst. apply EvalRefl.
  - (* State st *) simpl in H.
Abort.


