Require Import Arith Le List Omega.

Import ListNotations.

Inductive state (Q : Type) :=
  | Halt : state Q
  | State : Q -> state Q.

Arguments Halt {Q}.
Arguments State {Q} _.

Inductive symbol (Y : Type) :=
  | Symbol : Y -> symbol Y.

Arguments Symbol {Y} _.

Inductive dir : Set :=
  | Left : dir
  | Right : dir.

Inductive turing_machine (Q Y : Type) := TM {
  trans_table : state Q -> symbol Y -> dir -> state Q * symbol Y * dir;
  start_state : state Q;
  empty_symbol : symbol Y
}.

Arguments TM {Q Y} _ _ _.

Inductive config (Q Y : Type) := Config {
  curr_state : state Q;
  curr_dir : dir;
  tape : list (symbol Y) * list (symbol Y)
}.

Arguments Config {Q Y} _ _ _.
Arguments curr_state {Q Y} _.

Function start_config {Q Y} (tm : turing_machine Q Y) : config Q Y :=
  match tm with TM _ start_st _
    => Config start_st Right ([], [])
  end.

Function top_default {X} (t : list X) (default : X) : X :=
  match t with
    | top :: rest => top
    | [] => default
  end.

Function tail {X} (t : list X) : list X :=
  match t with
    | top :: rest => rest
    | [] => []
  end.

Function pop_top {Y} (tape : list (symbol Y) * list (symbol Y))
                     (d : dir) (empty_symb : symbol Y)
  : symbol Y * (list (symbol Y) * list (symbol Y)) :=
  match tape with (left_tp, right_tp) =>
    match d with
      | Left  => (top_default left_tp empty_symb,  (tail left_tp, right_tp))
      | Right => (top_default right_tp empty_symb, (left_tp, tail right_tp))
    end
  end.

Function push_back {Y} (symb : symbol Y) (tape : list (symbol Y) * list (symbol Y))
                       (d : dir) : list (symbol Y) * list (symbol Y) :=
  match tape with (left_tp, right_tp) =>
    match d with
      | Left  => (left_tp, symb :: right_tp)
      | Right => (symb :: left_tp, right_tp)
    end
  end.

Function step {Q Y} (tm : turing_machine Q Y)
                               (c : config Q Y) : config Q Y :=
  match c with Config curr_st curr_d curr_tape =>
    match curr_st with
      | Halt => c (* No change if already halted. *)
      | State _ =>
        match tm with TM ttable _ empty_symb =>
          let (curr_symb, tape) := pop_top curr_tape curr_d empty_symb in
            match ttable curr_st curr_symb curr_d with
              (new_state, new_symbol, new_dir) =>
                Config new_state new_dir (push_back new_symbol tape new_dir)
            end
        end
    end
  end.

(* eval tm c c' <-> tm can reach c' from c through a series of steps. *)
Inductive eval {Q Y} : turing_machine Q Y -> config Q Y -> config Q Y -> Prop :=
  | EvalRefl : forall tm c, eval tm c c
  | EvalStep : forall tm c c', eval tm c c' -> eval tm c (step tm c').

Definition halts_from {Q Y} (tm : turing_machine Q Y) (c : config Q Y) :=
  exists c_halt, eval tm c c_halt /\ curr_state c_halt = Halt.

Definition halts {Q Y} (tm : turing_machine Q Y) :=
  halts_from tm (start_config tm).

Fixpoint run {Q Y} (tm : turing_machine Q Y) (c : config Q Y) (steps : nat) :=
  match steps with
    | 0 => c
    | S k => run tm (step tm c) k
  end.

Lemma run_step_permute : forall Q Y (tm : turing_machine Q Y) c n,
  step tm (run tm c n) = run tm (step tm c) n.
Proof.
  intros. generalize dependent c. induction n; intros.
  - reflexivity.
  - simpl. apply IHn.
Qed.

Lemma eval_run : forall Q Y (tm : turing_machine Q Y) c c',
  eval tm c c' <-> exists n, c' = run tm c n.
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

Theorem halts_run : forall Q S (tm : turing_machine Q S),
  halts tm <-> exists n, curr_state (run tm (start_config tm) n) = Halt.
Proof.
  split; intros.
  - destruct H as [c [Heval Hhalt]]. apply eval_run in Heval.
    destruct Heval as [n Hrun]. exists n. rewrite <- Hrun. assumption.
  - destruct H as [n H]. exists (run tm (start_config tm) n). split.
    + apply eval_run. exists n. reflexivity.
    + assumption.
Qed.

Definition bb22_ttable st symb (d : dir) :=
  match st, symb with
    | State 0, Symbol 0 => (State 1, Symbol 1, Right)  (* A0 -> 1RB *)
    | State 0, Symbol 1 => (State 1, Symbol 1, Left)   (* A1 -> 1LB *)
    | State 1, Symbol 0 => (State 0, Symbol 1, Left)   (* B0 -> 1LA *)
    | State 1, Symbol 1 => (Halt, Symbol 1, Right)     (* B1 -> 1RH *)
    | _, _ => (Halt, Symbol 0, Right)
  end.

Definition bb22 : turing_machine nat nat :=
  TM bb22_ttable (State 0) (Symbol 0).

Example bb22_halts: halts bb22.
Proof. apply halts_run. exists 6. reflexivity. Qed.

(* Seems unnecessary to prove a_rep
Function tape_dir d c :=
  match d with
    | Left => left_tape c
    | Right => right_tape c
  end.

Lemma a_rep: forall tm st s d c,
  tm st empty_symbol = (s, d, st) ->
  curr_state c = st /\ curr_symb c = empty_symbol /\ tape_dir d c = [] ->
  curr_state (step tm c) = st /\
  curr_symb (step tm c) = empty_symbol /\ tape_dir d (step tm c) = [].
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
                  tape_dir d c = []). {
    clear Hhalt. remember start_config as c_start. induction Heval.
    - subst. split. reflexivity. split. reflexivity. destruct d; reflexivity. 
    - apply a_rep with (s:=s) (d:=d); try assumption.
      apply IHHeval; assumption. }
  destruct Hstate. rewrite H0 in Hhalt. inversion Hhalt.
Qed.
*)

(* TODO: Scoring functions will need to be built into TM 
Function score_symbol symb :=
  match symb with
    | Symbol 0 => 0
    | Symbol _ => 1
  end.

Fixpoint score_tape t :=
  match t with
    | [] => 0
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

Definition bb1 st symb := 
  match st, symb with
    | State 0, Symbol 0 => (Symbol 1, Right, Halt)  (* A0 -> 1RH *)
    | _, _ => no_result
  end.

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
*)

Definition macro_symbol Y := list (symbol Y).

Fixpoint repeat {X} (x : X) (count : nat) : list X :=
  match count with
    | 0 => []
    | S n => x :: repeat x n
  end.

Inductive macro_state Q :=
  | MacroState : Q -> macro_state Q
  | Infinite : macro_state Q.

Fixpoint bounded_run tm c max_steps :=
  match max_steps with
    | O => c
    | S n => 

Function macro_ttable {Q Y} (tm : turing_machine Q Y) :=
  fun (mst : state (macro_state Q)) (msymb : symbol (macro_symbol Y)) (d : dir) =>
    match msymb with Symbol list_symb =>
      match mst with
        | State (MacroState st) =>
          let tape := match d with
                        | Left => (list_symb, [])
                        | Right => ([], list_symb)
                      end in
            bounded_run tm (Config st d tape) 100 (* Need to calc real max steps *)
      | _ => 

Function macro_machine {Q Y} (tm : turing_machine Q Y) (block_size : nat) :=
  match tm with TM ttable start_st empty_symb _ _ =>
    TM (macro_ttable tm block_size) (State (MacroState start_st)) 
                                    (Symbol (repeat empty_symb block_size))


(* Compressed tape format.
   Tape halves are stored as a series of (symb, pcount) pairs which represents
   a string of (pcount + 1) symb. We use pcount rather than count to disallow
   having a run of length 0 which would add a lot of edge cases. *)
Inductive repeat_config (Q Y : Type) := RepeatConfig {
  RC_curr_state : state Q;
  RC_curr_dir : dir;
  RC_tape : list (symbol Y * nat) * list (symbol Y * nat)
}.

Arguments RepeatConfig {Q Y} _ _ _.

Function rep_tape {X} (rt : X * X) (d : dir) :=
  match rt with (left_rep, right_rep) =>
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

Fixpoint rep_to_tape {Y} (repeat_tape : list (symbol Y * nat)) : list (symbol Y) :=
  match repeat_tape with
    | [] => []
    | (symb, pcount) :: rest => (repeat symb (S pcount)) ++ rep_to_tape rest
  end.

Lemma combine_rep : forall Y (symb : symbol Y) pn pm rest,
  rep_to_tape ((symb, pn) :: (symb, pm) :: rest) =
  rep_to_tape ((symb, S (pn + pm)) :: rest).  (* n + m - 1 = (n - 1) + (m - 1) + 1 *)
Proof.
  induction pn; intros.
  - (* n = 1 *) simpl. reflexivity.
  - simpl. simpl in IHpn. rewrite IHpn. reflexivity.
Qed.

Function rep2config {Q Y} (tm : turing_machine Q Y) (rc : repeat_config Q Y) :=
  match tm with TM _ _ empty_symb =>
    match rc with RepeatConfig st d rt =>
      match d with
        | Left => Config st
                         (top_default (rep_to_tape (rep_tape rt d)) empty_symb)
                         (tail (rep_to_tape (rep_tape rt Left)))
                         (rep_to_tape (rep_tape rt Right))
        | Right => Config st
                          (top_default (rep_to_tape (rep_tape rt d)) empty_symb)
                          (rep_to_tape (rep_tape rt Left))
                          (tail (rep_to_tape (rep_tape rt Right)))
      end
    end
  end.

Theorem eval_trans : forall Q Y (tm : turing_machine Q Y) c1 c2 c3,
  eval tm c1 c2 -> eval tm c2 c3 -> eval tm c1 c3.
Proof.
  intros. induction H0. assumption. apply EvalStep. apply IHeval. assumption.
Qed.

Theorem long_step : forall Q Y (tm : turing_machine Q Y) st st_num d in_symb out_symb pcount front_rest back_rest rt rt',
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
  rt = (back_rest, []) ->                   (* rc:  ... B> 0^Inf *)
  eval tm (rep2config (RepeatConfig st d rt)) c ->
  exists back_rest', c = rep2config (RepeatConfig st d (back_rest', [])).
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
  rt = (back_rest, []) ->                   (* rc:  ... B> 0^Inf *)
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
  eval tree (rep2config (RepeatConfig (State 0) Left ([], [(Symbol 2, pn)])))
            (rep2config (RepeatConfig (State 0) Left ([], [(Symbol 2, S (S pn))]))).
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


