Require Import Bool Arith List.
Set Implicit Arguments.
Set Asymmetric Patterns.

Function pred1 (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Function pred2 (n : nat) : option nat :=
  match n with
    | O => None
    | S n' => Some n'
  end.

Lemma not_0_ne_0 : 0 <> 0 -> False.
auto. Qed.

Function pred3 (n : nat) : n <> 0 -> nat :=
  match n with
    | O => fun Hn0 : 0 <> 0 => match (not_0_ne_0 Hn0) with end
    | S n' => fun _ => n'
  end.

Program Definition pred4 (n : nat) : n <> 0 -> {m : nat | S m = n} :=
  match n with
    | O => fun Hn0 : 0 <> 0 => match (not_0_ne_0 Hn0) with end
    | S n' => fun _ => exist _ n' _
  end.

Program Definition pred5 (sn : {n : nat | n <> 0}) : {m : nat | S m = proj1_sig sn} :=
  match sn with
    | 0 => _
    | S n' => exist _ n' _
  end.

Definition pred6 (n : nat) : n <> 0 -> {m : nat | S m = n}.
  refine (
    match n with
      | O => fun _ => False_rec _ _
      | S n' => fun _ => exist _ n' _
    end). apply _H. reflexivity. reflexivity.
Qed.