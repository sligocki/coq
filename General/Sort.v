Require Import Arith List.

Import ListNotations.

Section sort.

Variable X : Type.
Variable le : X -> X -> bool.
Hypothesis le_refl : forall x, le x x = true.
Hypothesis le_trans : forall x y z, le x y = true -> le y z = true -> le y z = true.
Hypothesis le_total : forall x y, le x y = true \/ le y x = true.

Fixpoint insert (x : X) (xs : list X) : list X :=
  match xs with
    | [] => [x]
    | x' :: xs' =>
      if le x x' then x :: xs
                 else x' :: insert x xs'
  end.

Fixpoint insertion_sort_helper (unsorted sorted : list X) : list X :=
  match unsorted with
    | [] => sorted
    | x :: xs => insertion_sort_helper xs (insert x sorted)
  end.

Function insertion_sort (xs : list X) : list X := insertion_sort_helper xs [].


Definition lengthOrder (xs ys : list X) : Prop := length xs < length ys.

Lemma length_0 : forall Y (l : list Y), 0 = length l -> l = [].
Proof.
  intros. destruct l. reflexivity. simpl in H. inversion H.
Qed.

Lemma lengthOrder_wf' : forall len, forall ls, length ls <= len -> Acc lengthOrder ls.
Proof.
  induction len.
  - intros. constructor. intros.

apply le_n_0_eq in H. apply length_0 in H. subst. constructor.


Fixpoint sorted_merge (xs ys : list X) : list X :=
  match xs, ys with
    | [], _ => ys
    | _, [] => xs
    | x :: xs', y :: ys' =>
      if le x y then x :: sorted_merge xs' ys
                else y :: sorted_merge xs ys'
  end.

Fixpoint merge_sort (xs : list X) : list X :=
  match split xs with (ys, zs) =>
    sorted_merge (merge_sort ys) (merge_sort zs)
  end.