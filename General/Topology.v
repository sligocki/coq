(* Formalization of Munkres Topology *)

Require Import Ensembles Powerset.

Section Topologies.

(* Universe *)
Variable Uni : Type.

(* x in UnionCollection C if there is a set U in C such that x in U. *)
Inductive UnionCollection (C : Ensemble (Ensemble Uni)) : Ensemble Uni :=
  UnionColl_intro : forall U x,
    In _ C U -> In _ U x -> In _ (UnionCollection C) x.

(* Chapter 2: Topological Spaces and Continuous Functions *)
(* Section 12: Topological spaces *)
Inductive Topology (X : Ensemble Uni) (open_sets : Ensemble (Ensemble Uni)) :=
  topology_intro :
    (forall U, In _ open_sets U -> Included _ U X) ->  (* all sets are inside X *)
    In _ open_sets (Empty_set Uni) ->  (* empty set is open *)
    In _ open_sets X ->      (* full X is open *)
    (forall U V, In _ open_sets U -> In _ open_sets V
       -> In _ open_sets (Intersection _ U V)) ->  (* finite intersections are open *)
    (forall C, (forall U, In _ C U -> In _ open_sets U)
       -> In _ open_sets (UnionCollection C))  (* arbitrary unions are open *)
  -> Topology X open_sets.

Example DiscreteTopology: forall X : Ensemble Uni, Topology X (Power_set _ X).
Proof.
  intros. constructor; intros.
  - destruct H. assumption.
  - constructor. auto with sets.
  - constructor. auto with sets.
  - constructor. destruct H. destruct H0. unfold Included in *. intros. destruct H1.
    apply H. assumption.
  - constructor. unfold Included. intros. destruct H0. apply H in H0. destruct H0.
    unfold Included in H0. apply H0. assumption.
Qed.

(* Section 13: Basis for a Topology *)
Inductive Basis (X : Ensemble Uni) (basis : Ensemble (Ensemble Uni)) :=
  basis_intro :
    (forall B, In _ basis B -> Included _ B X) ->
    (forall x, In _ X x -> exists B, In _ basis B /\ In _ B x) ->
    (forall B1 B2 x, In _ basis B1 -> In _ basis B2 -> In _ (Intersection _ B1 B2) x
       -> exists B3, In _ basis B3 /\ In _ B3 x /\ Included _ B3 (Intersection _ B1 B2))
  -> Basis X basis.

Definition GeneratedOpenSets (X : Ensemble Uni) (basis : Ensemble (Ensemble Uni))
  (U : Ensemble Uni) :=
  Included _ U X /\
  (forall x, In _ U x -> exists B, In _ basis B /\ In _ B x /\ Included _ B U).

(* if A subset B and C subset D -> (A intersect C) subset (B intersect D) *)
Lemma BothIntersectionIncluded: forall A B C D,
  Included Uni A B -> Included Uni C D ->
  Included Uni (Intersection Uni A C) (Intersection Uni B D).
Proof.
  unfold Included in *. intros. destruct H1. constructor; auto.
Qed.

(* A subset B subset C -> A subset C *)
Lemma IncludedTrans: forall A B C,
  Included Uni A B -> Included Uni B C -> Included Uni A C.
Proof.
  unfold Included in *. auto.
Qed.

Theorem GeneratedTopology: forall X basis,
  Basis X basis -> Topology X (GeneratedOpenSets X basis).
Proof.
  intros. constructor; intros.
  - unfold In in H0. destruct H0. assumption.
  - unfold In. split; auto with sets. intros. unfold In in H0. destruct H0.
  - unfold In. split; auto with sets. intros. destruct H as [HinX HinB _].
    destruct (HinB x) as [B [HB HBx]]; trivial. exists B.
    repeat split; try assumption. apply HinX. assumption.
  - constructor. destruct H0. destruct H1.
    + unfold Included in *. intros. apply H0. destruct H4. assumption.
    + intros. destruct H2.
      destruct H0 as [_ HUB1]. destruct (HUB1 x) as [B1 [HB1 [HB1x HB1U]]]; try assumption.
      destruct H1 as [_ HVB2]. destruct (HVB2 x) as [B2 [HB2 [HB2x HB2V]]]; try assumption.
      clear HUB1 HVB2. destruct H as [_ _ HB1B2B3].
      destruct (HB1B2B3 B1 B2 x) as [B3 [HB3 [HB3x HB3inter]]]; trivial.
      constructor; assumption.
      exists B3. split; [|split]; trivial.
      * apply IncludedTrans with (B:=(Intersection Uni B1 B2)); trivial.
        apply BothIntersectionIncluded; assumption.
  - constructor.
    + unfold Included. intros. destruct H1. apply H0 in H1. destruct H1.
      destruct (H3 x) as [B [HB [HBx HBU]]]; trivial. unfold Included in *. auto.
    + intros. destruct H1. apply H0 in H1 as Hin. destruct Hin.
      destruct (H4 x) as [B [HB [HBx HBU]]]; trivial. exists B. repeat split; trivial.
      unfold Included. intros. apply UnionColl_intro with (U:=U); auto.
Qed.

(* Munkres Lemma 13.1 *)
Lemma BasisUnion: forall X basis,
  Basis X basis -> forall U, In _ (GeneratedOpenSets X basis) U ->
  exists Bs, forall B, In _ Bs B /\ Same_set _ U (UnionCollection Bs).
Proof.
  intros. (* TODO: This requires creating Bs ... *)
Abort.

(* Munkres Lemma 13.2 *)
Lemma IsBasis: forall X open_sets Bs,
  Topology X open_sets ->
  (forall B, In _ Bs B -> In _ open_sets B) ->
  (forall U, In _ open_sets U -> forall x, In _ U x ->
     exists B, In _ Bs B /\ In _ B x /\ Included _ B U) ->
  Basis X Bs /\ (GeneratedOpenSets X Bs) = open_sets.
Abort. (* TODO *)

(* Munkres Lemma 13.3 *)
(* TODO: Lemma FinerBases: ... *)
(* TODO: Example StandardRealTopology *)
(* TODO: Inductive Subbasis X Ss *)

(* Section 14: The Order Topology *)
(* A < order *)
Inductive TotalOrder (A : Ensemble Uni) (rel : Uni -> Uni -> Prop) :=
  total_order_intro:
    (forall x y, In _ A x -> In _ A y -> x = y \/ rel x y \/ rel y x) ->  (* total *)
    (forall x, In _ A x -> ~ (rel x x)) ->  (* non-reflexive *)
    (forall x y z, In _ A x -> In _ A y -> In _ A z -> rel x y -> rel y z -> rel x z) (* transitive *)
  -> TotalOrder A rel.

(* Open interval or ray *)
Inductive OpenSegment (X : Ensemble Uni) (rel : Uni -> Uni -> Prop) : Ensemble Uni -> Prop :=
  open_ray_right: forall a, In _ X a ->
    OpenSegment X rel (Intersection _ X (fun x => rel a x)) | (* Open ray (a, inf) *)
  open_ray_left:  forall b, In _ X b ->
    OpenSegment X rel (Intersection _ X (fun x => rel x b)) | (* Open ray (-inf, b) *)
  open_interval:  forall a b, In _ X a -> In _ X b ->
    OpenSegment X rel (Intersection _ X (fun x => rel a x /\ rel x b)). (* Open interval (a, b) *)

Definition CollectionOpenIntervals (X : Ensemble Uni) (rel : Uni -> Uni -> Prop)
  : Ensemble (Ensemble Uni) :=
  fun U => exists seg, OpenSegment X rel seg /\ U = seg.

Theorem OrderBasis: forall X rel,
  TotalOrder X rel -> Basis X (CollectionOpenIntervals X rel).
Proof.
  intros. constructor; intros.
  (* forall B, B subset X *)
  - unfold In in H0. unfold CollectionOpenIntervals in H0. destruct H0 as [seg [Hseg Heq]].
    subst seg. destruct Hseg; auto with sets.
  (* forall x in X, exists B, x in B *)
  - admit. (* TODO *)
  (* forall B1 B2, exists B3, B3 subset (B1 intersect B2) *)
  - exists (Intersection _ B1 B2). repeat split.
    + unfold CollectionOpenIntervals. unfold In. (* TODO: Split out and solve for all cases ... *)
Abort.

(* Section 15: The Product Topology on X * Y *)
Inductive CartProd {A B} (X : Ensemble A) (Y : Ensemble B) : Ensemble (A * B) :=
  cart_prod: forall x y, In _ X x -> In _ Y y -> In _ (CartProd X Y) (x, y).

Definition BoxBasis {A B} (openX : Ensemble (Ensemble A)) (openY : Ensemble (Ensemble B))
  : Ensemble (Ensemble (A * B)) :=
  fun U => exists UX UY, U = CartProd UX UY.

(*Theorem ProductBasis: forall X Y openX openY,
  Topology X openX -> Topology Y openY -> Basis (CartProd X Y) (BoxBasis openX openY). (* TODO: Uni <> Uni * Uni ... sigh *)
*)

(* Section 16: The Subspace Topology *)
Definition Restrict (open : Ensemble (Ensemble Uni)) (A : Ensemble Uni) : Ensemble (Ensemble Uni) :=
  fun U => exists V, In _ open V /\ U = Intersection _ V A.

Lemma IncludedIntersectionEq: forall (X A : Ensemble Uni),
  Included _ A X -> A = Intersection _ X A.
Proof.
  intros. apply Extensionality_Ensembles. split; auto with sets.
Qed.
Hint Resolve IncludedIntersectionEq: sets.

Lemma IntersectionTrans: forall X Y Z : Ensemble Uni,
  Intersection _ (Intersection _ X Y) Z = Intersection _ X (Intersection _ Y Z).
Proof.
  intros. apply Extensionality_Ensembles. split.
  - constructor; repeat destruct H; auto with sets.
  - constructor; destruct H; destruct H0; auto with sets.
Qed.
Hint Resolve IntersectionTrans: sets.
Hint Rewrite IntersectionTrans: sets.

Lemma IntersectionTrans2: forall (X Y Z : Ensemble Uni),
  Intersection _ (Intersection _ X Z) (Intersection _ Y Z) = Intersection _ (Intersection _ X Y) Z.
Proof.
  intros. autorewrite with sets.
  replace (Intersection Uni Z (Intersection Uni Y Z)) with (Intersection _ Y Z); auto with sets.
Qed.
Hint Resolve IntersectionTrans2: sets.

(* Filter open to only include U st U inter A in C. *)
Definition Raise (open C : Ensemble (Ensemble Uni)) (A : Ensemble Uni) : Ensemble (Ensemble Uni) :=
  fun U => In _ open U /\ In _ C (Intersection _ U A).

(* TODO: Maybe prove that Restrict (Raise C A) A = C ? *)
(* TODO: Maybe prove that (UnionCollection C) inter A = UnionCollection (Restrict C A) *)

Theorem SubspaceTopology: forall X open A,
  Topology X open -> Included _ A X -> Topology A (Restrict open A).
Proof.
  intros. constructor; intros.
  - (* all open are subset A *) destruct H1 as [V [HVopen Heq]]. subst. auto with sets.
  - (* Empty is open *) exists (Empty_set _). split.
    + (* Empty set is open in X *) apply H.
    + (* Empty = Empty intersect A *) auto with sets.
  - (* A is open *) exists X. split.
    + (* X open in X *) apply H.
    + (* A = X intersect A *) auto with sets.
  - (* U, V open -> U inter V open *) destruct H1 as [U' [HU'open Heq]]. subst.
    destruct H2 as [V' [HV'open Heq]]. subst.
    exists (Intersection _ U' V'). split.
    + (* U' inter V' open in X *) apply H; trivial.
    + auto with sets.
  - (* all U in C open -> Union C open *) exists (UnionCollection (Raise open C A)). split.
    + apply H. intros. destruct H2. trivial.
    + (* Union C = (Union C') inter A *) apply Extensionality_Ensembles. split.
      * intros U HUC. auto with sets.

(* ... *)
Axiom QuantFunc: forall X Y (R : X -> Prop) (P : X -> Y -> Prop),
  (forall x, R x -> exists y, P x y) -> exists f, forall x, R x -> P x (f x).

(* Section 17: Closed Sets and Limit Points *)
(* TODO: Hausdorff Spaces *)
(* Section 18: Continuous Functions *)
(* Section 19: The Product Topology *)
(* Section 20: The Metric Topology *)
(* Section 22: The Quotient Topology *)

(* Chapter 3: Connectedness and Compactness *)




























