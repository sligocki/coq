Require Import Arith Le List Omega.
Import ListNotations.

Section DistrSystem.

Parameter Name : Set.
Parameter Input : Set.
Parameter Output : Set.
Parameter Message : Set.
Parameter State : Name -> Set.
Parameter InputHandler :
  forall name : Name, State name -> Input
  -> (State name * list Output * list Message).
Parameter MessageHandler :
  forall dst : Name, State dst -> Name -> Message
  -> (State dst * list Output * list Message).

Parameter beq_Name : Name -> Name -> bool.
Parameter beq_Name_eq : forall n1 n2, n1 = n2 <-> beq_Name n1 n2 = true.

Definition States := forall n : Name, State n.


Inductive DistrState := DState {
  in_flight_messages : list Message;
  node_states : States;
  history : list (option Input * list Output)
}.

Function update (states : States) (update_name : Name)
                (new_state : State update_name) : States :=
  fun (n : Name) => if beq_Name n update_name then new_state else states n.

Inductive reachable : DistrState -> DistrState -> Prop :=
  | R_refl : forall s, s --> s
  | R_trans : forall s1 s2 s3,
      s1 --> s2  ->  s2 --> s3  ->  s1 --> s3
  | R_input : forall s ...,
      InputHandler name (states name) input
        = (new_state, new_outputs, new_messages) ->
      DistrState messages states hist
      --> Distr (new_messages ++ messages) (update states name new_state)
                ((Some input, new_outputs) :: hist)

where (s --> t) = reachable s t.