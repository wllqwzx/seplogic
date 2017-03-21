Require Import util.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.


Definition store := id -> nat.

Definition heap := nat -> option nat.

Axiom finite_heap : forall h: heap, exists n: nat,
  forall n' v: nat, h n' = Some v -> n' < n.

Definition emp_heap : heap :=
  fun (n: nat) => None.


Definition in_dom (l: nat) (h: heap) : Prop :=
  exists n, h l = Some n.

Definition not_in_dom (l: nat) (h: heap) : Prop :=
  h l = None.
  
Theorem in_not_in_dec :
  forall l h, {in_dom l h} + {not_in_dom l h}.
Proof.
  intros l h. unfold in_dom. unfold not_in_dom.
  destruct (h l).
  left. exists n. auto.
  right. auto.
Qed.



Definition disjoint (h1 h2: heap) : Prop :=
  forall l, not_in_dom l h1 \/ not_in_dom l h2.

Definition h_union (h1 h2: heap) : heap :=
  fun l =>
    if (in_not_in_dec l h1) then h1 l else h2 l.


(* h1 is a subset of h2 *)
Definition h_subset (h1 h2: heap) : Prop :=
  forall l n, h1 l = Some n -> h2 l = Some n.



(* store update *)
Definition st_update (s: store) (x: id) (n: nat) : store :=
  fun x' => if beq_id x x' then n else s x'.


(* heap update *)
Definition h_update (h: heap) (l: nat) (n: nat) : heap :=
  fun l' => if beq_nat l l' then Some n else h l'.






Definition state : Type := (store * heap).

(* since program may abort, we extend our state
   definition to add a special state Abt *)
Inductive ext_state : Type :=
|  St:  state -> ext_state    (* normal state *)
| Abt: ext_state.             (* abort *)





