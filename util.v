Require Import Coq.Strings.String.

Inductive id : Type :=
| Id      : string -> id.

Definition beq_id id1 id2 :=
  match id1,id2 with
  | Id n1, Id n2 => if string_dec n1 n2 then true else false
  end.

Theorem beq_id_true_iff :
  forall x y : id,
  beq_id x y = true <-> x = y.
Admitted.

Theorem false_beq_id :
  forall x y : id,
  x <> y <-> beq_id x y = false.
Admitted.

