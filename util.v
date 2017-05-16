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
Proof.
  intros. split.
  -intros. unfold beq_id in *. destruct x. destruct y.
   destruct (string_dec s s0). +subst. auto. +inversion H.
  -intros. unfold beq_id. destruct x. destruct y.
   destruct (string_dec s s0). +auto. +inversion H. subst.
   destruct n. auto.
Qed.


Theorem false_beq_id :
  forall x y : id,
  x <> y <-> beq_id x y = false.
Proof.
  intros. split; unfold beq_id in *.
  -intros. destruct x. destruct y. destruct (string_dec s s0).
   +subst. destruct H. auto. +auto.
  -intros. destruct x. destruct y. destruct (string_dec s s0).
   +inversion H. +clear H. unfold not in *. intros. inversion H.
    contradiction.
Qed.

