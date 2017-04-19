Require Import util.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.


Definition storeV := id -> nat.
Definition storeB := id -> nat.
Definition storeF := id -> list nat.

Definition heapV := nat -> option nat.
Definition heapB := nat -> option nat.

Definition emp_heapV : heapV :=
  fun (n: nat) => None.

Definition emp_heapB : heapB :=
  fun (n: nat) => None.


Definition in_domV (l: nat) (h: heapV) : Prop :=
  exists n, h l = Some n.

Definition in_domB (l: nat) (h: heapB) : Prop :=
  exists n, h l = Some n.


Definition not_in_domV (l: nat) (h: heapV) : Prop :=
  h l = None.

Definition not_in_domB (l: nat) (h: heapB) : Prop :=
  h l = None.



Theorem in_not_in_dec_V :
  forall l h, {in_domV l h} + {not_in_domV l h}.
Proof.
  intros l h. unfold in_domV. unfold not_in_domV.
  destruct (h l).
  left. exists n. auto.
  right. auto.
Qed.

Theorem in_not_in_dec_B :
  forall l h, {in_domB l h} + {not_in_domB l h}.
Proof.
  intros l h. unfold in_domB. unfold not_in_domB.
  destruct (h l).
  left. exists n. auto.
  right. auto.
Qed.




Definition disjointV (h1 h2: heapV) : Prop :=
  forall l, not_in_domV l h1 \/ not_in_domV l h2.

Definition disjointB (h1 h2: heapB) : Prop :=
  forall l, not_in_domB l h1 \/ not_in_domB l h2.

Definition h_unionV (h1 h2: heapV) : heapV :=
  fun l =>
    if (in_not_in_dec_V l h1) then h1 l else h2 l.

Definition h_unionB (h1 h2: heapB) : heapB :=
  fun l =>
    if (in_not_in_dec_B l h1) then h1 l else h2 l.


(* h1 is a subset of h2 *)
Definition h_subsetV (h1 h2: heapV) : Prop :=
  forall l n, h1 l = Some n -> h2 l = Some n.

Definition h_subsetB (h1 h2: heapB) : Prop :=
  forall l n, h1 l = Some n -> h2 l = Some n.


(* store update *)
Definition st_updateV (s: storeV) (x: id) (n: nat) : storeV :=
  fun x' => if beq_id x x' then n else s x'.

Definition st_updateB (s: storeB) (x: id) (n: nat) : storeB :=
  fun x' => if beq_id x x' then n else s x'.

Definition st_updateF (s: storeF) (x: id) (nli: list nat) : storeF :=
  fun x' => if beq_id x x' then nli else s x'.



(* heap update *)
Definition h_updateV (h: heapV) (l: nat) (n: nat) : heapV :=
  fun l' => if beq_nat l l' then Some n else h l'.

Definition h_updateB (h: heapB) (l: nat) (n: nat) : heapB :=
  fun l' => if beq_nat l l' then Some n else h l'.


(* heap remove *)
Definition h_removeV (h:heapV) (l:nat) : heapV :=
fun x => if eq_nat_dec x l then None else h x.

Definition h_removeB (h:heapB) (l:nat) : heapB :=
fun x => if eq_nat_dec x l then None else h x.


Definition state : Type := (storeV * storeB * storeF * heapV * heapB).

Inductive ext_state : Type :=
|  St:  state -> ext_state    (* normal state *)
| Abt: ext_state.             (* abort *)


