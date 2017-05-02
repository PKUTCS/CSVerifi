Require Import util.
Require Import Coq.omega.Omega.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import language.
Require Import semantic.
Require Import state.
Require Import assertionV.
Require Import assertionB.
Require Import assertionG.
Import ListNotations.


Definition triple (P:assertionG) (c:command) (Q:assertionG) : Prop :=
  forall st opst, 
    P st ->
    c / st \\ opst ->
    match opst with
    | Abt => False
    | St st2 => Q st2
    end.

Notation "{{ P }} c {{ Q }}" :=
  (triple P c Q) (at level 90, c at next level).


Definition assn_sub (X: id) (a: aexp) P : assertion :=
  fun st => P ((st_update (fst st) X (aeval (fst st) a)), (snd st)).
Notation "P [ X \ a ]" := (assn_sub X a P) (at level 10).





