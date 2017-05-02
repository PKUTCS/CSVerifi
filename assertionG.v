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
Import ListNotations.



Definition assertionG := state -> Prop.



Definition pairG (assV: assertionV) (assB: assertionB) : assertionG := 
    fun st:state => 
        (assV st) /\ (assB st).



Definition empG : assertionG :=
    pairG empV empB.

Definition s_conjG (p q: assertionG) : assertionG :=
  fun (s: state) => p s /\ q s.
Notation "p '/G\' q" := (s_conjG p q) (at level 75).

Definition s_disjG (p q: assertionG) : assertionG :=
  fun (s: state) => p s \/ q s.
Notation "p '\G/' q" := (s_disjG p q) (at level 78).

Definition s_impG (p q: assertionG) : assertionG :=
  fun (s: state) => p s -> q s.
Notation "p '--G>' q" := (s_impG p q) (at level 85).


Definition strongerThanB (p q: assertionB) : Prop :=
  forall s: state, s_impB p q s.
Notation "p '==G>' q" := (strongerThanB p q) (at level 90).




