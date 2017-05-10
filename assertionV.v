Require Import util.
Require Import Coq.omega.Omega.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import language.
Require Import semantic.
Require Import state.
Import ListNotations.


Definition assertionV := state -> Prop.


Definition empV : assertionV :=
  fun st:state => match st with
                  | (stoV,stoB,stoF,hV,hB) => hV = emp_heapV
                  end.

Definition trueV : assertionV :=
  fun st:state => True.


Definition falseV : assertionV :=
  fun st:state => False.

Definition point_toV (e1 e2:aexp) : assertionV :=
  fun st:state =>
  match st with
  | (stoV,stoB,stoF,hV,hB) => 
      hV = h_updateV emp_heapV (aeval stoV stoF e1) (aeval stoV stoF e2)
  end.

Notation "e1 '|->' e2" := (point_toV e1 e2) (at level 60).


Definition notV (p:assertionV) : assertionV :=
  fun st:state => not (p st).

Definition eqV (a1 a2: aexp) : assertionV :=
  fun st:state =>
  match st with
  | (stoV,stoB,stoF,hV,hB) => (aeval stoV stoF a1) = (aeval stoV stoF a2)
  end.

Definition leV (a1 a2: aexp) : assertionV :=
  fun st:state =>
  match st with
  | (stoV,stoB,stoF,hV,hB) => (aeval stoV stoF a1) <= (aeval stoV stoF a2)
  end.



Definition sep_conjV (p q : assertionV) : assertionV :=
    fun st: state =>
      match st with
      | (stoV,stoB,stoF,hV,hB) => 
        exists hv1, exists hv2,
          disjointV hv1 hv2 /\ h_unionV hv1 hv2 = hV /\ 
          p (stoV,stoB,stoF,hv1,hB) /\ q (stoV,stoB,stoF,hv2,hB)
      end.
Notation "p '**' q" := (sep_conjV p q) (at level 70).


Definition sep_disjV (p q: assertionV) : assertionV :=
  fun (st : state) =>
    match st with
    | (stoV,stoB,stoF,hV,hB) => 
      forall hv', disjointV hv' hV -> p (stoV,stoB,stoF, hv', hB) -> 
      q (stoV,stoB,stoF,h_unionV hV hv',hB)
    end.
Notation "p '--*' q" := (sep_disjV p q) (at level 80).

Definition s_conjV (p q: assertionV) : assertionV :=
  fun (s: state) => p s /\ q s.
Notation "p '//\\' q" := (s_conjV p q) (at level 75).

Definition s_disjV (p q: assertionV) : assertionV :=
  fun (s: state) => p s \/ q s.
Notation "p '\\//' q" := (s_disjV p q) (at level 78).

Definition s_impV (p q: assertionV) : assertionV :=
  fun (s: state) => p s -> q s.
Notation "p '-->' q" := (s_impV p q) (at level 85).


Definition strongerThanV (p q: assertionV) : Prop :=
  forall s: state, s_impV p q s.
Notation "p '==>' q" := (strongerThanV p q) (at level 90).




