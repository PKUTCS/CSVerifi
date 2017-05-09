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



Definition assn_sub (X: id) (a: aexp) P : assertionG :=
  fun st => 
  match st with
  | (stoV,stoB,stoF,hV,hB) => 
      P ((st_updateV stoV X (aeval stoV stoF a)), stoB,stoF,hV,hB)
  end.
Notation "P [ X \ a ]" := (assn_sub X a P) (at level 10).


Definition bassn b : assertionG :=
  fun st => 
  match st with 
  | (stoV,stoB,stoF,hV,hB) => 
      (beval stoV stoB stoF b = Some true)
  end.

Definition not_bassn b : assertionG :=
  fun st => 
  match st with 
  | (stoV,stoB,stoF,hV,hB) => 
      (beval stoV stoB stoF b = Some false)
  end.


Definition bassn_Abt b : assertionG :=
  fun st => 
  match st with 
  | (stoV,stoB,stoF,hV,hB) => 
      (beval stoV stoB stoF b = None)
  end.


Lemma bexp_eval_true : forall b stoV stoB stoF hV hB,
  beval stoV stoB stoF b = Some true -> 
  (bassn b) (stoV,stoB,stoF,hV,hB).
Proof.
  intros.
  unfold bassn. assumption.
Qed.

Lemma bexp_eval_false : forall b stoV stoB stoF hV hB,
  beval stoV stoB stoF b = Some false -> 
  not ((bassn b) (stoV,stoB,stoF,hV,hB)).
Proof.
  unfold bassn, not.
  intros. rewrite H in H0. inversion H0.
Qed.

Definition reverse bkli : list bkexp :=
match bkli with
| [] => []
| x::xl => xl ++ [x]
end.

Fixpoint bkli_to_fe (bkli:list bkexp) : fe:=
match bkli with
| [] => Nil
| x::xl => Appbk (bkli_to_fe xl) x
end.


Inductive triple: assertionG -> command -> assertionG -> Prop :=
| rule_asgn : forall Q X a,
                triple (Q [X \ a]) (CAss X a) Q
| rule_consequence_pre: forall (P P' Q : assertionG) c,
                          triple P' c Q ->
                          (*P ==> P' ->*)
                          triple P c Q
| rule_consequence_post: forall (P Q Q' : assertionG) c,
                          triple P c Q' ->
                          (*Q' ==> Q ->*)
                          triple P c Q
| rule_consequence: forall (P P' Q Q' : assertionG) c,
                      triple P' c Q' ->
                      (*P ==> P' ->
                      Q' ==> Q ->*)
                      triple P c Q
| rule_skip : forall P,
     triple P CSkip P

| rule_seq: forall P Q R c1 c2,
              triple Q c2 R ->
              triple P c1 Q ->
              triple P (CSeq c1 c2) R

| rule_if: forall P Q b c1 c2,
            triple (fun st => P st /\ bassn b st) c1 Q ->
            triple (fun st => P st /\ not (bassn b st)) c2 Q ->
            triple P (CIf b c1 c2) Q

| rule_while : forall P b c,
                triple (fun st => P st /\ bassn b st) c P ->
                triple P (CWhile b c) (fun st => P st /\ not (bassn b st))

| rule_cons: forall P X a,
              triple (fun st => forall loc, (((ANum loc) |-> a) --* P [X \ (ANum loc)]) st)
              (CCons X a) P

| rule_lookup: forall (P:assertionG) a x,
                  triple (fun st
                             =>(match st with
                                | (stoV,stoB,stoF,hV,hB) =>
                                    exists loc, ((aeval stoV stoF a) = loc) /\
                                    exists val, (hV loc) = Some val /\
                                    P ((st_updateV stoV x val),stoB,stoF,hV,hB)
                                end))
                         (CLookup x a) 
                         P

| rule_mutate : forall P a1 a2,
                  triple (fun st => 
                              (match st with
                              | (stoV,stoB,stoF,hV,hB) =>
                                exists loc, ((aeval stoV stoF a1) = loc) /\
                                exists val, (hV loc) = Some val /\
                                P (stoV,stoB,stoF,(h_updateV hV loc (aeval stoV stoF a2)),hB)
                              end))
                         (CMutat a1 a2)
                         P

| rule_dispose : forall P a,
        triple (fun st => (match st with
                           | (stoV,stoB,stoF,hV,hB) =>
                                exists loc, ((aeval stoV stoF a) = loc) /\
                                exists val, (hV loc) = Some val /\
                                P (stoV,stoB,
                                   stoF,(fun l => if (eq_nat_dec l loc) then None else hV l),hB)
                           end))
               (CDispose a)
               P

| rule_Fcreate : forall x bkli P,
      triple ([[P & empB]])
             (CFcreate x bkli)
             ([[P & (point_toF x (bkli_to_fe (reverse bkli)))]])

| rule_FcontentAppend : forall fid bkli P ffe,
      triple ([[P & point_toF fid ffe]])
             (CFcontentAppend fid bkli)
             ([[P & point_toF fid (Appfe ffe (bkli_to_fe (reverse bkli))) ]])

| rule_Fdelete : forall fid ffe P,
      triple ([[ P & point_toF fid ffe ]])
             (CFdelete fid)
             ([[ P & empB]])

| rule_Blookup : forall x tv bk bk1 P,
      triple ([[ P & (BKId x =b= tv) /@\ (point_toB bk bk1) ]])
             (CBlookup x bk)
             ([[ P & (BKId x =b= bk1) /@\ (point_toB bk bk1) ]])

| rule_Bmutate : forall bk1 bk2 P t,
      triple ([[ P &  point_toB bk1 t ]])
             (CBmutat bk1 bk2)
             ([[ P & point_toB bk1 bk2 ]])

| rule_Bdelete : forall bk t P,
      triple ([[ P & point_toB bk t ]])
             (CBdelete bk)
             ([[ P & empB ]]).

Notation "{{ P }} c {{ Q }}" :=
  (triple P c Q) (at level 90, c at next level).





