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

| rule_Fcreate : forall x bkli,
      triple ()
             (CFcreate x bkli)
             ()
.

Notation "{{ P }} c {{ Q }}" :=
  (triple P c Q) (at level 90, c at next level).


Definition triple (P:assertionG) (c:command) (Q:assertionG) : Prop :=
  forall st opst, 
    P st ->
    c / st \\ opst ->
    match opst with
    | Abt => False
    | St st2 => Q st2
    end.





(* proof rules *)
(* assign *)
Theorem rule_asgn : forall Q X a,
  {{Q [X \ a]}} (CAss X a) {{Q}}.
Proof.
  intros.
  unfold triple.
  intros. unfold assn_sub in *.
  destruct st. repeat destruct p. destruct opst.
  -inversion H0. subst. assumption.
  -inversion H0.
Qed.



(* consquence *)
Theorem rule_consequence_pre : forall (P P' Q : assertionG) c,
  {{P'}} c {{Q}} ->
  P ==G> P' ->
  {{P}} c {{Q}}.
Proof.
  intros.
  unfold triple in *.
  unfold strongerThanG in *.
  intros.
  apply H0 in H1.
  apply H in H2.
  -apply H2. -apply H1.
Qed.


Theorem rule_consequence_post : forall (P Q Q' : assertionG) c,
  {{P}} c {{Q'}} ->
  Q' ==G> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold triple in *.
  unfold strongerThanG in *.
  intros. unfold s_impG in *.
  assert (c / st \\ opst /\ P st). -auto.
  -apply H with (opst:=opst) in H1.
   +destruct opst. 
    *apply H0. assumption.
    *inversion H1.
   +apply H2.
Qed.


Theorem rule_consequence : forall (P P' Q Q' : assertionG) c,
  {{P'}} c {{Q'}} ->
  P ==G> P' ->
  Q' ==G> Q ->
  {{P}} c {{Q}}.
Proof.
  intros.
  apply rule_consequence_pre with P'.
  -apply rule_consequence_post with Q'.
   +assumption.
   +assumption.
  -assumption.
Qed.




(* skip rule *)
Theorem rule_skip : forall P,
     {{P}} CSkip {{P}}.
Proof.
  unfold triple. intros.
  inversion H0. subst. assumption.
Qed.





(* Sequencing *)
Theorem rule_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} (CSeq c1 c2) {{R}}.
Proof.
  unfold triple.
  intros.
  inversion H2. subst.
  apply H0 in H5. apply H in H8.
  -assumption. -assumption. -assumption. 
  -subst. apply H0 in H7.
   +inversion H7. +apply H1.
Qed.





(* Conditionals *)
(*
      {{P ∧  b}} c1 {{Q}}
      {{P ∧ ~b}} c2 {{Q}}
------------------------------------
{{P}} IFB b THEN c1 ELSE c2 FI {{Q}}
*)
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


(* if rule is not soundness: bexp can abort! *)
Theorem rule_if : forall (P Q:assertionG) b c1 c2,
  (forall st, P st -> not ((bassn_Abt b) st)) ->
  {{fun st:state => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st:state => P st /\ not_bassn b st}} c2 {{Q}} ->
  {{P}} (CIf b c1 c2) {{Q}}.
Proof.
  unfold triple, bassn, not.
  intros. inversion H3. subst.
  -apply H0 in H10. assumption.
   +split. ++apply H2. ++apply H9.
  -subst. apply H1 in H10.
   +apply H10. 
   +split.
    ++apply H2.
    ++intros. simpl in *. assumption.
  -subst. apply H in H2.
    +inversion H2.
    +unfold bassn_Abt. assumption.
Qed.


(* loops *)
Theorem rule_while : forall (P:assertionG) b c,
  (forall st, P st -> not ((bassn_Abt b) st)) ->
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} (CWhile b c) {{fun st => P st /\ not (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (CWhile b c) as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst.
  - (* E_WhileEnd *)
    split. 
    +apply Hhoare in HP. unfold triple in *.
     inversion H0. subst.
     *
     unfold bassn_Abt in *.
  - (* E_WhileLoop *)
    apply IHHe2. reflexivity. unfold triple in *.
    apply (Hhoare (sto, h) (St st)). assumption.
    split. assumption. apply bexp_eval_true. assumption.
  - unfold triple in *.
    apply (Hhoare (sto, h) Abt).
    +assumption. +split. *assumption.
     *apply bexp_eval_true. simpl. assumption.
Qed.
