Require Import CSSsVerification.
Import ListNotations.


Definition i  : id := Id "i".
Definition f1 : id := Id "f1".
Definition f2 : id := Id "f2".
Definition f3 : id := Id "f3".
Definition f4 : id := Id "f4".
Definition f5 : id := Id "f5".
Definition f6 : id := Id "f6".
Definition f7 : id := Id "f7".
Definition bc : id := Id "bc".
Definition bk : id := Id "bk".
Definition tv : id := Id "tv".


Definition Append :=
  i ::= (ANum 1);;
  WHILE (BLe (AId i) (AFsize f1)) DO
    CBlookup bc (BKAddr f1 (AId i));;
    CFcontentAppend f2 [(BKId bc)];;
    i ::= (APlus (AId i) (ANum 1))
  END.



Example append_correct :
  {{ [[ (eqV (AFsize f3) (AFsize f1)) & 
        (point_toF f1 (Fi f3)) @@ (point_toF f2 (Fi f4)) ]] 
  }}

  Append

  {{ [[ (eqV (AFsize f3) (AFsize f1)) & 
        (point_toF f1 (Fi f3)) @@ (point_toF f2 (Appfe (Fi f4) (Fi f3))) ]] 
  }}.
Proof.
  unfold Append.
  apply rule_seq with 
    (Q:= [[ (eqV (AId i) (APlus (AFsize f1) (ANum 1))) //\\ 
            (eqV (AFsize f5) (AMinus (AId i) (ANum 1))) //\\ 
            (eqV (AFsize f6) (APlus (AMinus (AFsize f1) (AId i)) (ANum 1)))
          & point_toF f1 (Appfe (Fi f5) (Fi f6)) @@ 
            point_toF f2 (Appfe (Fi f4) (Fi f5)) ]]).
  -apply rule_consequence_post with
        (Q':= (fun st => (([[ (eqV (AFsize f5) (AMinus (AId i) (ANum 1))) //\\ 
                            (eqV (AFsize f6) (APlus (AMinus (AFsize f1) (AId i)) (ANum 1)))
                          & point_toF f1 (Appfe (Fi f5) (Fi f6)) @@ 
                            point_toF f2 (Appfe (Fi f4) (Fi f5)) ]]) st)
                         /\ not (bassn (BLe (AId i) (AFsize f1)) st))).
   eapply rule_consequence_pre.
   apply rule_while.
   apply rule_seq with
      (Q:= [[ (leV (AId i) (AFsize f1)) //\\ 
              (eqV (AFsize f5) (AMinus (AId i) (ANum 1))) //\\ 
              (eqV (AFsize f7) (AMinus (AFsize f1) (AId i)))
            & point_toF f1 (Appfe (Appbk (Fi f5) (BKId bk)) (Fi f7)) @@ 
              point_toF f2 (Appfe (Fi f4) (Fi f5)) /@\ 
              (bk_eq (BKId bc) (BKId bk)) ]]).
   +apply rule_seq with
      (Q:= [[ (leV (AId i) (AFsize f1)) //\\ (eqV (AFsize f5) (AId i)) //\\ 
              (eqV (AFsize f6) (AMinus (AFsize f1) (AId i)))
              & point_toF f1 (Appfe (Fi f5) (Fi f6)) @@ 
                point_toF f2 (Appfe (Fi f4) (Fi f5)) ]]).
    *eapply rule_consequence_pre.
     apply rule_asgn.
    *eapply rule_consequence_pre.
     apply rule_consequence_post with
        (Q':= [[  (leV (AId i) (AFsize f1)) //\\ 
                  (eqV (AFsize f5) (AMinus (AId i) (ANum 1))) //\\ 
                  (eqV (AFsize f7) (AMinus (AFsize f1) (AId i)))
               &  point_toF f2 (Appbk (Appfe (Fi f4) (Fi f5)) (BKId bc))
              ]]).
     apply rule_FcontentAppendBk.
     ++unfold not_appear. auto.
   +apply rule_consequence_post with
        (Q':= [[  (leV (AId i) (AFsize f1)) //\\ 
                  (eqV (AFsize f5) (AMinus (AId i) (ANum 1))) //\\ 
                  (eqV (AFsize f7) (AMinus (AFsize f1) (AId i)))
               &  (BKId bc =b= (BKId bk)) /@\ 
                  (point_toB (BKAddr f1 (AId i)) (bk_sub bc (BKId tv) (BKId bk)))
              ]]).
    eapply rule_consequence_pre.
    apply rule_Blookup.
  -apply rule_consequence_post with
        (Q':= [[  (leV (AId i) (APlus (AFsize f1) (ANum 1))) //\\ 
                  (eqV (AFsize f5) (AMinus (AId i) (ANum 1))) //\\ 
                  (eqV (AFsize f6) (APlus (AMinus (AFsize f1) (AId i)) (ANum 1)))
              & point_toF f1 (Appfe (Fi f5) (Fi f6)) @@ 
                point_toF f2 (Appfe (Fi f4) (Fi f5)) ]]).
   eapply rule_consequence_pre.
   apply rule_asgn.
Qed.




