Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import language.
Require Import state.
Require Import util.
Import ListNotations.

Fixpoint aeval (stoV: storeV) (stoF: storeF) (a:aexp) : nat :=
match a with
| ANum n => n
| AId name => (stoV name)
| APlus a1 a2 => (aeval stoV stoF a1) + (aeval stoV stoF a2)
| AMult a1 a2 => (aeval stoV stoF a1) * (aeval stoV stoF a2)
| AMinus a1 a2 => (aeval stoV stoF a1) - (aeval stoV stoF a2)
| AFsize fname => length (stoF fname)
end.


Fixpoint findbk (li:list nat) (loc:nat): option nat :=
match li with
| [] => None
| x::xli => if (beq_nat loc 1) then Some x else (findbk xli (loc-1))
end.



Fixpoint bkeval (stoV:storeV) (stoB:storeB) 
                (stoF:storeF) (bk:bkexp) : option nat :=
match bk with
| BKNum n => Some n
| BKId name => Some (stoB name)
| BKAddr fname a => findbk (stoF fname) (aeval stoV stoF a)
end.


Fixpoint beval stoV stoB stoF (b:bexp) : bool :=
match b with
| BTrue => true
| BFalse => false
| BEq a1 a2 => beq_nat (aeval stoV stoF a1) (aeval stoV stoF a2)
| BLe a1 a2 => leb (aeval stoV stoF a1) (aeval stoV stoF a2)
| BNot b1 => negb (beval stov stoB stoF b1)
| BAnd b1 b2 => andb (beval stov stoB stoF b1) (beval stov stoB stoF b2)
| BOr  b1 b2 => orb (beval stov stoB stoF b1) (beval stov stoB stoF b2)
| BKeq bk1 bk2 => beq_nat () ()
| BKle bk1 bk2 => leb () ()
end.



Inductive big_step: command -> state -> ext_state -> Prop :=
| E_Skip  : forall stat,
              big_step CSkip stat (St stat)
| E_Ass   : forall stoV stoB stoF hV hB x a n, (aeval stoV stoF a) = n ->
              big_step (CAss x a) (stoV,stoB,stoF,hV,hB) 
                       (St ((st_updateV stoV x n),stoB,stoF,hV,hB))
| E_Seq   : forall c1 c2 st0 st1 opst,
              big_step c1 st0 (St st1) ->
              big_step c2 st1 opst ->
              big_step (CSeq c1 c2) st0 opst
| E_Seq_Ab: forall c1 c2 st0,
              big_step c1 st0 Abt ->
              big_step (CSeq c1 c2) st0 Abt

/////
| E_IfTure: forall sto h opst b c1 c2,
              beval sto b = true ->
              big_step c1 (sto,h) opst ->
              big_step (CIf b c1 c2) (sto,h) opst
| E_IfFalse:forall b sto c1 c2 h opst,
              beval sto b = false ->
              big_step c2 (sto,h) opst ->
              big_step (CIf b c1 c2) (sto,h) opst
| E_WhileEnd : forall b sto h c,
                 beval sto b = false ->
                 big_step (CWhile b c) (sto, h) (St (sto, h))
| E_WhileLoop : forall sto h opst b c st,
                  beval sto b = true ->
                  big_step c (sto, h) (St st) ->
                  big_step (CWhile b c) st opst ->
                  big_step (CWhile b c) (sto, h) opst
| E_WhileLoop_Ab : forall sto h b c,
                  beval sto b = true ->
                  big_step c (sto, h) Abt ->
                  big_step (CWhile b c) (sto, h) Abt
| E_Cons : forall sto h a n x l,
              aeval sto a = n ->
              h l = None ->
              big_step (CCons x a) (sto, h)
                       (St (st_update sto x l,
                            h_update h l n))
| E_Lookup : forall sto h x a1 n1 n2,
                aeval sto a1 = n1 ->
                h n1 = Some n2 ->
                big_step (CLookup x a1) (sto, h) (St (st_update sto x n2, h))
| E_Lookup_Ab : forall sto a1 n1 h x,
                   aeval sto a1 = n1 ->
                   h n1 = None ->
                   big_step (CLookup x a1) (sto, h) Abt
| E_Mutat : forall sto h a1 a2 n1 n2,
                  aeval sto a1 = n1 ->
                  aeval sto a2 = n2 ->
                  in_dom n1 h ->
                  big_step (CMutat a1 a2) (sto, h) (St (sto, h_update h n1 n2))
| E_Mutat_Ab : forall sto h a1 a2 n1,
                     aeval sto a1 = n1 ->
                     h n1 = None ->
                     big_step (CMutat a1 a2) (sto, h) Abt
| E_Dispose : forall sto h a1 n1,
                 aeval sto a1 = n1 ->
                 in_dom n1 h ->
                 big_step
                   (CDispose a1) (sto, h)
                   (St (sto, fun x => if eq_nat_dec x n1 then None else h x))
| E_Dispose_Ab : forall sto h a1 n1,
                    aeval sto a1 = n1 ->
                    h n1 = None ->
                    big_step (CDispose a1) (sto, h) Abt.

Notation "c1 '/' st '\\' opst" := (big_step c1 st opst) 
                                  (at level 40, st at level 39).



