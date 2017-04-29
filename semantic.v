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


Fixpoint beval stoV stoB stoF (b:bexp) : option bool :=
match b with
| BTrue   => Some true
| BFalse  => Some false
| BEq a1 a2 => Some (beq_nat (aeval stoV stoF a1) (aeval stoV stoF a2))
| BLe a1 a2 => Some (leb (aeval stoV stoF a1) (aeval stoV stoF a2))
| BNot b1   =>(match (beval stoV stoB stoF b1) with
               | None => None
               | Some x => Some (negb x)
               end)
| BAnd b1 b2  =>(match (beval stoV stoB stoF b1), (beval stoV stoB stoF b2) with
                 | None,_ => None
                 | _,None => None
                 | Some x1,Some x2 => Some (andb x1 x2)
                 end)
| BOr  b1 b2  =>(match (beval stoV stoB stoF b1), (beval stoV stoB stoF b2) with
                 | None,_ => None
                 | _,None => None
                 | Some x1, Some x2 => Some (orb x1 x2)
                 end)
| BKeq bk1 bk2  =>(match (bkeval stoV stoB stoF bk1),
                         (bkeval stoV stoB stoF bk2) 
                   with
                   | None,_ => None
                   | _,None => None
                   | Some a1, Some a2 => (Some (beq_nat a1 a2))
                   end)
| BKle bk1 bk2  => (match (bkeval stoV stoB stoF bk1),
                          (bkeval stoV stoB stoF bk2) 
                   with
                   | None,_ => None
                   | _,None => None
                   | Some a1, Some a2 => (Some (leb a1 a2))
                   end)
end.


(* auxiliary function *)
Definition beq_op_nat x y : bool :=
match x,y with
| None,None => true
| Some n1,Some n2 => beq_nat n1 n2
| _,_ => false
end.

Fixpoint in_list (li:list (option nat)) (x:option nat) : bool :=
match li with
| [] => false
| t::xli => if beq_op_nat t x then true else in_list xli x
end.

Definition get_content (nli:list (option nat)) : list nat :=
let f := fun t => match t with
                 | Some n => n
                 | None => 0
                 end
in (map f nli).

Fixpoint all_none (opli:list (option nat)) : bool :=
match opli with
| [] => true
| x::li => if beq_op_nat x None then all_none li
           else false
end.

Fixpoint h_unionB_many hB locli nli : heapB :=
match locli,nli with
| loc::locs,n::ns => h_unionB_many (h_updateB hB loc n) locs ns
| [],[] => hB
| _,_ => hB
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
| E_IfTure: forall stoV stoB stoF hV hB opst b c1 c2,
              beval stoV stoB stoF b = Some true ->
              big_step c1 (stoV,stoB,stoF,hV,hB) opst ->
              big_step (CIf b c1 c2) (stoV,stoB,stoF,hV,hB) opst
| E_IfFalse: forall stoV stoB stoF hV hB opst b c1 c2,
              beval stoV stoB stoF b = Some false ->
              big_step c2 (stoV,stoB,stoF,hV,hB) opst ->
              big_step (CIf b c1 c2) (stoV,stoB,stoF,hV,hB) opst
| E_If_Ab : forall stoV stoB stoF hV hB b c1 c2,
              beval stoV stoB stoF b = None ->
              big_step (CIf b c1 c2) (stoV,stoB,stoF,hV,hB) Abt


| E_WhileEnd : forall b stoV stoB stoF hV hB c,
                 beval stoV stoB stoF b = Some false ->
                 big_step (CWhile b c) (stoV,stoB,stoF,hV,hB) (St (stoV,stoB,stoF,hV,hB))

| E_WhileLoop : forall stoV stoB stoF hV hB opst b c st,
                  beval stoV stoB stoF b = Some true ->
                  big_step c (stoV,stoB,stoF,hV,hB) (St st) ->
                  big_step (CWhile b c) st opst ->
                  big_step (CWhile b c) (stoV,stoB,stoF,hV,hB) opst
| E_WhileLoop_Ab : forall stoV stoB stoF hV hB b c,
                  beval stoV stoB stoF b = Some true ->
                  big_step c (stoV,stoB,stoF,hV,hB) Abt ->
                  big_step (CWhile b c) (stoV,stoB,stoF,hV,hB) Abt
| E_While_Ab :  forall stoV stoB stoF hV hB b c,
                  beval stoV stoB stoF b = None ->
                  big_step (CWhile b c) (stoV,stoB,stoF,hV,hB) Abt

| E_Cons : forall stoV stoB stoF hV hB a n x l,
              aeval stoV stoF a = n ->
              hV l = None ->
              big_step (CCons x a) (stoV,stoB,stoF,hV,hB)
                       (St ((st_updateV stoV x l),stoB,stoF,
                            (h_updateV hV l n), hB))

| E_Lookup : forall stoV stoB stoF hV hB x a1 l n,
                aeval stoV stoF a1 = l ->
                hV l = Some n ->
                big_step (CLookup x a1) (stoV,stoB,stoF,hV,hB) 
                         (St ((st_updateV stoV x n),stoB,stoF,hV,hB))

| E_Lookup_Ab : forall stoV stoB stoF hV hB x a1 l,
                   aeval stoV stoF a1 = l ->
                   hV l = None ->
                   big_step (CLookup x a1) (stoV,stoB,stoF,hV,hB) Abt

| E_Mutat : forall stoV stoB stoF hV hB a1 a2 n1 n2,
                  aeval stoV stoF a1 = n1 ->
                  aeval stoV stoF a2 = n2 ->
                  in_domV n1 hV ->
                  big_step (CMutat a1 a2) (stoV,stoB,stoF,hV,hB) 
                           (St (stoV,stoB,stoF,(h_updateV hV n1 n2),hB))

| E_Mutat_Ab : forall stoV stoB stoF hV hB a1 a2 n1,
                     aeval stoV stoF a1 = n1 ->
                     hV n1 = None ->
                     big_step (CMutat a1 a2) (stoV,stoB,stoF,hV,hB) Abt

| E_Dispose : forall stoV stoB stoF hV hB a1 n1,
                 aeval stoV stoF a1 = n1 ->
                 in_domV n1 hV ->
                 big_step
                   (CDispose a1) (stoV,stoB,stoF,hV,hB)
                   (St (stoV,stoB,stoF,(h_removeV hV n1),hB))

| E_Dispose_Ab : forall stoV stoB stoF hV hB a1 n1,
                    aeval stoV stoF a1 = n1 ->
                    hV n1 = None ->
                    big_step (CDispose a1) (stoV,stoB,stoF,hV,hB) Abt

| E_Fcreate : forall stoV stoB stoF hV hB f bkli nli nlist locli xli,
                 nli = map (bkeval stoV stoB stoF) bkli ->
                 in_list nli None = false ->
                 get_content nli = nlist ->
                 length locli = length nli ->
                 map hB locli = xli ->
                 all_none xli = true ->
                 big_step (CFcreate f bkli) (stoV,stoB,stoF,hV,hB)
                          (St (stoV,stoB,(st_updateF stoF f locli),hV,
                              (h_unionB_many hB locli nlist)))
| E_Fcreate_Abt : forall stoV stoB stoF hV hB f bkli nli,
                    nli = map (bkeval stoV stoB stoF) bkli ->
                    in_list nli None = true ->
                    big_step (CFcreate f bkli) (stoV,stoB,stoF,hV,hB) Abt

| E_FcontentAppend : forall stoV stoB stoF hV hB f bkli nli nlist ff xli locli,
                        nli = map (bkeval stoV stoB stoF) bkli ->
                        in_list nli None = false ->
                        get_content nli = nlist ->
                        length locli = length nli ->
                        map hB locli = xli ->
                        all_none xli = true ->
                        ff = stoF f ->
                        big_step (CFcontentAppend f bkli) (stoV,stoB,stoF,hV,hB)
                                 (St (stoV,stoB,
                                     (st_updateF stoF f (ff ++ locli)),hV,
                                     (h_unionB_many hB locli nlist)))

| E_FcontentAppend_Abt : forall stoV stoB stoF hV hB f bkli nli,
                          nli = map (bkeval stoV stoB stoF) bkli ->
                          in_list nli None = true ->
                          big_step (CFcontentAppend f bkli) 
                                   (stoV,stoB,stoF,hV,hB) Abt

| E_FaddressAppend : forall stoV stoB stoF hV hB f1 f2 bkli nli nlist ff2,
                        nli = map (bkeval stoV stoB stoF) bkli ->
                        in_list nli None = false ->
                        get_content nli = nlist ->
                        ff2 = stoF f2 ->
                        big_step (CFaddressAppend f1 f2 bkli) (stoV,stoB,stoF,hV,hB)
                                 (St (stoV,stoB,
                                     (st_updateF stoF f1 (ff2 ++ nlist)),hV,hB))

| E_FaddressAppend_Abt : forall stoV stoB stoF hV hB f1 f2 bkli nli,
                          nli = map (bkeval stoV stoB stoF) bkli ->
                          in_list nli None = true ->
                          big_step (CFaddressAppend f1 f2 bkli) 
                                   (stoV,stoB,stoF,hV,hB) Abt

| E_Fdelete : forall stoV stoB stoF hV hB f,
                big_step (CFdelete f) (stoV,stoB,stoF,hV,hB)
                         (St (stoV,stoB,stoF,hV,hB))

| E_Blookup : forall stoV stoB stoF hV hB b bk n v,
                (bkeval stoV stoB stoF bk) = Some n->
                hB n = Some v ->
                big_step (CBlookup b bk) (stoV,stoB,stoF,hV,hB)
                         (St (stoV,(st_updateB stoB b v),stoF,hV,hB))

| E_Blookup_AbtBK : forall stoV stoB stoF hV hB b bk,
                      (bkeval stoV stoB stoF bk) = None ->
                      big_step (CBlookup b bk) (stoV,stoB,stoF,hV,hB) Abt

| E_Blookup_AbtHp : forall stoV stoB stoF hV hB b bk n,
                      (bkeval stoV stoB stoF bk) = Some n ->
                      hB n = None ->
                      big_step (CBlookup b bk) (stoV,stoB,stoF,hV,hB) Abt

| E_Bass : forall stoV stoB stoF hV hB b bk n,
              (bkeval stoV stoB stoF bk) = Some n ->
              big_step (CBlookup b bk) (stoV,stoB,stoF,hV,hB)
                       (St (stoV,(st_updateB stoB b n),stoF,hV,hB))

| E_Bass_Abt : forall stoV stoB stoF hV hB b bk,
                (bkeval stoV stoB stoF bk) = None ->
                big_step (CBlookup b bk) (stoV,stoB,stoF,hV,hB) Abt

| E_Bmutat : forall stoV stoB stoF hV hB bk1 bk2 n1 n2,
                (bkeval stoV stoB stoF bk1) = Some n1 ->
                (bkeval stoV stoB stoF bk2) = Some n2 ->
                big_step (CBmutat bk1 bk2) (stoV,stoB,stoF,hV,hB)
                         (St (stoV,stoB,stoF,hV,(h_updateB hB n1 n2)))

| E_Bmutat_AbtBk1 : forall stoV stoB stoF hV hB bk1 bk2,
                      (bkeval stoV stoB stoF bk1) = None ->
                      big_step (CBmutat bk1 bk2) (stoV,stoB,stoF,hV,hB) Abt

| E_Bmutat_AbtBk2 : forall stoV stoB stoF hV hB bk1 bk2 n1,
                      (bkeval stoV stoB stoF bk1) = Some n1 ->
                      (bkeval stoV stoB stoF bk2) = None ->
                      big_step (CBmutat bk1 bk2) (stoV,stoB,stoF,hV,hB) Abt

| E_Bdelete : forall stoV stoB stoF hV hB bk,
                big_step (CBdelete bk) (stoV,stoB,stoF,hV,hB)
                         (St (stoV,stoB,stoF,hV,hB)).

Notation "c1 '/' st '\\' opst" := (big_step c1 st opst) 
                                  (at level 40, st at level 39).



