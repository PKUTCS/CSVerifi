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


Definition assertionB := state -> Prop.


Definition empB : assertionB :=
fun st:state => match st with
                | (stoV,stoB,stoF,hV,hB) => hB = emp_heapB
                end.


Definition point_toB (bk1 bk2:bkexp) : assertionB :=
  fun st:state =>
    match st with
    | (stoV,stoB,stoF,hV,hB) => 
        (match (bkeval stoV stoB stoF bk1),(bkeval stoV stoB stoF bk2) with
         | Some n1, Some n2 => hB = h_updateB emp_heapB n1 n2
         | _,_ => False
        end)
    end.

Notation "e1 '|=>' e2" := (point_toB e1 e2) (at level 60).


Inductive fe : Type :=
| Nil : fe
| Fi  : id -> fe
| Appbk : fe -> bkexp -> fe
| Appfe : fe -> fe -> fe.


Fixpoint feEval stoV stoB stoF feExp : option (list nat) :=
match feExp with
| Nil => Some []
| Fi fid => Some (stoF fid)
| Appbk afe abkexp => (match (feEval stoV stoB stoF afe) with
                      | Some li => (match (bkeval stoV stoB stoF abkexp) with
                                    | Some bk => Some (li ++ [bk])
                                    | None => None
                                    end)
                      | None => None
                      end)
| Appfe fe1 fe2 => (match (feEval stoV stoB stoF fe1),
                          (feEval stoV stoB stoF fe2) with
                    | Some fli1, Some fli2 => Some (fli1 ++ fli2)
                    | _,_ => None
                    end)
end.


Fixpoint allSame (li1 li2:list nat) : Prop :=
  match li1,li2 with
  | [],[] => True
  | x::xl, y::yl => (x = y) /\ (allSame xl yl)
  | _,_ => False
  end.


Definition point_toF (f:id) (feExp:fe) : assertionB :=
  fun st:state =>
    match st with
    | (stoV,stoB,stoF,hV,hB) => 
        let opfeli := (feEval stoV stoB stoF feExp) in
        let opfi := (stoF f) in 
        (match opfeli, opfi with
         | Some li1, li2 => allSame li1 li2
         | _,_ => False
         end)
    end.




Definition sep_conjB (p q : assertionB) : assertionB :=
    fun st: state =>
      match st with
      | (stoV,stoB,stoF,hV,hB) => 
        exists hb1, exists hb2,
          disjointB hb1 hb2 /\ h_unionB hb1 hb2 = hB /\ 
          p (stoV,stoB,stoF,hV,hb1) /\ q (stoV,stoB,stoF,hV,hb2)
      end.
Notation "p '@@' q" := (sep_conjB p q) (at level 70).



Definition sep_disjB (p q: assertionB) : assertionB :=
  fun (st : state) =>
    match st with
    | (stoV,stoB,stoF,hV,hB) => 
      forall hb', disjointB hb' hB -> p (stoV,stoB,stoF, hV, hb') -> 
      q (stoV,stoB,stoF,hV,h_unionB hB hb')
    end.
Notation "p '--@' q" := (sep_disjB p q) (at level 80).


Definition s_conjB (p q: assertionB) : assertionB :=
  fun (s: state) => p s /\ q s.
Notation "p '/@\' q" := (s_conjB p q) (at level 75).

Definition s_disjB (p q: assertionB) : assertionB :=
  fun (s: state) => p s \/ q s.
Notation "p '\@/' q" := (s_disjB p q) (at level 78).

Definition s_impB (p q: assertionB) : assertionB :=
  fun (s: state) => p s -> q s.
Notation "p '--->' q" := (s_impB p q) (at level 85).


Definition strongerThanB (p q: assertionB) : Prop :=
  forall s: state, s_impB p q s.
Notation "p '===>' q" := (strongerThanB p q) (at level 90).


Definition bk_eq (bk1 bk2:bkexp) : assertionB :=
  fun st:state =>
    match st with
    | (stoV,stoB,stoF,hV,hB) => 
        (match (bkeval stoV stoB stoF bk1),(bkeval stoV stoB stoF bk2) with
         | Some n1, Some n2 => n1 = n2
         | _,_ => False
        end)
    end.
Notation "e1 '=b=' e2" := (bk_eq e1 e2) (at level 60).



Definition bk_le (bk1 bk2:bkexp) : assertionB :=
  fun st:state =>
    match st with
    | (stoV,stoB,stoF,hV,hB) => 
        (match (bkeval stoV stoB stoF bk1),(bkeval stoV stoB stoF bk2) with
         | Some n1, Some n2 => n1 <= n2
         | _,_ => False
        end)
    end.
Notation "e1 '<b=' e2" := (bk_le e1 e2) (at level 60).















