From RelAcqProof Require Import Events. 
From RelAcqProof Require Import Executions. 
From hahn Require Import Hahn.

Inductive LabelArm := 
| W_Rel (loc:Location) (val:Value)
| R_Acq_Pc (loc:Location) (val:Value). 

(* Instance LabelClassArm: LabelClass LabelArm.  *)
Instance LabelClassArm: LabelClass LabelArm := {
    lab_loc l := match l with
                | W_Rel loc _ => loc 
                | R_Acq_Pc loc _ => loc 
                end;
      
    lab_val l := match l with
                | W_Rel _ val => val 
                | R_Acq_Pc _ val => val 
                end;

    is_r l := match l with
                | W_Rel _ _ => False 
                | R_Acq_Pc _ _ => True 
                end;

    is_w l := match l with
                | W_Rel _ _ => True 
                | R_Acq_Pc _ _ => False 
                end;
}. 


(* ARM axiom *)
(* bob = ((R_acq_pc ; po) ∪ (po ; W_rel)) *)
Definition bob_arm {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): relation Event :=
    let R := ⦗fun r => is_r (event_label r)⦘ in 
    let W := ⦗fun w => is_w (event_label w)⦘ in
    (R ⨾ (po exec)) ∪ ((po exec) ⨾ W).

(* ob = (bob ∪ rfe ∪ moe ∪ fre)+ *)
Definition ordered_before_axiom_arm {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): Prop :=
    irreflexive (((bob_arm exec) ∪ (external rf exec) ∪ (external mo exec) ∪ (external fr exec))⁺).
    

Definition arm_consistent  {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): Prop := 
    well_formed exec /\ atomicity_axiom exec /\ coherence_axiom exec /\ ordered_before_axiom_arm exec. 