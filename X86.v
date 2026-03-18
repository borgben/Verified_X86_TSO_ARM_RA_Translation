From RelAcqProof Require Import Events. 
From RelAcqProof Require Import Executions. 
From hahn Require Import Hahn.

Inductive LabelX86 := 
| W_x86 (loc:Location) (val:Value)
| R_x86 (loc:Location) (val:Value). 

(* Instance LabelClassArm: LabelClass LabelArm.  *)
Instance LabelClassX86: LabelClass LabelX86 := {
    lab_loc l := match l with
                | W_x86 loc _ => loc 
                | R_x86 loc _ => loc 
                end;
      
    lab_val l := match l with
                | W_x86 _ val => val 
                | R_x86 _ val => val 
                end;

    is_r l := match l with
                | W_x86 _ _ => False  
                | R_x86 _ _ => True 
                end;

    is_w l := match l with
                | W_x86 _ _ => True  
                | R_x86 _ _ => False
                end;
}. 

(* atomic ops (in domain or codomain of rmw) act as a barrier between them and what happens before or after *)
Definition implid_x86 {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): relation Event :=
    let atomic := ⦗dom_rel (rmw exec)⦘ ∪ ⦗codom_rel (rmw exec)⦘ in
        ((po exec) ⨾ atomic) ∪ (atomic ⨾ (po exec)).

(* TSO enforces everything but W -> R to be ordered *)
(* is the last case even needed, considering we're esentially doing set difference? *)
Definition ppo_x86 {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): relation Event :=
    (po exec) \ (fun w r => is_w (event_label w) /\ is_r (event_label r)). 

(* happens before is defined by the union of several relations *)
Definition hb_x86 {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): relation Event :=
    ((ppo_x86 exec) ∪ (implid_x86 exec) ∪ (external rf exec) ∪ (fr exec) ∪ (mo exec))⁺. 

(* x86 Axiom: the transitive closure of happens before must be irreflexive (cycles cause it to be reflexive) *)
Definition ordered_before_axiom_x86 {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): Prop :=
    irreflexive (hb_x86 exec).  

Definition x86_consistent  {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): Prop := 
    well_formed exec /\ atomicity_axiom exec /\ coherence_axiom exec /\ ordered_before_axiom_x86 exec.