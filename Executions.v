From hahn Require Import Hahn.
From RelAcqProof Require Import Label. 
From RelAcqProof Require Import Events.  
Set Implicit Arguments.

Record Execution {Label : Type} `{LabelProof: LabelClass Label} := {
    (* Set of Events in the Execution Graph *)
    events: Event -> Prop; 

    (* The primitive relations *)
    (* po - relation over events in the same thread.*)
    po: relation Event;

    (* rf -  "reads from" write events read from read events.*)
    rf: relation Event;

    (* co - "coherence order" relates writes to the same location. *)
    mo: relation Event;

    (* Derived Relation*)
    rmw: relation Event; 
}. 
 
(* Internal Relation *)
(* We are stating that an internal relation (intra-thread) formally means that 
   Given some binary relation R over the given Execution, the internal version of said relation 
   consists of elements in R which are also elements of program order (po). *)
Definition internal {Label : Type} {LabelProof : LabelClass Label}
           (R : Execution -> Event  -> Event -> Prop) (exec : Execution): relation Event :=
        fun e1 e2 =>
            R exec e1 e2 /\ same_thread e1 e2.

(* External Relation *)
(* Literally the opposite of internal. *)
Definition external {Label : Type} {LabelProof : LabelClass Label} 
            (R : Execution  -> Event -> Event -> Prop) (exec : Execution): relation Event :=
        fun e1 e2 => 
            R exec e1 e2 /\ ~(same_thread e1 e2). 


(* From Read Relation *)
Definition fr {Label : Type} {LabelProof : LabelClass Label} (exec : Execution): relation Event  := (((rf exec)⁻¹)  ⨾  (mo exec)).  

(* PoLoc *)
Definition poloc {Label: Type} {LabelProof: LabelClass Label} (exec:Execution) : relation Event  := 
    fun e1 e2 => (same_loc e1 e2) /\ ((po exec) e1 e2).  

(* PoImm *)
Definition poimm {Label: Type} {LabelProof: LabelClass Label} (exec:Execution) : relation Event  := 
    fun e1 e2 =>  ((po exec) e1 e2) /\ ~(exists e3, ((po exec) e1 e3) /\ ((po exec) e3 e2)).


Definition well_formed_mo {Label: Type} {LabelProof: LabelClass Label} (exec:Execution) :Prop := 
    forall (e1 e2:Event), (mo exec) e1 e2 -> both_write e1 e2 /\ same_loc e1 e2. 

Definition well_formed_rf {Label: Type} {LabelProof: LabelClass Label} (exec:Execution) :Prop := 
    forall (w r:Event), (rf exec) w r -> is_w (event_label w) /\ is_r (event_label r)
                                         /\ same_loc w r 
                                         /\ same_val w r 
                                         /\ forall (w0:Event), is_w (event_label w0) -> (rf exec) w0 r -> w0 = w.   

Definition well_formed_rmw {Label: Type} {LabelProof: LabelClass Label} (exec:Execution) :Prop := 
    forall (r w:Event), (rmw exec) r w -> is_r (event_label r) /\ is_w (event_label w)
                                          /\ (poimm exec) r w
                                          /\ same_loc r w. 

Definition well_formed {Label: Type} {LabelProof: LabelClass Label} (exec:Execution) :Prop := 
    well_formed_mo exec /\ well_formed_rf exec /\ well_formed_rmw exec. 
