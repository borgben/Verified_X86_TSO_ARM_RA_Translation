Definition Location := nat.
Definition Value := nat.

Class LabelClass (L : Type):Type := {
  lab_loc : L -> option Location;
  lab_val : L -> option Value; 
  is_r : L -> Prop;
  is_w : L -> Prop;
}. 