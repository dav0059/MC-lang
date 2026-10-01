Require Import Strings.String.

Record IDS : Type := { 
  Ide : Type ; 
  Constr : Type; 
  Message : Type; 
  id_eqb : Ide -> Ide -> bool; 
  constr_eqb : Constr -> Constr -> bool; 
  message_eqb : Message -> Message -> bool; 
  id_eqb_eq : forall x y, x = y <-> id_eqb x y = true; 
  id_eqb_neq : forall x y, x <> y <-> id_eqb x y = false; 
  constr_eqb_eq: forall x y, x = y <-> constr_eqb x y = true; 
  constr_eqb_neq: forall x y, x <> y <-> constr_eqb x y = false;  
  message_eqb_eq: forall x y, x = y <-> message_eqb x y = true;
  message_eqb_neq: forall x y, x <> y <-> message_eqb x y = false; 
  id_eq_dec: forall (x y: Ide), {x = y} + {x <> y};
  constr_eq_dec: forall (x y: Constr), {x = y} + {x <> y};   
  message_eq_dec: forall (x y: Message), {x = y} + {x <> y}; 
  ids_refl : forall x y, Bool.reflect (x = y) (id_eqb x y); 
  constr_refl : forall x y , Bool.reflect (x = y) (constr_eqb x y);  
  id_to_string : Ide -> string; 
  constr_to_string : Constr -> string; 
  message_to_string : Message -> string
}.

