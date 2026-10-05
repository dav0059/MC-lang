Require Import Strings.String.
Require Import Lists.List. 

Record PRIM_DATA : Type := {
  BaseTp : Type;
  BaseVl : Type; 
  OP : Type; 
  base_tp_of_base_vl : BaseVl -> BaseTp;
  interp_op : OP -> list BaseVl -> option BaseVl; 
  eqb_BaseTp : BaseTp -> BaseTp -> bool; 
  eqb_BaseVl : BaseVl -> BaseVl -> bool; 
  BaseVl_to_string : BaseVl -> string;
  eq_BaseTp_dec : forall (x y: BaseTp), {x = y} + {x <> y};
  eq_BaseVl_dec : forall (x y: BaseVl), {x = y} + {x <> y}; 
  eqb_eq_BaseTp : forall x y, Bool.reflect (x = y) (eqb_BaseTp x y); 
  eqb_eq_BaseVl : forall x y, Bool.reflect (x = y) (eqb_BaseVl x y)
} . 

