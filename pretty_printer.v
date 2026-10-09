Require Import ids primitives env values. 
Require Import Strings.String.
Open Scope string_scope. 

Set Implicit Arguments.
Set Contextual Implicit. 

Section PRINTER.
    
    Context (I :IDS).
    Context (P: PRIM_DATA). 

    Fixpoint val_to_string (v : Val I P) : string := 
      match v with 
      |VCls _ _ _ _             => "<fun>" 
      |VLit x                   => BaseVl_to_string P x  
      |VUnit                    => "()"
      |VNil                     => "[]"
      |VPair (v1, _) (VUnit, _) => val_to_string v1 
      |VPair (v1, _) (v2, _)    => val_to_string v1 ++ "," ++ val_to_string v2  
      |VCons v1 v2 _            => val_to_string v1 ++ "::" ++ val_to_string v2
      |VVariant c _ v           => constr_to_string I c ++ 
                                   "(" ++ val_to_string v ++ ")" 
      |VError m                 => "MC Error: " ++
                                   (message_to_string I m)  
      end.

End PRINTER.

