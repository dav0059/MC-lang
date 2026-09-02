Require Import Strings.String PeanoNat.
Require Import Lists.List. 
Import ListNotations. 

Record PRIM_DATA : Type := {
  BaseTp : Type;
  BaseVl : Type; 
  OP : Type; 
  base_tp_of_base_vl : BaseVl -> BaseTp;
  interp_op : OP -> list BaseVl -> option BaseVl; 
  eqb_BaseTp : BaseTp -> BaseTp -> bool; 
  eqb_BaseVl : BaseVl -> BaseVl -> bool; 
  eq_BaseTp_dec : forall (x y: BaseTp), {x = y} + {x <> y};
  eq_BaseVl_dec : forall (x y: BaseVl), {x = y} + {x <> y}; 
  eqb_eq_BaseTp : forall x y, Bool.reflect (x = y) (eqb_BaseTp x y); 
  eqb_eq_BaseVl : forall x y, Bool.reflect (x = y) (eqb_BaseVl x y)
} . 

(* 
Record BNS_DATA : Type := {
    prim     : PRIM_DATA;
    TBool    : prim.(BaseTp);  
    TNat     : prim.(BaseTp); 
    TString  : prim.(BaseTp);
    VBool    : bool -> prim.(BaseVl); 
    VNat     : nat -> prim.(BaseVl);
    VString  : string -> prim.(BaseVl);
    OpNot    : prim.(OP); 
    OpAnd    : prim.(OP);
    OpOr     : prim.(OP); 
    OpSum    : prim.(OP);
    OpSub    : prim.(OP);
    OpMul    : prim.(OP);
    OpConcat : prim.(OP); 
    OpEq     : prim.(OP);
    type_VBool : forall b, prim.(base_tp_of_base_vl) (VBool b) = TBool;
    type_VNat  : forall n, prim.(base_tp_of_base_vl) (VNat n) = TNat;
    type_VString : forall s, prim.(base_tp_of_base_vl) (VString s) = TString
}.
 *)

(* 
(* a concrete implementation of the minimal MC interface *)
Module PrimitiveData <: BNS_PRIMITIVE. 
    
    Inductive BaseTyp : Type := 
     |TpNat 
     |TpBool 
     |TpString . 

    Inductive BaseVal : Type := 
     |VlNat (n: nat)
     |VlBool (b: bool)
     |VlString (s: string)
     . 

    Inductive Op : Type := 
     |Not 
     |And 
     |Sum 
     |Mul 
     |Concat 
     |Eq . 

    Definition BaseTp  := BaseTyp. 
    Definition BaseVl  := BaseVal. 
    Definition OP      := Op.   
    Definition TBool   := TpBool. 
    Definition TNat    := TpNat. 
    Definition TString := TpString. 
    Definition VBool (b: bool) := VlBool b. 
    Definition VNat  (n: nat)  := VlNat n. 
    Definition VString (s: string) := VlString s. 
    Definition OpNot := Not. 
    Definition OpAnd := And. 
    Definition OpSum := Sum. 
    Definition OpMul := Mul. 
    Definition OpConcat := Concat. 
    Definition OpEq := Eq.           
      
    Definition base_tp_of_base_vl (v: BaseVl) : BaseTp := 
      match v with 
      |VlNat _ => TpNat 
      |VlBool _ => TpBool 
      |VlString _ => TpString 
      end.


    Definition interp_op (o: OP) (l: list BaseVl) : option BaseVl := 
      match o, l with
      |Not, [VlBool b1]            => Some (VlBool (negb b1))
      |And, [VlBool b1; VlBool b2] => Some (VlBool (andb b1 b2)) 
      |Sum, [VlNat x1; VlNat x2]   => Some (VlNat (x1 + x2))
      |Mul, [VlNat x1; VlNat x2]   => Some (VlNat (x1 * x2))
      |Concat, [VlString s1; VlString s2] => Some (VlString (String.append s1 s2))
      |Eq, [x1; x2] => match x1, x2 with 
                        |VlNat n1, VlNat n2 => Some (VlBool (Nat.eqb n1 n2))
                        |VlBool b1, VlBool b2 => Some (VlBool (Bool.eqb b1 b2)) 
                        |VlString s1, VlString s2 => Some (VlBool (eqb s1 s2))
                        |_, _        => None    
                        end
      |_, _          => None 
      end. 

    
    Lemma eq_BaseTp_dec : forall (x y: BaseTp), {x = y} + {x <> y} . 
    Proof. intros. destruct x, y; try eauto; right; discriminate. Qed.
       

    Lemma eq_BaseVl_dec : forall (x y: BaseVl), {x = y} + {x <> y}. 
    Proof. 
      intros. destruct x, y; 
      try (right; discriminate).  
      + destruct (Nat.eqb n n0) eqn: eq. 
        * rewrite Nat.eqb_eq in eq. 
          rewrite eq.
          left. eauto. 
        * rewrite Nat.eqb_neq in eq. 
          right. 
          unfold not; intro. 
          inversion H.
          contradiction. 
      + destruct (Bool.eqb b b0) eqn: eq. 
        * rewrite Bool.eqb_true_iff in eq. 
          rewrite eq. 
          left; eauto. 
        * rewrite Bool.eqb_false_iff in eq. 
          right. 
          unfold not; intro. 
          inversion H. 
          contradiction. 
      + destruct (eqb s s0) eqn: eq. 
        * rewrite eqb_eq in eq. 
          rewrite eq. 
          left; eauto. 
        * rewrite eqb_neq in eq. 
          right. 
          unfold not; intro. 
          inversion H. 
          contradiction. 
    Qed.   
          

     Lemma type_VBool : forall (b: bool), base_tp_of_base_vl (VBool b)  = TBool.
     Proof. intros. simpl. unfold TBool. eauto.
     Qed. 
     
     Lemma type_VNat : forall (n: nat), base_tp_of_base_vl (VNat n) = TNat. 
     Proof. intros. simpl. unfold TNat. eauto. 
     Qed. 

     Lemma type_VString: forall (s: string), base_tp_of_base_vl (VString s) = TString.
     Proof. intros. simpl. unfold TString. eauto.
     Qed.  

End PrimitiveData. *)