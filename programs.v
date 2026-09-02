Require Import result_type ids primitives env values surface_syntax kernel_syntax desugarer elaboration evaluation. 
Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope string_scope. 

Set Implicit Arguments. 
Set Contextual Implicit.

Definition ide := string. 
Definition cnstrct := string. 
Definition mssg := string. 


Definition ide_eqb := String.eqb. 
Definition cnstrct_eqb := String.eqb.
Definition mssg_eqb := String.eqb.

Lemma ide_eqb_eq: forall x y, 
  x = y <-> ide_eqb x y = true .
Proof. 
  symmetry; apply eqb_eq.
Qed.

Lemma ide_eqb_neq: forall x y, 
  x <> y <-> ide_eqb x y = false.
Proof. 
  symmetry; apply eqb_neq.
Qed. 

Lemma cnstrct_eqb_eq: forall x y, 
  x = y <-> cnstrct_eqb x y = true .
Proof. 
  intros. apply ide_eqb_eq.
Qed. 

Lemma cnstrct_eqb_neq: forall x y, 
  x <> y <-> cnstrct_eqb x y = false. 
Proof. 
  intros. apply (ide_eqb_neq). 
Qed. 

Lemma mssg_eqb_eq: forall x y, 
  x = y <-> mssg_eqb x y = true . 
Proof.
  intros. apply ide_eqb_eq. 
Qed. 

Lemma mssg_eqb_neq: forall x y, 
  x <> y <-> mssg_eqb x y = false.
Proof. 
  intros; apply ide_eqb_neq. 
Qed.   

Corollary ide_eq_dec: forall (x y: ide), {x = y} + {x <> y}. 
Proof. 
  intros.
  apply Bool.reflect_dec with (ide_eqb x y). 
  apply Bool.iff_reflect. 
  apply ide_eqb_eq.
Qed. 
  
Corollary cnstrct_eq_dec : forall (x y: cnstrct), {x = y} + {x <> y}. 
Proof. 
  intros; apply ide_eq_dec. 
Qed. 

Corollary mssg_eq_dec: forall (x y: mssg), {x = y} + {x <> y}. 
Proof. 
  intros; apply ide_eq_dec. 
Qed. 

Corollary ide_refl : forall (x y: ide), Bool.reflect (x = y) (ide_eqb x y).
Proof. 
  intros. apply Bool.iff_reflect. apply ide_eqb_eq.
Qed.

Corollary cnstr_refl : forall (x y: cnstrct), Bool.reflect (x = y) (cnstrct_eqb x y). 
Proof. 
  intros. apply ide_refl.
Qed. 



Definition ids_string : IDS := {|
    Ide := ide; 
    Constr := cnstrct; 
    Message := mssg; 
    id_eqb := ide_eqb; 
    constr_eqb := cnstrct_eqb;
    message_eqb := mssg_eqb; 
    id_eqb_eq := @ide_eqb_eq; 
    constr_eqb_eq := @cnstrct_eqb_eq; 
    message_eqb_eq := @mssg_eqb_eq; 
    id_eqb_neq := @ide_eqb_neq; 
    constr_eqb_neq := @cnstrct_eqb_neq; 
    message_eqb_neq := @mssg_eqb_neq; 
    id_eq_dec := @ide_eq_dec; 
    constr_eq_dec := @cnstrct_eq_dec; 
    message_eq_dec := @mssg_eq_dec; 
    ids_refl := @ide_refl ;
    constr_refl := @cnstr_refl;
    id_to_string := @id ide; 
    constr_to_string := @id cnstrct;
    message_to_string := @id mssg 
|}  .

      
    
Section MC_lang. 
    
    Let I := ids_string. 
    Let P := bns_data.
    
    Local Notation "'$p' s " := (@PVar I s) (at level 90).
    Local Notation "'0p' "  := (@PNat I 0) (at level 90). 
    Local Notation " n 'p+.1'" := (@PNat I (n + 1)) (at level 90, right associativity).
    Local Notation "'pT' " := (@PBool I true) (at level 90, right associativity).
    Local Notation "'pF' " := (@PBool I false) (at level 90, right associativity).
    Local Notation "'#p' s" := (@PString I s) (at level 90, right associativity).
    Local Notation "p 'As' x" := (@PAs I p x) (at level 91, left associativity). 
    Local Notation "'_ "  := (@PAny I) (at level 90, right associativity).
    Local Notation " 'pTup(' l ')' " := (@PTup I l) (at level 90, right associativity).
    Local Notation " 'pCons(' l ')' " := (@PCons I l) (at level 90, right associativity).
    Local Notation " 'pC(' c ',' l ')' " := (@PVariant I c l) (at level 100, right associativity).

    Local Notation " 'TFunction' " := (@TFunction I). 
    Local Notation " 'TNat' " := (@TNat I). 
    Local Notation " 'TBool' " := (@TBool I). 
    Local Notation " 'TString' " := (@TString I). 
    Local Notation " 'TEmpty '" := (@TEmpty I). 
    Local Notation " 'TTup' l " := (@TTup I l) (at level 90). 
    Local Notation " 'TList' t " := (@TList I t) (at level 90). 
    Local Notation " 'TVariant' l" := (@TVariant I l) (at level 90). 
    Local Notation " 'TRef' i" := (@TRef I i) (at level 90).
    Local Notation " 'TError' " := (@TError I).

    Local Notation " '$' s " := (@Var I s) (at level 90).
    Local Notation " 'T' " := (@Bool I true) (at level 90). 
    Local Notation " 'F' " := (@Bool I false) (at level 90). 
    Local Notation " '#' s" := (@String I s) (at level 50).
    Local Notation " '!' e " := (@Not I e) (at level 90).
    Local Notation " e1 & e2 " := (@And I e1 e2) (at level 91, left associativity). 
    Local Notation " e1 || e2 " := (@Or I e1 e2) (at level 50, left associativity).
    Local Notation " e1 '+.' e2 " := (@Sum I e1 e2) (at level 92, left associativity).
    Local Notation " e1 '-.' e2 " := (@Sub I e1 e2) (at level 92, left associativity).
    Local Notation " e1 '*.' e2 " := (@Mul I e1 e2) (at level 91, left associativity). 
    Local Notation " e1 '@.' e2 " := (@Concat I e1 e2) (at level 91, left associativity).
    Local Notation " e1 '==' e2 " := (@Equal I e1 e2) (at level 91, left associativity). 
    Local Notation " 'λ' l '.' e  " := (@Lam I l e) (at level 90).  
    Local Notation " 'Tup' l " := (@Tup I l) (at level 90).  
    Local Notation " 'Cons' l " := (@Cons I l) (at level 90).
    Local Notation " 'C(' c ',' l ')' " := (@EVariant I c l) (at level 90).
    Local Notation " 'Let' p '::=' e1 'In' e2" := (@ELet I p e1 e2) (at level 90).
    Local Notation " 'If' e1 'Then' e2 'Else' e3 " := (@If I e1 e2 e3) (at level 90). 
    Local Notation " 'LetRec' i '::=' e1 'In' e2 " := (@LetRec I i e1 e2) (at level 90).
    Local Notation " 'DefType' l 'In' e " := (@DefType I l e) (at level 90). 
    Local Notation " 'Match' e 'With' l " := (@Match I e l) (at level 90). 
    
   
    Definition my_length_lis : Expr I :=  
      DefType [("LIST_NAT", TVariant([
        ("Nil", []); 
        ("Cons", [TNat; TRef "LIST_NAT"])
       ]))] In 
       LetRec "map" ::= λ[$p"f"; $p"l"]. Match $"l" With [
                              (pC("Nil", []), C("Nil", [])); 
                              (pC("Cons", [$p"n"; $p"t"]), 
                                C("Cons", [App ($"f") [$"n"]; App ($"map") [$"f"; $"t"]]))
                              ] 
       In App ($"map") [λ[$p"x"]. $"x"; 
                        C("Cons", [(@Nat I 0); C("Cons", [(@Nat I 1) ; C("Nil", [])])])] .  

    Definition my_nat := DefType [("NAT", TVariant([
        ("Z", []); 
        ("S", [TRef "NAT"])
      ]))] In 
       LetRec "sum" ::= λ[$p"x"; $p"y"]. Match $"x" With [
                              (pC("Z", []), $"y"); 
                              (pC("S", [$p"n"]), C("S", [App ($"sum") [$"n"; $"y"]]))
                          ] 
       In App ($"sum") [C("S", [C("S", [C("S", [C("Z", [])])])]); 
                        C("Z", [])] .
                    
    Definition my_prog_des := @desugar_Expr I my_length_lis.
    Definition register_empty := @empty_env (Ide I) (unit). 
    Definition c_env_empty := @empty_env (Constr I) ((Ide I) * (KTp I P)).
    Definition my_prog_elab := elab my_prog_des [] register_empty c_env_empty.
    Definition v_env_empty := @empty_env (Ide I) (Val I P).

    Definition my_prog_eval := 
      match my_prog_elab with 
      |Ok le   => eval (1000) le v_env_empty 
      |Error m => Error ("elaboration failed with the following error message: " ++ m) 
      end.  

    Eval vm_compute in my_prog_des.
    Eval vm_compute in my_prog_elab.
    Eval vm_compute in my_prog_eval.
  

    
    


    
   

    
End MC_lang. 