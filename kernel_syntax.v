Require Import Strings.String Lists.List ids primitives.
Import ListNotations. 


Set Implicit Arguments. 
Set Contextual Implicit. 

Section KERNEL_SYNTAX. 
  
  Variable I : IDS. 
  Variable P : PRIM_DATA.
  
  Local Notation " 'Ide' " := (Ide I).
  Local Notation " 'BaseVl' " := (BaseVl P).
  Local Notation " 'Constr' " := (Constr I).
  Local Notation " 'BaseTp' " := (BaseTp P).
  Local Notation " 'OP' " := (OP P).
  Local Notation " 'Message' " := (Message I).

  Inductive KPat : Type := 
  |KPVar (i: Ide)
  |KPLit (p: BaseVl)
  |KPAs (p: KPat) (i: Ide)
  |KPAny
  |KPUnit  
  |KPNil 
  |KPPair (p1: KPat) (p2: KPat)
  |KPCons (p1: KPat) (p2: KPat)
  |KPVariant (c: Constr) (p: KPat).  


  Inductive KTp: Type := 
  |KTFunction
  |KTBase (t: BaseTp)
  |KTUnit 
  |KTEmpty
  |KTProd (t1: KTp) (t2: KTp)
  |KTList (t: KTp)
  |KTVariant (tags: list (Constr * KTp))
  |KTRef (i: Ide)
  |KTError . 


  Inductive KExpr : Type := 
  |KVar (i: Ide)
  |KLit (x: BaseVl)
  |KOp (op: OP) (args: list KExpr) 
  |KLam (p: KPat) (e: KExpr) 
  |KApp (e1: KExpr) (e2: KExpr)
  |KUnit
  |KNil 
  |KPair (e1 : KExpr) (e2: KExpr)
  |KCons (e1: KExpr) (e2: KExpr) 
  |KVariant (c: Constr) (e: KExpr)
  |KFix (name: Ide) (cls: KExpr) 
  |KDefType (l: list (Ide * KTp)) (e: KExpr)
  |KMatch (e: KExpr) (cases: list (KPat * KExpr))
  |KError (m: Message).




    (* 1. INDUCTION PRINCIPLE FOR TYPES *)
    Section Tp_ind'.
        
        Variable Q: KTp -> Prop. 

        Hypothesis TFun_case       : Q KTFunction.
        Hypothesis TBase_case      : forall t, Q (KTBase t).   
        Hypothesis TUnit_case      : Q KTUnit . 
        Hypothesis TEmpty_case     : Q KTEmpty. 
        Hypothesis TProd_case      : forall t1 t2,  
                                        Q t1 -> 
                                        Q t2 -> 
                                        Q (KTProd t1 t2).
        Hypothesis TList_case      : forall t, 
                                        Q t -> 
                                        Q (KTList t). 
        Hypothesis TVariant_case   : forall lis, 
                                        Forall (fun p => Q (snd p)) lis -> 
                                        Q (KTVariant lis). 
        Hypothesis TRef_case       : forall i, Q (KTRef i). 
        Hypothesis TError_case     : Q KTError. 
        
        
        Fixpoint KTp_ind' t : Q t := 
          match t with 
          |KTFunction         => TFun_case 
          |KTBase t           => TBase_case  
          |KTUnit             => TUnit_case 
          |KTEmpty            => TEmpty_case 
          |KTProd t1 t2       => TProd_case (KTp_ind') (KTp_ind')
          |KTList t           => TList_case (KTp_ind')
          |KTVariant lis      => TVariant_case
            ((fix lis_ind' l : Forall (fun p => Q (snd p)) l := 
                match l with 
                |[]         => Forall_nil _ 
                |(_, _)::_ => Forall_cons _ (KTp_ind') (lis_ind' _)
                end) lis)
          |KTRef i            => TRef_case  
          |KTError            => TError_case 
          end.
  
    End Tp_ind'.
    


    (* Induction principle for expressions *)
    Section KExpr_ind'.
      
      Variable Q: KExpr -> Prop.
      
      Hypothesis KVar_case     : forall i, Q (KVar i).
      Hypothesis KLit_case     : forall x, Q (KLit x).
      Hypothesis KOp_case      : forall op l, Forall Q l -> Q (KOp op l).
      Hypothesis KLam_case     : forall p e, Q e -> Q (KLam p e).
      Hypothesis KApp_case     : forall e1 e2, Q e1 -> Q e2 -> Q (KApp e1 e2).
      Hypothesis KUnit_case    : Q KUnit.
      Hypothesis KNil_case     : Q KNil. 
      Hypothesis KPair_case    : forall e1 e2, Q e1 -> Q e2 -> Q (KPair e1 e2).
      Hypothesis KCons_case    : forall e1 e2, Q e1 -> Q e2 -> Q (KCons e1 e2).
      Hypothesis KVariant_case : forall c e, Q e -> Q (KVariant c e).
      Hypothesis KFix_case     : forall i e, Q e -> Q (KFix i e). 
      Hypothesis KDefType_case : forall l e, Q e -> Q (KDefType l e).
      Hypothesis KMatch_case   : forall e l,
                                   Q e ->
                                   Forall (fun p => Q (snd p)) l -> 
                                   Q (KMatch e l).
      Hypothesis KError_case   : forall m, Q (KError m).


      Fixpoint KExpr_ind' (e: KExpr) : Q e := 
        match e with 
        |KVar _       => KVar_case
        |KLit _       => KLit_case
        |KOp _ _      => KOp_case ((fix lis_expr_ind' l : Forall Q l := 
                                     match l with 
                                     |[]   => Forall_nil _
                                     |h::t => Forall_cons _ (KExpr_ind') (lis_expr_ind' t) 
                                     end) _)  
        |KLam _ _     => KLam_case (KExpr_ind')  
        |KApp _ _     => KApp_case (KExpr_ind') (KExpr_ind') 
        |KUnit        => KUnit_case 
        |KNil         => KNil_case 
        |KPair _ _    => KPair_case (KExpr_ind') (KExpr_ind') 
        |KCons _ _    => KCons_case (KExpr_ind') (KExpr_ind') 
        |KVariant _ _ => KVariant_case (KExpr_ind') 
        |KFix _ _     => KFix_case (KExpr_ind')
        |KDefType _ _ => KDefType_case (KExpr_ind')
        |KMatch _ _   => KMatch_case (KExpr_ind') 
                          ((fix lis_cases_ind' l : Forall (fun p => Q (snd p)) l :=
                              match l with 
                              |[]        => Forall_nil _ 
                              |(p, e)::t => Forall_cons _ (KExpr_ind') (lis_cases_ind' t)
                              end) _)
        |KError _     => KError_case
        end.


    End KExpr_ind'.
    

  End KERNEL_SYNTAX. 


  
  














 




