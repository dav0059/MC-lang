Require Import ids primitives Strings.String Lists.List. 
Import ListNotations.

Set Implicit Arguments. 
Set Contextual Implicit.

Section SURFACE_SYNTAX . 

   Context (I: IDS). 

   Inductive Pat : Type := 
   |PVar (x: I.(Ide))
   |PBool (x: bool)
   |PNat (x: nat)
   |PString (x: string)
   |PAny 
   |PAs (p: Pat) (x: I.(Ide))  
   |PTup (lis: list Pat)
   |PCons (lis: list Pat)
   |PVariant (c: I.(Constr)) (lis: list Pat). 
   

   Inductive Tp : Type := 
   |TFunction 
   |TBool 
   |TNat 
   |TString
   |TEmpty
   |TTup (lis: list Tp)
   |TList (t: Tp)
   |TVariant (tags: list (I.(Constr) * list Tp))
   |TRef (i: I.(Ide))
   |TError . 


   Inductive Expr : Type := 
   |Var (x: I.(Ide))
   |Bool (x: bool)
   |Nat (x: nat)
   |String (x: string)
   |Not (e: Expr)
   |And (e1 e2 : Expr)
   |Or (e1 e2: Expr)
   |Sum (e1 e2 : Expr)
   |Sub (e1 e1 : Expr)
   |Mul (e1 e2 : Expr)
   |Concat (e1 e2 : Expr)
   |Equal (e1 e2: Expr)
   |Lam (form: list Pat) (body: Expr)
   |App (e1: Expr) (args: list Expr) 
   |Tup (lis: list Expr)
   |Cons (lis: list Expr)
   |EVariant (c: I.(Constr)) (args: list Expr)
   |ELet (p: Pat) (e1: Expr) (e2: Expr)
   |If (e1: Expr) (e2: Expr) (e3: Expr)
   |LetRec (name: I.(Ide)) (cls: Expr) (e: Expr)
   |DefType (block: list (I.(Ide) * Tp)) (e: Expr)
   |Match (e: Expr) (block: list (Pat * Expr))
   |EError (m: I.(Message)).
   
   
   Section Pat_ind'. 
      Variable P : Pat -> Prop.
      
      Hypothesis PVar_case        : forall i, P (PVar i). 
      Hypothesis PBool_case       : forall b, P (PBool b). 
      Hypothesis PNat_case        : forall n, P (PNat n).
      Hypothesis PString_case     : forall s, P (PString s).
      Hypothesis PAny_case        : P PAny.
      Hypothesis PAs_case         : forall i p, P p -> P (PAs p i). 
      Hypothesis PTup_case        : forall l, Forall P l -> P (PTup l). 
      Hypothesis PCons_case       : forall l, Forall P l -> P (PCons l).
      Hypothesis PVariant_case    : forall c l, Forall P l -> P (PVariant c l).
      
      Fixpoint Pat_ind' (p: Pat) : P p :=  
         match p with 
         |PVar x         => PVar_case 
         |PBool x        => PBool_case 
         |PNat x         => PNat_case 
         |PString x      => PString_case 
         |PAny           => PAny_case 
         |PAs p i        => PAs_case (Pat_ind')    
         |PTup lis       => PTup_case  
            ((fix lis_pat_ind (l: list Pat) : Forall P l := 
               match l with 
               |[] => @Forall_nil _ _ 
               |h::t => @Forall_cons _ _ h t (Pat_ind') (lis_pat_ind t)
               end ) lis)
         |PCons lis      => PCons_case  
            ((fix lis_pat_ind (l: list Pat) : Forall P l := 
               match l with 
               |[] => @Forall_nil _ _ 
               |h::t => @Forall_cons _ _ h t (Pat_ind') (lis_pat_ind t)
               end ) lis)
         |PVariant c lis => PVariant_case   
            ((fix lis_pat_ind (l: list Pat) : Forall P l := 
               match l with 
               |[] => @Forall_nil _ _ 
               |h::t => @Forall_cons _ _ h t (Pat_ind') (lis_pat_ind t)
               end ) lis)  
      end.

   End Pat_ind'.


   Section Tp_ind'. 

      Variable P: Tp -> Prop.
      
      Hypothesis TFun_case     : P TFunction. 
      Hypothesis TBool_case    : P TBool. 
      Hypothesis TNat_case     : P TNat. 
      Hypothesis TString_case  : P TString. 
      Hypothesis TEmpty_case   : P TEmpty. 
      Hypothesis TTup_case     : forall l, Forall P l -> P (TTup l). 
      Hypothesis TList_case    : forall t, P t -> P (TList t). 
      Hypothesis TVariant_case : forall l, 
                                  Forall (fun p => Forall (fun t => P t) (snd p)) l ->
                                  P (TVariant l). 
      Hypothesis TRef_case     : forall x, P (TRef x).
      Hypothesis TError_case   : P TError.


      Fixpoint Tp_ind' (t: Tp) : P t :=  
         match t with 
         |TFunction               => TFun_case 
         |TBool                   => TBool_case
         |TNat                    => TNat_case 
         |TString                 => TString_case
         |TEmpty                  => TEmpty_case
         |TTup lis                => TTup_case  
            ((fix lis_tp_ind' (l: list Tp) : Forall P l := 
               match l with 
               |[]   => Forall_nil _   
               |h::t => Forall_cons _ (Tp_ind') (lis_tp_ind' t) 
               end) lis )
         |TList t                 => TList_case (Tp_ind') 
         |TVariant lis            => TVariant_case  
            ((fix lis_variant_ind' (l: list (I.(Constr) * list Tp)) :
                                   Forall (fun p => Forall (fun t => P t) (snd p)) l := 
               match l with 
               |[]        => Forall_nil _   
               |((c, h) as el)::t => @Forall_cons _ _ el t 
                                     ((fix lis_variant_ind'' (l: list Tp) : Forall (fun t => P t) l := 
                                        match l with 
                                        |[]  => Forall_nil _  
                                        |x::xs => @Forall_cons _ _ x xs (Tp_ind') 
                                                   (lis_variant_ind'' xs) 
                                        end) h) (lis_variant_ind' t)     
               end) lis) 
         |TRef i                   => TRef_case 
         |TError                   => TError_case
         end.
         
         
         
   End Tp_ind'. 
   
   
   Section Expr_ind'. 

         Variable P: Expr -> Prop. 

         Hypothesis Var_case      : forall x, P (Var x). 
         Hypothesis Bool_case     : forall b, P (Bool b). 
         Hypothesis Nat_case      : forall n, P (Nat n).
         Hypothesis String_case   : forall s, P (String s). 
         Hypothesis Not_case      : forall e, P e -> P (Not e). 
         Hypothesis And_case      : forall e1 e2, P e1 -> P e2 -> P (And e1 e2).
         Hypothesis Or_case       : forall e1 e2, P e1 -> P e2 -> P (Or e1 e2). 
         Hypothesis Sum_case      : forall e1 e2, P e1 -> P e2 -> P (Sum e1 e2).
         Hypothesis Sub_case      : forall e1 e2, P e1 -> P e2 -> P (Sub e1 e2). 
         Hypothesis Mul_case      : forall e1 e2, P e1 -> P e2 -> P (Mul e1 e2).
         Hypothesis Concat_case   : forall e1 e2, P e1 -> P e2 -> P (Concat e1 e2). 
         Hypothesis Eq_case       : forall e1 e2, P e1 -> P e2 -> P (Equal e1 e2). 
         Hypothesis Lam_case      : forall l e, P e -> P (Lam l e).
         Hypothesis App_case      : forall e l, P e -> Forall P l -> P (App e l).
         Hypothesis Tup_case      : forall l, Forall P l -> P (Tup l).
         Hypothesis Cons_case     : forall l, Forall P l -> P (Cons l). 
         Hypothesis EVariant_case : forall c l, Forall P l -> P (EVariant c l).
         Hypothesis ELet_case     : forall p e1 e2, P e1 -> P e2 -> P (ELet p e1 e2). 
         Hypothesis If_case       : forall e1 e2 e3, P e1 -> P e2 -> P e3 -> P (If e1 e2 e3). 
         Hypothesis LetRec_case   : forall i e1 e2, P e1 -> P e2 -> P (LetRec i e1 e2). 
         Hypothesis DefType_case  : forall l e, P e -> P (DefType l e). 
         Hypothesis Match_case    : forall e l, P e -> Forall (fun p => P (snd p)) l -> P (Match e l).
         Hypothesis Error_case    : forall m, P (EError m).
         
         Fixpoint Expr_ind' e : P e := 
            match e with 
            |Var _                    => Var_case 
            |Bool _                   => Bool_case 
            |Nat _                    => Nat_case 
            |String _                 => String_case 
            |Not _                    => Not_case (Expr_ind')
            |And _ _                  => And_case (Expr_ind') (Expr_ind') 
            |Or _ _                   => Or_case (Expr_ind') (Expr_ind')
            |Sum _ _                  => Sum_case (Expr_ind') (Expr_ind')
            |Sub _ _                  => Sub_case (Expr_ind') (Expr_ind') 
            |Mul _ _                  => Mul_case (Expr_ind') (Expr_ind')  
            |Concat _ _               => Concat_case (Expr_ind') (Expr_ind') 
            |Equal _ _                => Eq_case (Expr_ind') (Expr_ind') 
            |Lam _ _                  => Lam_case (Expr_ind')
            |App _ _                  => App_case (Expr_ind')
                  ((fix lis_Expr_ind' (l: list Expr) : Forall P l :=   
                     match l with 
                     |[]     => Forall_nil _ 
                     |h::t   => Forall_cons _ (Expr_ind') (lis_Expr_ind' t) 
                     end) _)
            |Tup _                    => Tup_case  
                  ((fix lis_Expr_ind' (l: list Expr) : Forall P l :=   
                     match l with 
                     |[]     => Forall_nil _ 
                     |h::t   => Forall_cons _ (Expr_ind') (lis_Expr_ind' t) 
                     end) _ )
            |Cons _                    => Cons_case 
               ((fix lis_Expr_ind' (l: list Expr) : Forall P l :=   
                     match l with 
                     |[]     => Forall_nil _ 
                     |h::t   => Forall_cons _ (Expr_ind') (lis_Expr_ind' t) 
                     end) _)    
            |EVariant _ _              => EVariant_case 
               ((fix lis_Expr_ind' (l: list Expr) : Forall P l :=   
                     match l with 
                     |[]     => Forall_nil _ 
                     |h::t   => Forall_cons _ (Expr_ind') (lis_Expr_ind' t) 
                     end) _)
            |ELet _ _ _                => ELet_case (Expr_ind') (Expr_ind')        
            |If _ _ _                  => If_case (Expr_ind') (Expr_ind' ) (Expr_ind')
            |LetRec _ _ _              => LetRec_case (Expr_ind' ) (Expr_ind' )
            |DefType _ _               => DefType_case (Expr_ind' )
            |Match _ _                 => Match_case (Expr_ind') 
               ((fix lis_Expr_ind' (l: list (Pat * Expr)) :  Forall (fun p => P (snd p)) l :=   
                     match l with 
                     |[]     => Forall_nil _ 
                     |h::t   => Forall_cons _ (Expr_ind' ) (lis_Expr_ind' t) 
                     end) _)
            |EError _                   => Error_case  
            end.  
         
   End Expr_ind'. 


End SURFACE_SYNTAX. 
