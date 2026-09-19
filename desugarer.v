Require Import Lists.List Strings.String PeanoNat. 
Import ListNotations.
Require Import primitives ids kernel_syntax surface_syntax.  
Open Scope string_scope.

Set Implicit Arguments. 
Set Contextual Implicit. 

(* The version of the kernel language we are going to implement and verify is generic on IDS but 
   concrete on PRIM_DATA, i.e. comes from a particular choice of primtive data and operations on 
   them. The chosen set consists of Naturals, Booleans and Strings . The desugarer will be 
   defined on a surface syntax having built-in primitive data and operations corresponding to 
   those we've chosen to be definable into the kernel.  *)
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
     |OpNot 
     |OpAnd 
     |OpOr
     |OpSum 
     |OpSub
     |OpMul 
     |OpConcat 
     |OpEq . 

     Definition typeof_base_vl (v: BaseVal) : BaseTyp := 
      match v with 
      |VlNat _ => TpNat 
      |VlBool _ => TpBool 
      |VlString _ => TpString 
      end.

     Definition interp_prim_op (o: Op) (l: list BaseVal) : option BaseVal := 
      match o, l with
      |OpNot, [VlBool b1]            => Some (VlBool (negb b1))
      |OpAnd, [VlBool b1; VlBool b2] => Some (VlBool (andb b1 b2)) 
      |OpOr, [VlBool b1; VlBool b2]  => Some (VlBool (orb b1 b2)) 
      |OpSum, [VlNat n1; VlNat n2]   => Some (VlNat (n1 + n2))
      |OpSub, [VlNat n1; VlNat n2]   => Some (VlNat (n1 - n2))
      |OpMul, [VlNat n1; VlNat n2]   => Some (VlNat (n1 * n2))
      |OpConcat, [VlString s1; VlString s2] => Some (VlString (String.append s1 s2))
      |OpEq, [x1; x2] => match x1, x2 with 
                        |VlNat n1, VlNat n2 => Some (VlBool (Nat.eqb n1 n2))
                        |VlBool b1, VlBool b2 => Some (VlBool (Bool.eqb b1 b2)) 
                        |VlString s1, VlString s2 => Some (VlBool (eqb s1 s2))
                        |_, _        => None    
                        end
      |_, _          => None 
      end. 

    
    Definition eqb_BaseTyp (t t': BaseTyp) : bool := 
      match t, t' with 
      |TpNat, TpNat | TpBool, TpBool | TpString, TpString => true
      |_, _  => false 
      end.
      
    Definition eqb_BaseVal (v v' : BaseVal) : bool := 
      match v, v' with 
      |VlNat n, VlNat n'  => Nat.eqb n n' 
      |VlBool b, VlBool b' => Bool.eqb b b' 
      |VlString s, VlString s' => eqb s s' 
      |_, _ => false 
      end.  

    Definition digit_to_string (n: nat) : string := 
      match n with 
      |0   => "0"
      |1   => "1"
      |2   => "2"
      |3   => "3"
      |4   => "4"
      |5   => "5"
      |6   => "6" 
      |7   => "7"
      |8   => "8"
      |9   => "9"
      |_   => "" 
      end. 
      
  
    Fixpoint fuel_nat_to_string (fuel: nat) (n: nat) : string := 
      match fuel with 
      |O    => ""
      |S n' => if Nat.leb n 10 then digit_to_string n 
               else fuel_nat_to_string n' (Nat.div n 10) ++ 
                 digit_to_string (Nat.modulo n 10)
      end.
      
    Definition nat_to_string n := fuel_nat_to_string n n.

    Definition BaseVal_to_string (v: BaseVal) : string := 
      match v with 
      |VlNat n      => nat_to_string n 
      |VlBool true  => "true"
      |VlBool false => "false" 
      |VlString s   => "\" ++ s ++ "\" 
      end.

      
    Lemma eq_baseTp_dec : forall (x y: BaseTyp), {x = y} + {x <> y} . 
    Proof. intros. destruct x, y; try eauto; right; discriminate. Qed.
       

    Lemma eq_baseVl_dec : forall (x y: BaseVal), {x = y} + {x <> y}. 
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
    
    
    Lemma eqb_eq_BaseTyp : forall t t', Bool.reflect (t = t') (eqb_BaseTyp t t').
    Proof. 
       intros. apply Bool.iff_reflect; 
       split; intros; destruct t; inversion H; eauto;
       destruct t'; eauto; discriminate.
    Qed.   

    Lemma eqb_eq_BaseVal : forall v v', Bool.reflect (v = v') (eqb_BaseVal v v').
    Proof.
       intros. apply Bool.iff_reflect;
       split; intros; destruct v; inversion H; simpl. 
       + rewrite Nat.eqb_eq; eauto. 
       + rewrite Bool.eqb_true_iff; eauto.
       + rewrite eqb_eq; eauto.
       + destruct v'; simpl in *; try rewrite Nat.eqb_eq in H; 
         subst; eauto; discriminate.
       + destruct v'; simpl in *; try rewrite Bool.eqb_true_iff in H; 
         subst; eauto; discriminate.
       + destruct v'; simpl in *; try rewrite eqb_eq in H; 
         subst; eauto; discriminate.
    Qed.          
       


    Definition bns_data : PRIM_DATA := 
    {| BaseTp := BaseTyp ; 
       BaseVl := BaseVal ; 
       OP := Op;
       base_tp_of_base_vl := typeof_base_vl ;
       interp_op := interp_prim_op;
       eqb_BaseTp := eqb_BaseTyp; 
       eqb_BaseVl := eqb_BaseVal; 
       BaseVl_to_string := BaseVal_to_string; 
       eq_BaseTp_dec := @eq_baseTp_dec; 
       eq_BaseVl_dec := @eq_baseVl_dec; 
       eqb_eq_BaseTp := @eqb_eq_BaseTyp ;
       eqb_eq_BaseVl := @eqb_eq_BaseVal  |} .


Section Desugarer. 
        
   Context (I: IDS). 
    
   (* common lemmas *)
   Section common.
       
       Variable X : Type. 
       Variable Y : Type.

       Lemma forall2_eq_map: forall (l: list X) (l': list Y) (f: X -> Y), 
         Forall2 (fun x y => f x = y) l l' <->  map f l = l'. 
       Proof.
              split; intros. 
              + generalize dependent l'; induction l; intros. 
                ++ inversion H; reflexivity.
                ++ inversion H; subst; simpl; f_equal; apply IHl; assumption. 
              + generalize dependent l'; induction l; intros. 
                ++ inversion H; subst; simpl; apply Forall2_nil. 
                ++ inversion H; subst; simpl; apply Forall2_cons; 
                   try reflexivity; 
                   apply IHl; reflexivity.
       
       Qed. 

       Lemma Forall2P_eq_Forall2f: forall l l' (P: X -> Y -> Prop) (f: X -> Y), 
              (forall x y, P x y <-> f x = y) -> Forall2 P l l' <-> Forall2 (fun x y => f x = y) l l'. 
       Proof. 
              split; intros;  
              generalize dependent l'; induction l; intros; 
              inversion H0; subst;
              first [apply Forall2_nil |
                     apply Forall2_cons ];
              try apply H; try apply IHl; try reflexivity; assumption.         
       Qed.
              
   End common.


   (* 1. PATTERN DESUGARING *)
       (* 1.1. helper functions for pattern desugaring*)              
       Fixpoint from_lispat_to_tup (l:list (KPat I bns_data)) := 
              match l with 
              |[]   => KPUnit
              |h::t => KPPair h (from_lispat_to_tup t)
              end.


       (* 1.2. specification for pattern desugaring *) 
       
       Inductive Desugar_Pat: Pat I -> KPat I bns_data -> Prop :=   
       |dsg_PVar       : forall i,   
                          Desugar_Pat (PVar i) (KPVar i)
       |dsg_PBool      : forall b, Desugar_Pat (PBool b) (@KPLit _ bns_data (VlBool b))
       |dsg_PNat       : forall n, Desugar_Pat (PNat n) (@KPLit _ bns_data (VlNat n))
       |dsg_PString    : forall s, Desugar_Pat (PString s) (@KPLit _ bns_data (VlString s)) 
       |dsg_PAny       : Desugar_Pat (PAny) (KPAny) 
       |dsg_PAs        : forall p1 p2 i,
                            Desugar_Pat p1 p2 ->  
                            Desugar_Pat (PAs p1 i) (KPAs p2 i)
       |dsg_PTup       : forall l l',
                            Forall2 Desugar_Pat l l' -> 
                            Desugar_Pat (PTup l) (from_lispat_to_tup l') 
       |dsg_PNil       : Desugar_Pat PNil KPNil  
       |dsg_PCons      : forall head head' tail tail',
                            Desugar_Pat head head'->
                            Desugar_Pat tail tail' -> 
                            Desugar_Pat (PCons head tail) (KPCons head' tail')
       |dsg_PVariant   : forall c l l',
                            Forall2 Desugar_Pat l l' ->  
                            Desugar_Pat (PVariant c l) (KPVariant c (from_lispat_to_tup l')).



       (* 1.3. induction principle for Desugar_Pat proposition *)
       Section Desugar_Pat_ind'.

              Variable P  : Pat I -> KPat I bns_data -> Prop.

              Hypothesis PVar_case     : forall i, P (PVar i) (KPVar i). 
              Hypothesis PBool_case    : forall b, P (PBool b) (@KPLit _ bns_data (VlBool b)).
              Hypothesis PNat_case     : forall n, P (PNat n) (@KPLit _ bns_data (VlNat n)).
              Hypothesis PString_case  : forall s, P (PString s) (@KPLit _ bns_data (VlString s)).
              Hypothesis PAny_case     : P PAny (KPAny).
              Hypothesis PAs_case      : forall i p p' , 
                                          P p p' -> 
                                          P (PAs p i) (KPAs p' i).
              Hypothesis PTup_case     : forall l l', 
                                          Forall2 P l l' -> 
                                          P (PTup l) (from_lispat_to_tup l').
              Hypothesis PNil_case     : P PNil KPNil.
              Hypothesis PCons_case    : forall head head' tail tail', 
                                          P head head' ->
                                          P tail tail' ->
                                          P (PCons head tail) (KPCons head' tail').
              Hypothesis PVariant_case : forall c l l',  
                                          Forall2 P l l' ->
                                          P (PVariant c l) (KPVariant c (from_lispat_to_tup l')).
              
              

              Fixpoint Desugar_Pat_ind' (ps: Pat I) (pk: KPat I bns_data) 
                                          (H: Desugar_Pat ps pk) : P ps pk := 
                     match H with 
                     |dsg_PVar => PVar_case 
                     |dsg_PBool => PBool_case 
                     |dsg_PNat  => PNat_case  
                     |dsg_PString => PString_case  
                     |dsg_PAny => PAny_case 
                     |dsg_PAs H => PAs_case (Desugar_Pat_ind' H) 
                     |dsg_PTup H => PTup_case  
                            ((fix list_pat_ind' lis lis' 
                                                 (H: Forall2 Desugar_Pat lis lis')
                                   : Forall2 P lis lis' := 
                            match H with 
                            |Forall2_nil _ => Forall2_nil P   
                            |Forall2_cons _ _ Hh Ht  => 
                                   Forall2_cons _ _
                                   (Desugar_Pat_ind' Hh) (list_pat_ind' _ _ Ht)    
                            end) _ _ H )
                     |dsg_PNil       => PNil_case 
                     |dsg_PCons H H' => PCons_case (Desugar_Pat_ind' H) (Desugar_Pat_ind' H')
                     |dsg_PVariant H => PVariant_case  
                            ((fix list_pat_ind' lis lis' 
                                                 (H: Forall2 Desugar_Pat lis lis')
                                   : Forall2 P lis lis' := 
                            match H with 
                            |Forall2_nil _ => Forall2_nil P   
                            |Forall2_cons _ _ Hh Ht => 
                                   Forall2_cons _ _
                                   (Desugar_Pat_ind' Hh ) (list_pat_ind' _ _ Ht)    
                            end) _ _ H) 
                     end.

       End Desugar_Pat_ind'.


       (* 1.4. function for pattern desugaring *)

       Fixpoint desugar_Pat (p : Pat I) : KPat I bns_data :=
         match p with 
         |PVar i                     => KPVar i 
         |PBool b                    => @KPLit _ bns_data (VlBool b) 
         |PNat n                     => @KPLit _ bns_data (VlNat n)
         |PString s                  => @KPLit _ bns_data (VlString s)
         |PAny                       => KPAny 
         |PAs p' i                   => KPAs (desugar_Pat p') i
         |PTup lis                   => from_lispat_to_tup (map desugar_Pat lis)   
         |PNil                       => KPNil
         |PCons head tail            => KPCons (desugar_Pat head) (desugar_Pat tail)
         |PVariant c lis             => KPVariant c (from_lispat_to_tup (map desugar_Pat lis))
         end.



       (* 1.5. correctness of the implementation for pattern desugaring *)
       Theorem desugar_Pat_correct: forall p p', 
           desugar_Pat p = p' -> Desugar_Pat p p' . 
       Proof. 
              intros p p' Hdesugar. 
              generalize dependent p'.   
              induction p using Pat_ind';
              intros; subst; simpl; 
              eauto using 
              dsg_PVar, dsg_PBool, dsg_PNat, dsg_PString, dsg_PAny ,  
              dsg_PAs, dsg_PNil, dsg_PCons.
              + apply dsg_PTup. induction l.          
                 * simpl; apply Forall2_nil.
                 * apply Forall2_cons; inversion H; subst; clear H;
                   try apply H2; eauto.
              + apply dsg_PVariant. induction l. 
                 * simpl; apply Forall2_nil.
                 * apply Forall2_cons; inversion H; subst; clear H;
                   try apply H2; eauto.
       Qed. 


       (* completeness of the implementation for pattern desugaring *)
       Theorem desugar_Pat_complete: forall p p', 
         Desugar_Pat p p' -> desugar_Pat p = p'. 
       Proof.
              intros p p' H. 
              induction H using Desugar_Pat_ind';  
              simpl; eauto; 
              try (subst; reflexivity);  
              repeat f_equal; apply forall2_eq_map; assumption. 
       Qed.       
       

       Corollary desugar_Pat_eq_Desugar_Pat: forall p p', 
         Desugar_Pat p p' <-> desugar_Pat p = p'. 
       Proof. 
              split.
              apply desugar_Pat_complete. 
              apply desugar_Pat_correct. 
       Qed.
       
       

   (* 2. TYPE DESUGARING *)
       
       (* 2.1. helper function for type desugaring *)
       Fixpoint from_listTp_to_tup (l: list (KTp I bns_data)) := 
          match l with 
          |[]   => KTUnit
          |h::t => KTProd h (from_listTp_to_tup t)
          end. 
 
       
       (* 2.2. specification for type desugaring *)   
       Inductive Desugar_Tp: Tp I -> KTp I bns_data -> Prop := 
       |dsg_TFunction   : Desugar_Tp (TFunction) (KTFunction)
       |dsg_TBool       : Desugar_Tp (TBool) (@KTBase _ bns_data(TpBool))
       |dsg_TNat        : Desugar_Tp (TNat) (@KTBase _ bns_data (TpNat))
       |dsg_TString     : Desugar_Tp (TString) (@KTBase _ bns_data (TpString))
       |dsg_TEmpty      : Desugar_Tp (TEmpty) (KTEmpty)
       |dsg_TProd       : forall l l',  
                            Forall2 Desugar_Tp l l' ->
                            Desugar_Tp (TTup l) (from_listTp_to_tup l') 
       |dsg_TList       : forall t t', 
                            Desugar_Tp t t' -> 
                            Desugar_Tp (TList t) (KTList t')                         
       |dsg_TVariant    : forall l1 l2 l3, 
                            Forall2 (fun p q =>
                               fst p = fst q /\ 
                               Forall2 Desugar_Tp (snd p) (snd q)) l1 l2 ->
                            Forall2 (fun p q => 
                               fst p = fst q /\ 
                               snd q = from_listTp_to_tup (snd p)) l2 l3 ->  
                            Desugar_Tp (TVariant l1) (KTVariant l3)
       |dsg_TRef        : forall i, Desugar_Tp (TRef i) (KTRef i) 
       |dsg_TError      : Desugar_Tp (TError) (KTError). 


       (* 2.3. induction principle for Desugar_Tp proposition *)
       Section Desugar_Tp_ind'.
              
              Variable P : Tp I -> KTp I bns_data -> Prop. 
              
              Hypothesis TFun_case     : P TFunction (KTFunction). 
              Hypothesis TBool_case    : P TBool (@KTBase _ bns_data (TpBool)).
              Hypothesis TNat_case     : P TNat (@KTBase _ bns_data (TpNat)).
              Hypothesis TString_case  : P TString (@KTBase _ bns_data (TpString)). 
              Hypothesis TEmpty_case   : P TEmpty (KTEmpty). 
              Hypothesis TProd_case    : forall l l',
                                          Forall2 P l l' ->
                                          P (TTup l) (from_listTp_to_tup l').
              Hypothesis TList_case    : forall t t', 
                                          P t t' -> 
                                          P (TList t) (KTList t'). 
              Hypothesis TVariant_case : forall l1 l2 l3, 
                                          Forall2 (fun p q => fst p = fst q /\ 
                                             Forall2 P (snd p) (snd q)) l1 l2 ->
                                          Forall2 (fun p q => fst p = fst q /\ 
                                                              snd q = from_listTp_to_tup (snd p)) l2 l3 ->
                                          P (TVariant l1) (KTVariant l3).
              Hypothesis TRef_case     : forall x, P (TRef x) (KTRef x). 
              Hypothesis TError_case   : P TError (KTError) .


              Fixpoint Desugar_Tp_ind' (ts: Tp I) (tk: KTp I bns_data) (H: Desugar_Tp ts tk)  
                                          : P ts tk :=  
                 match H with 
                 |dsg_TFunction               => TFun_case 
                 |dsg_TBool                   => TBool_case 
                 |dsg_TNat                    => TNat_case 
                 |dsg_TString                 => TString_case 
                 |dsg_TEmpty                  => TEmpty_case 
                 |dsg_TProd H                 => TProd_case  
                    ((fix lis_tp_ind' l l' (H: Forall2 Desugar_Tp l l'): Forall2 P l l' := 
                            match H with 
                            |Forall2_nil _ => Forall2_nil _  
                            |Forall2_cons _ _ Hh Ht => 
                               Forall2_cons _ _ 
                                  (Desugar_Tp_ind' Hh) (lis_tp_ind' _ _ Ht) 
                            end ) _ _ H)
                 |dsg_TList H                 => TList_case (Desugar_Tp_ind' H)
                 |dsg_TVariant H1 H2          => TVariant_case  
                    ((fix lis_variant_ind' l l'
                                           (H: Forall2 (fun p q => fst p = fst q /\
                                                 Forall2 Desugar_Tp (snd p) (snd q)) l l') :
                                           Forall2 (fun p q => fst p = fst q /\ 
                                             Forall2 P (snd p) (snd q)) l l' := 
                            match H with 
                            |Forall2_nil _  => Forall2_nil _ 
                            |Forall2_cons _ _ Hh Ht =>   
                                Forall2_cons _ _ 
                                 (match Hh with 
                                  |conj A B =>  conj A ((fix lis_variant_ind'' l l' 
                                                              (H: Forall2 Desugar_Tp l l') : Forall2 P l l' := 
                                                            match H with 
                                                            |Forall2_nil _ => Forall2_nil _ 
                                                            |Forall2_cons _ _ Hh Ht => 
                                                               Forall2_cons _ _ (Desugar_Tp_ind' Hh) 
                                                                 (lis_variant_ind'' _ _ Ht) 
                                                            end) _ _ B) end) 
                                 (lis_variant_ind' _ _ Ht)  
                                                         
                            end ) _ _ H1) H2
                 |dsg_TRef                    => TRef_case  
                 |dsg_TError                  => TError_case 
                 end.
              
       End Desugar_Tp_ind'.


       (* 2.4. function for type desugaring *)
       Fixpoint desugar_Tp (t: Tp I) : KTp I bns_data :=
          match t with 
          |TFunction          => KTFunction 
          |TBool              => @KTBase _ bns_data (TpBool)
          |TNat               => @KTBase _ bns_data (TpNat)
          |TString            => @KTBase _ bns_data (TpString)
          |TEmpty             => KTEmpty 
          |TTup lis           => from_listTp_to_tup (map desugar_Tp lis)
          |TList t            => KTList (desugar_Tp t)
          |TVariant lis       => let l := map (fun x => (fst x, map (desugar_Tp) (snd x))) lis in 
                                 KTVariant (map (fun x => (fst x, from_listTp_to_tup (snd x))) l)  
          |TRef i             => KTRef i
          |TError             => KTError
         end.
       


       (* 2.5. correctness of implementation for type desugaring *)
       Theorem desugar_Tp_correct: forall t t', 
            desugar_Tp t = t' -> Desugar_Tp t t'. 
       Proof.
              intros t t' Hdesugar.
              generalize dependent t'. 
              induction t using Tp_ind'; 
              intros; subst; simpl;    
              eauto using 
              dsg_TFunction, dsg_TBool, dsg_TNat, dsg_TString, dsg_TEmpty ,  
              dsg_TError, dsg_TRef, dsg_TList. 
              + apply dsg_TProd; induction l; simpl. 
                   -- apply Forall2_nil. 
                   -- apply Forall2_cons; inversion H; subst. 
                      eauto. 
                      apply IHl; assumption.  
              + remember (map (fun (x: Constr I * list (Tp I)) =>
                      (fst x, map desugar_Tp (snd x))) l) as l2 .    
                remember (map (fun (x: Constr I * list (KTp I bns_data)) =>
                      (fst x, from_listTp_to_tup (snd x))) l2) as l3.        
                apply dsg_TVariant with (l2 := l2) (l3 := l3).
                * generalize dependent l2. generalize dependent l3. induction l.
                  - intros; subst; apply Forall2_nil. 
                  - intros;  rewrite Heql2; apply Forall2_cons; simpl. split; eauto.
                    inversion H;
                    induction H2.
                    -- apply Forall2_nil.
                    -- apply Forall2_cons; eauto.
                    -- simpl in Heql2. destruct l2. discriminate. 
                       inversion Heql2. 
                       change (Forall2
                         (fun p q =>
                            fst p = fst q /\
                            Forall2 Desugar_Tp (snd p) (snd q)) l 
                            (map (fun x : Constr I * list (Tp I) =>
                                   (fst x, map desugar_Tp (snd x))) l)).
                       rewrite <- H2.                    
                       apply IHl with (l3 := map (fun x : Constr I * list (KTp I bns_data) =>
                                                 (fst x, from_listTp_to_tup (snd x))) l2); eauto.
                       inversion H; eauto.
                * generalize dependent l. generalize dependent l3. induction l2. 
                  - intros. simpl in *; subst. apply Forall2_nil. 
                  - intros. simpl in *. destruct l3. discriminate. 
                    apply Forall2_cons; inversion Heql3. 
                    -- eauto.
                    -- destruct l. discriminate. 
                       simpl in *.  
                       apply IHl2 with (l := l); 
                       inversion H; inversion Heql2; eauto.
                     
       Qed.


       (* 2.6. completeness of implementation for type desugaring *)
       Theorem desugar_Tp_complete: forall t t', 
           Desugar_Tp t t' -> desugar_Tp t = t'. 
       Proof. 
           intros t t' HDesugar. 
           induction HDesugar using Desugar_Tp_ind';  
           eauto.
           + simpl. f_equal. apply forall2_eq_map. assumption.
           + simpl. f_equal. eauto.
           + simpl. f_equal. apply forall2_eq_map.  
             generalize dependent l3. generalize dependent l2. 
             induction l1; intros. 
              - inversion H. inversion H0; subst. apply Forall2_nil. discriminate.
              - inversion H. inversion H0; subst. discriminate. 
                 apply Forall2_cons. 
                * simpl. destruct y0. inversion H8; destruct H6. 
                  simpl in *; subst. destruct H3; rewrite H1. 
                  repeat f_equal. apply forall2_eq_map. eauto. 
                * apply IHl1 with (l2 := l'); inversion H0; eauto. 
       Qed.
              

       Corollary desugar_Tp_eq_Desugar_Tp: forall t t',  
         Desugar_Tp t t' <-> desugar_Tp t = t'. 
       Proof. 
              split. 
              apply desugar_Tp_complete.
              apply desugar_Tp_correct. 
       Qed.


     (* 3. EXPRESSION DESUGARING *)
       (* 3.1. helper functions *)
       Fixpoint from_lispat_to_lam (l: list (KPat I bns_data)) e := 
              match l with 
              |[]   => KLam (KPUnit) e 
              |h::t => KLam h (from_lispat_to_lam t e)
              end.

       Fixpoint from_lisargs_to_napp (l: list (KExpr I bns_data)) e := 
              match l with
              |[]   => e 
              |h::t => KApp (from_lisargs_to_napp t e) h 
              end.  

       Fixpoint from_lisexpr_to_tup (l: list (KExpr I bns_data))  := 
              match l with 
              |[]   => KUnit 
              |h::t => KPair h (from_lisexpr_to_tup t)
              end.
              
                                               
       (* 3.2. specification for expression desugaring:
       -Lambda rules state that the desugaring of `Lam [p1;...;pn] e` is 
       `Lam(p1, ..., (Lam(pn, Lam(Any, e))...)`. 
       -App rules state that the desugaring of `App e1 [e2;...en]` is 
       `App (App ...(App e1 e2)...en) Unit `. 
       -Tup rules state that the desugaring of `Tup [e1;...;en]` is 
       `Pair e1 (...(Pair en Unit))`. 
       -Cons rules state that the desugaring of `Cons [e1;...;en]` is 
       `Cons e1 (...(Cons en Nil))`. 
       -Reduce rules state that the desugaring of `Reduce e1 e2 [e3;...;en]` is
       `Reduce e1 e2 (Pair e3 (...(Pair en Unit)))`.
       -Variant rules state that the desugaring of `Variant c [e1;...;en]` is 
       `Variant c (Pair e1 (...(Pair en Unit)))` .
       -Let rules state that the desugaring of `Let p e1 e2` is `App (Lam p e2) e1`.
       -If rules state that the desugaring of `If e1 e2 e3` is `Match e1 [(true, e2); (false e3)]`

       Every other form desugars in itself.

       *)
       Inductive Desugar_Expr: Expr I -> KExpr I bns_data -> Prop := 
       |dsg_Var      : forall i, 
                        Desugar_Expr (Var i) (KVar i)
       |dsg_Bool     : forall b, 
                        Desugar_Expr (Bool b) (@KLit _ bns_data (VlBool b))
       |dsg_Nat      : forall n, 
                        Desugar_Expr (Nat n) (@KLit _ bns_data (VlNat n))
       |dsg_String   : forall s, 
                        Desugar_Expr (EString s) (@KLit _ bns_data (VlString s))
       |dsg_Not      : forall e e', 
                        Desugar_Expr e e' ->
                        Desugar_Expr (Not e) (@KOp _ bns_data (OpNot) [e']) 
       |dsg_And      : forall e1 e2 e1' e2',
                        Desugar_Expr e1 e1' -> 
                        Desugar_Expr e2 e2' ->
                        Desugar_Expr (And e1 e2) (@KOp _ bns_data (OpAnd) [e1'; e2'])
       |dsg_Or       : forall e1 e2 e1' e2',
                        Desugar_Expr e1 e1' ->
                        Desugar_Expr e2 e2' ->
                        Desugar_Expr (Or e1 e2) (@KOp _ bns_data (OpOr) [e1'; e2'])
       |dsg_Sum      : forall e1 e2 e1' e2',
                        Desugar_Expr e1 e1' ->
                        Desugar_Expr e2 e2' ->
                        Desugar_Expr (Sum e1 e2) (@KOp _ bns_data (OpSum) [e1'; e2'])
       |dsg_Sub      : forall e1 e2 e1' e2',
                        Desugar_Expr e1 e1' ->
                        Desugar_Expr e2 e2' ->
                        Desugar_Expr (Sub e1 e2) (@KOp _ bns_data (OpSub) [e1'; e2'])
       |dsg_Mul      : forall e1 e2 e1' e2', 
                        Desugar_Expr e1 e1' -> 
                        Desugar_Expr e2 e2' ->
                        Desugar_Expr (Mul e1 e2) (@KOp _ bns_data (OpMul) [e1'; e2']) 
       |dsg_Concat   : forall e1 e2 e1' e2', 
                        Desugar_Expr e1 e1' ->
                        Desugar_Expr e2 e2' ->
                        Desugar_Expr (Concat e1 e2) (@KOp _ bns_data (OpConcat) [e1'; e2'])  
       |dsg_Equal    : forall e1 e2 e1' e2',
                        Desugar_Expr e1 e1' ->
                        Desugar_Expr e2 e2' ->
                        Desugar_Expr (Equal e1 e2) (@KOp _ bns_data (OpEq) [e1'; e2'])                        
       |dsg_Lam      : forall lp lp' e e',  
                        Forall2 Desugar_Pat lp lp' ->       
                        Desugar_Expr e e' -> 
                        Desugar_Expr (Lam lp e) (from_lispat_to_lam lp' e')
       |dsg_App      : forall l l' e e', 
                        Desugar_Expr e e' -> 
                        Forall2 Desugar_Expr l l' ->
                        Desugar_Expr (App e l) (KApp (from_lisargs_to_napp (rev l') e') KUnit) 
       |dsg_Tup      : forall l l',  
                        Forall2 Desugar_Expr l l' ->
                        Desugar_Expr (Tup l) (from_lisexpr_to_tup l')
       |dsg_Nil      : Desugar_Expr Nil KNil
       |dsg_Cons     : forall head head' tail tail',  
                        Desugar_Expr head head' ->
                        Desugar_Expr tail tail' ->
                        Desugar_Expr (Cons head tail) (KCons head' tail') 
       |dsg_Variant  : forall c l l',   
                        Forall2 Desugar_Expr l l' -> 
                        Desugar_Expr (EVariant c l) (KVariant c (from_lisexpr_to_tup l'))
       |dsg_Let      : forall p p' e1 e2 e1' e2',
                        Desugar_Pat p p' -> 
                        Desugar_Expr e1 e1' ->
                        Desugar_Expr e2 e2' -> 
                        Desugar_Expr (ELet p e1 e2) (KApp (KLam p' e2') e1') 
       |dsg_If       : forall e1 e2 e3 e1' e2' e3',  
                        Desugar_Expr e1 e1' ->
                        Desugar_Expr e2 e2' ->
                        Desugar_Expr e3 e3' ->
                        Desugar_Expr (If e1 e2 e3) (
                            KMatch e1' [
                            (@KPLit _ bns_data (VlBool true), e2'); 
                            (@KPLit _ bns_data (VlBool false), e3')
                            ])
       |dsg_LetRec   :  forall i e1 e2 e1' e2', 
                         Desugar_Expr e1 e1' -> 
                         Desugar_Expr e2 e2' -> 
                         Desugar_Expr (LetRec i e1 e2) (KApp (KLam (KPVar i) e2') (KFix i e1'))
       |dsg_DefType  :  forall l l' e e', 
                         Forall2 (fun p q =>
                            fst p = fst q /\ Desugar_Tp (snd p) (snd q)) l l' ->
                         Desugar_Expr e e' -> 
                         Desugar_Expr (DefType l e) (KDefType l' e')
       |dsg_Match    :  forall l l' e e', 
                         Desugar_Expr e e' ->
                         Forall2 (fun p q =>
                            Desugar_Pat (fst p) (fst q) /\ Desugar_Expr (snd p) (snd q)) l l' -> 
                         Desugar_Expr (Match e l) (KMatch e' l')
       |dsg_Error   :  forall m, Desugar_Expr (EError m) (KError m) .
       
       
       
  (* 3.3. induction principle for Desugar_Expr proposition *)
  Section Desugar_Expr_ind'.  

        Variable P  : Expr I -> KExpr I bns_data -> Prop. 
        Hypothesis Var_case       : forall i, P (Var i) (KVar i).
        Hypothesis Bool_case      : forall b, P (Bool b) (@KLit _ bns_data (VlBool b)).
        Hypothesis Nat_case       : forall n, P (Nat n) (@KLit _ bns_data (VlNat n)). 
        Hypothesis String_case    : forall s, P (EString s) (@KLit _ bns_data (VlString s)).
        Hypothesis Not_case       : forall e e', P e e' -> P (Not e) (@KOp _ bns_data OpNot [e']).
        Hypothesis And_case       : forall e1 e2 e1' e2', 
                                      P e1 e1' -> 
                                      P e2 e2' -> 
                                      P (And e1 e2) (@KOp _ bns_data OpAnd [e1'; e2']).
        Hypothesis Or_case       : forall e1 e2 e1' e2', 
                                      P e1 e1' -> 
                                      P e2 e2' -> 
                                      P (Or e1 e2) (@KOp _ bns_data OpOr [e1'; e2']).
        Hypothesis Sum_case       : forall e1 e2 e1' e2', 
                                      P e1 e1' -> 
                                      P e2 e2' ->
                                      P (Sum e1 e2) (@KOp _ bns_data OpSum [e1'; e2']).
        Hypothesis Sub_case       : forall e1 e2 e1' e2', 
                                      P e1 e1' -> 
                                      P e2 e2' -> 
                                      P (Sub e1 e2) (@KOp _ bns_data OpSub [e1'; e2']).
        Hypothesis Mul_case       : forall e1 e2 e1' e2', 
                                      P e1 e1' -> 
                                      P e2 e2' -> 
                                      P (Mul e1 e2) (@KOp _ bns_data OpMul [e1'; e2']).
        Hypothesis Concat_case    : forall e1 e2 e1' e2', 
                                      P e1 e1' -> 
                                      P e2 e2' -> 
                                      P (Concat e1 e2) (@KOp _ bns_data OpConcat [e1'; e2']).
        Hypothesis Eq_case        : forall e1 e2 e1' e2', 
                                      P e1 e1' -> 
                                      P e2 e2' -> 
                                      P (Equal e1 e2) (@KOp _ bns_data OpEq [e1'; e2']).
        Hypothesis Lam_case       : forall lp lp' e e', 
                                      Forall2 Desugar_Pat lp lp' -> 
                                      P e e' -> 
                                      P (Lam lp e) (from_lispat_to_lam lp' e') .
        Hypothesis App_case       : forall e e' l l', 
                                      P e e' -> 
                                      Forall2 P l l' ->
                                      P (App e l) (KApp (from_lisargs_to_napp (rev l') e') KUnit).
        Hypothesis Tup_case       : forall l l', 
                                      Forall2 P l l' -> 
                                      P (Tup l) (from_lisexpr_to_tup l').
        Hypothesis Nil_case       : P Nil KNil.
        Hypothesis Cons_case      : forall head head' tail tail', 
                                      P head head' ->
                                      P tail tail' ->  
                                      P (Cons head tail) (KCons head' tail').       
        Hypothesis Variant_case  : forall c l l', 
                                      Forall2 P l l' -> 
                                      P (EVariant c l) (KVariant c (from_lisexpr_to_tup l')). 
        Hypothesis ELet_case      : forall p p' e1 e1' e2 e2', 
                                      Desugar_Pat p p' -> 
                                      P e1 e1' -> 
                                      P e2 e2' -> 
                                      P (ELet p e1 e2) (KApp (KLam p' e2') e1').
        Hypothesis If_case        : forall e1 e1' e2 e2' e3 e3', 
                                      P e1 e1' -> 
                                      P e2 e2' -> 
                                      P e3 e3' -> 
                                      P (If e1 e2 e3) (KMatch e1' [
                                                      (@KPLit _ bns_data (VlBool true), (e2')); 
                                                      (@KPLit _ bns_data (VlBool false), (e3'))]).
        Hypothesis LetRec_case    : forall i e1 e1' e2 e2', 
                                      P e1 e1' -> 
                                      P e2 e2' -> 
                                      P (LetRec i e1 e2) (KApp (KLam (KPVar i) e2') (KFix i e1')). 
        Hypothesis DefType_case   : forall l l' e e',  
                                      Forall2 (fun p q => fst p = fst q /\ Desugar_Tp (snd p) (snd q)) l l' -> 
                                      P e e' -> 
                                      P (DefType l e) (KDefType l' e'). 
        Hypothesis Match_case     : forall e e' l l', 
                                      P e e' -> 
                                      Forall2 (fun p q => Desugar_Pat (fst p) (fst q) /\ P (snd p) (snd q)) l l' -> 
                                      P (Match e l) (KMatch e' l').
        Hypothesis Error_case     : forall m, P (EError m) (KError m).
        
        Fixpoint Desugar_Expr_ind' (e: Expr I) (e': KExpr I bns_data) (H: Desugar_Expr e e') 
                                    : P e e' := 
                match H with 
                |dsg_Var                  => Var_case 
                |dsg_Bool                 => Bool_case  
                |dsg_Nat                  => Nat_case  
                |dsg_String               => String_case 
                |dsg_Not Hp               => Not_case (Desugar_Expr_ind' Hp) 
                |dsg_And Hp1 Hp2          => And_case (Desugar_Expr_ind' Hp1) 
                                                      (Desugar_Expr_ind' Hp2)
                |dsg_Or Hp1 Hp2           => Or_case (Desugar_Expr_ind' Hp1)
                                                     (Desugar_Expr_ind' Hp2) 
                |dsg_Sum Hp1 Hp2          => Sum_case (Desugar_Expr_ind' Hp1) 
                                                      (Desugar_Expr_ind' Hp2)
                |dsg_Sub Hp1 Hp2          => Sub_case (Desugar_Expr_ind' Hp1) 
                                                      (Desugar_Expr_ind' Hp2) 
                |dsg_Mul Hp1 Hp2          => Mul_case (Desugar_Expr_ind' Hp1) 
                                                      (Desugar_Expr_ind' Hp2)
                |dsg_Concat Hp1 Hp2       => Concat_case (Desugar_Expr_ind' Hp1) 
                                                         (Desugar_Expr_ind' Hp2)
                |dsg_Equal Hp1 Hp2        => Eq_case (Desugar_Expr_ind' Hp1) 
                                                     (Desugar_Expr_ind' Hp2)
                |dsg_Lam Hp1 Hp2          => Lam_case Hp1 (Desugar_Expr_ind' Hp2)   
                |dsg_App Hp1 Hp2          => App_case (Desugar_Expr_ind' Hp1)
                      ((fix lis_exp_ind' l l' (H: Forall2 Desugar_Expr l l') 
                                              : Forall2 P l l' := 
                              match H with 
                              |Forall2_nil _            => Forall2_nil _ 
                              |Forall2_cons _ _ Hhp Htp => Forall2_cons _ _ (Desugar_Expr_ind' Hhp)  
                                                                            (lis_exp_ind' _ _ Htp) 
                              end) _ _ Hp2)
                |dsg_Tup Hp                                 => Tup_case  
                      ((fix lis_exp_ind' l l' (H: Forall2 Desugar_Expr l l') 
                                              : Forall2 P l l' := 
                              match H with 
                              |Forall2_nil _            => Forall2_nil _ 
                              |Forall2_cons _ _ Hhp Htp => Forall2_cons _ _ (Desugar_Expr_ind' Hhp)  
                                                                            (lis_exp_ind' _ _ Htp) 
                              end) _ _ Hp)
                |dsg_Nil                  => Nil_case
                |dsg_Cons Hp1 Hp2         => Cons_case (Desugar_Expr_ind' Hp1) 
                                                       (Desugar_Expr_ind' Hp2)   
                |dsg_Variant Hp           => Variant_case 
                      ((fix lis_exp_ind l l' (H: Forall2 Desugar_Expr l l') 
                                             : Forall2 P l l' := 
                              match H with 
                              |Forall2_nil _            => Forall2_nil _ 
                              |Forall2_cons _ _ Hhp Htp => Forall2_cons _ _ (Desugar_Expr_ind' Hhp)  
                                                                            (lis_exp_ind _ _ Htp) 
                              end) _ _ Hp)
                |dsg_Let Hp1 Hp2 Hp3      => ELet_case Hp1 (Desugar_Expr_ind' Hp2)
                                                           (Desugar_Expr_ind' Hp3)

                |dsg_If Hp1 Hp2 Hp3       => If_case (Desugar_Expr_ind' Hp1)
                                                     (Desugar_Expr_ind' Hp2)
                                                     (Desugar_Expr_ind' Hp3)    
                |dsg_LetRec Hp1 Hp2       => LetRec_case (Desugar_Expr_ind' Hp1)
                                                         (Desugar_Expr_ind' Hp2)   
                |dsg_DefType Hp1 Hp2      => DefType_case Hp1 (Desugar_Expr_ind' Hp2)
                |dsg_Match Hp1 Hp2        => Match_case (Desugar_Expr_ind' Hp1)
                      ((fix lis_exp_ind' l l' 
                            (H: Forall2 (fun p q => Desugar_Pat (fst p) (fst q) /\ Desugar_Expr (snd p) (snd q)) l l')
                            : Forall2 (fun p q => Desugar_Pat (fst p) (fst q) /\ P (snd p) (snd q)) l l' := 
                        match H with 
                        |Forall2_nil _  => Forall2_nil _ 
                        |Forall2_cons _ _ Hph Hpt =>   
                              @Forall2_cons _ _ (fun p q => Desugar_Pat (fst p) (fst q) /\ P (snd p) (snd q)) _ _ _ _ 
                              (match Hph with 
                              |conj A B =>  conj A (Desugar_Expr_ind' B) end) 
                              (lis_exp_ind' _ _ Hpt)  
                                                          
                              end ) _ _ Hp2) 
                |dsg_Error                                  => Error_case  
                                  
                end.

  End Desugar_Expr_ind'.



       (* 3.4. function for expression desugaring *)
       Fixpoint desugar_Expr (e: Expr I) : KExpr I bns_data := 
              match e with 
              |Var i               => KVar i 
              |Bool b              => @KLit _ bns_data (VlBool b)
              |Nat n               => @KLit _ bns_data (VlNat n)
              |EString s           => @KLit _ bns_data (VlString s)
              |Not e               => @KOp _ bns_data (OpNot) [desugar_Expr e]
              |And e1 e2           => @KOp _ bns_data (OpAnd) [desugar_Expr e1; desugar_Expr e2]
              |Or e1 e2            => @KOp _ bns_data (OpOr) [desugar_Expr e1; desugar_Expr e2]
              |Sum e1 e2           => @KOp _ bns_data (OpSum) [desugar_Expr e1; desugar_Expr e2]
              |Sub e1 e2           => @KOp _ bns_data (OpSub) [desugar_Expr e1; desugar_Expr e2]
              |Mul e1 e2           => @KOp _ bns_data (OpMul) [desugar_Expr e1; desugar_Expr e2]
              |Concat e1 e2        => @KOp _ bns_data (OpConcat) [desugar_Expr e1; desugar_Expr e2]
              |Equal e1 e2         => @KOp _ bns_data (OpEq) [desugar_Expr e1; desugar_Expr e2] 
              |Lam l e             => from_lispat_to_lam (map desugar_Pat l) (desugar_Expr e)
              |App e l             => KApp (from_lisargs_to_napp (rev (map desugar_Expr l)) (desugar_Expr e)) KUnit
              |Tup l               => from_lisexpr_to_tup (map desugar_Expr l)
              |Nil                 => KNil
              |Cons head tail      => KCons (desugar_Expr head) (desugar_Expr tail)
              |EVariant c l        => KVariant c (from_lisexpr_to_tup (map desugar_Expr l))
              |ELet p e1 e2        => KApp (KLam (desugar_Pat p) (desugar_Expr e2)) (desugar_Expr e1)
              |If e1 e2 e3         => KMatch (desugar_Expr e1) [
                                          (@KPLit _ bns_data (VlBool true), (desugar_Expr e2)); 
                                          (@KPLit _ bns_data (VlBool false), (desugar_Expr e3))] 
              |LetRec i e1 e2      => KApp (KLam (KPVar i) (desugar_Expr e2)) (KFix i (desugar_Expr e1))
              |DefType l e         => KDefType (map (fun p => (fst p, desugar_Tp (snd p))) l) (desugar_Expr e) 
              |Match e l           => KMatch (desugar_Expr e) 
                                              (map (fun p => (desugar_Pat (fst p), desugar_Expr (snd p))) l)
              |EError m            => KError m
              end.
              
       

       (* 3.5. correctness of implementation for expression desugaring *)
       Theorem desugar_Expr_correct: forall e e', 
              desugar_Expr e = e' -> Desugar_Expr e e'. 
       Proof.
              intros e e' Hdesugar.
              generalize dependent e'. 
              induction e using Expr_ind'; intros;
              simpl in Hdesugar; subst;
              eauto using dsg_Var, dsg_Bool, dsg_Nat, dsg_String, dsg_Error; 
              eauto using dsg_Not, dsg_And, dsg_Or, dsg_Sub, dsg_Sum, dsg_Mul, 
                          dsg_Concat, dsg_Equal, dsg_Nil, dsg_Cons. 
              + apply dsg_Lam; eauto. 
                apply (Forall2P_eq_Forall2f _ (@desugar_Pat_eq_Desugar_Pat)). 
                apply forall2_eq_map; eauto. 

              + apply dsg_App; eauto. 
                induction l as [| h t IHt]. 
                - apply Forall2_nil. 
                - apply Forall2_cons; inversion H; subst; 
                  eauto.
              + apply dsg_Tup. 
                induction l as [| h t IHt]. 
                - apply Forall2_nil.
                - apply Forall2_cons; inversion H; subst; 
                  eauto.
              + apply dsg_Variant.  
                induction l as [| h t IHt]. 
                - apply Forall2_nil.  
                - apply Forall2_cons; inversion H; subst; 
                  eauto.
              + apply dsg_Let;
                try apply desugar_Pat_eq_Desugar_Pat; eauto.                   
              + apply dsg_If; eauto.
              + apply dsg_LetRec; eauto.
              + apply dsg_DefType; eauto.   
                induction l as [| h t IHt].
                - apply Forall2_nil.
                - apply Forall2_cons; eauto.
                  split; simpl;  
                  try apply desugar_Tp_eq_Desugar_Tp; 
                  eauto.   
              + apply dsg_Match; eauto.   
                induction l as [|h t IHt]. 
                - apply Forall2_nil. 
                - apply Forall2_cons; inversion H; subst; 
                  eauto;  
                  split; simpl; 
                  try apply desugar_Pat_eq_Desugar_Pat; 
                  eauto. 
 
       Qed.                  


       (* 3.6. completeness of implementation for expression desugaring *)
       Theorem desugar_Expr_complete: forall e e', 
          Desugar_Expr e e' -> desugar_Expr e = e' . 
       Proof.
              intros e e' HDesugar.
              induction HDesugar using Desugar_Expr_ind';
              simpl; subst;  
              repeat f_equal; 
              try apply forall2_eq_map; 
              try apply (Forall2P_eq_Forall2f _ (@desugar_Pat_eq_Desugar_Pat)); 
              try apply desugar_Pat_complete;
              eauto. 
              + induction H; subst. 
                - apply Forall2_nil. 
                - apply Forall2_cons; 
                  eauto. 
                  inversion H as [H1 H2]; subst. 
                  apply desugar_Tp_complete in H2.
                  rewrite H1, H2. 
                  destruct y; 
                  eauto.   
              + induction H; subst. 
                - apply Forall2_nil. 
                - apply Forall2_cons;
                  eauto.
                  inversion H as [H1 H2]; subst. 
                  apply desugar_Pat_complete in H1. 
                  rewrite H1, H2. 
                  destruct y; eauto. 
       Qed.

       
       Corollary desugar_Expr_eq_Desugar_Expr: forall e e', 
         Desugar_Expr e e' <-> desugar_Expr e = e'. 
       Proof. 
              split. 
              apply desugar_Expr_complete. 
              apply desugar_Expr_correct. 
       Qed. 
       
       

End Desugarer.



(* 

Eval compute in  desugar_Expr (

       DefType 
       
       ([("Nat", TVariant [
                     ("Z", TTup []); 
                     ("S", TTup [TRef "Nat"])])])  
       (LetRec "sum" 
              (Lam [PVar "x"; PVar "y"] 
                     (Match (Var "x") [(PVariant "Z" [], Var "y"); 
                                          (PVariant "S" [PVar "n"],
                                          App (Var "sum") [ Var "n" ; EVariant "S" [Var "y"] ])]))
              (App (Var "sum") [EVariant "Z" []; EVariant "S" [EVariant "Z" []]])))
       . 


Eval compute  in desugar_Expr (Reduce (Lam [PVar "x"; PVar "y"] (Sum (Var "x") (Var "y"))) 
                                   (Nat 0)
                                   [Cons [Nat 1; Nat 2; Nat 3; Nat 5]]).  *)
