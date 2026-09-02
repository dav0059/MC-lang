Require Import ids primitives kernel_syntax type_env env.
Require Import Lists.List Lists.ListDec. 
Import ListNotations. 
Open Scope bool_scope. 

Set Implicit Arguments . 
Set Contextual Implicit. 

Section TYPE_THEORY. 

    Context (I: IDS). 
    Context (P: PRIM_DATA). 

    Local Notation " 'Ide' " := (@Ide I). 
    Local Notation " 'KTp' " := (@KTp I P).
    Local Notation " 'Constr' " := (@Constr I).
    Local Notation " 'tenv' " := (@tenv I P).
     
   (* 1.1. function for deciding if a type is FOT (first order type). 
      A first order type T is a non-variant type without nested variants.*)
    Fixpoint is_FOT (t: KTp) : bool := 
       match t with 
       |KTFunction    => true  
       |KTBase _      => true 
       |KTUnit        => true  
       |KTEmpty       => true 
       |KTRef _       => true 
       |KTError       => true 
       |KTProd t1 t2  => is_FOT t1 && is_FOT t2 
       |KTList t      => is_FOT t 
       |_           => false 
       end.
    
    
    Section nodup.
        
        Variable X: Type.

        (* 1.2. *)
        Fixpoint nodupb (eqb: X -> X -> bool) 
                        (l: list X) : bool := 
          match l with 
          |[]   => true 
          |h::t => (match find (fun x => eqb x h) t with 
                    |None  => nodupb eqb t 
                    |Some _ => false 
                    end)
          end.
                    

        (* 1.3. nodupb is equivalent to the Stdlib logical characterization *)
        Lemma nodupb_eq_NoDup : forall (l: list X) eqb,
            (forall x y, Bool.reflect (x = y) (eqb x y)) ->
             NoDup l <-> nodupb eqb l = true.
        Proof.
            intros * Hrefl.
            split.
            + intros HNodup . 
              induction HNodup. 
              - eauto.
              - simpl. 
                destruct (find _) eqn: eqfind. 
                * apply find_some in eqfind. 
                  destruct eqfind as [eqIn eqdec].
                  apply (Bool.reflect_iff (x0 = x) (eqb x0 x)) in Hrefl.
                  rewrite <- Hrefl in eqdec.
                  rewrite eqdec in eqIn.
                  contradiction. 
                * eauto. 
            + intros Hnodup. 
              induction l. 
              - apply NoDup_nil. 
              - apply NoDup_cons; simpl in *;
                try apply IHl;
                destruct (find _) eqn: eqfind;    
                try discriminate; eauto;  
                unfold not; intros HIn;
                apply find_none with (x := a) in eqfind;
                apply (Bool.reflect_iff (a = a) (eqb a a)) in Hrefl; 
                assert (Id : a = a) by eauto;
                apply Hrefl in Id;
                rewrite Id in *; 
                try discriminate; eauto.
        Qed.

        Lemma In_false_nodupb: forall x l l' eqb, 
          (forall x y, Bool.reflect (x = y) (eqb x y)) -> 
           In x l ->
           In x l' -> 
           nodupb eqb (l ++ l') = false. 
        Proof.
          intros * Hrefl HInl HInl'. 
          generalize dependent l'. 
          induction l; intros; try contradiction.  
          simpl. destruct (find _) eqn: eqfind; eauto.
          simpl in HInl.  
          apply IHl; eauto. 
          destruct HInl; subst.
          + apply find_none with (x := x) in eqfind. 
            specialize Hrefl with x x.
            destruct Hrefl. discriminate. contradiction.
            apply in_or_app. right; eauto.
          + eauto.  
        Qed.

        Lemma nodupb_In_false: forall x l l' eqb,
          (forall x y, Bool.reflect (x = y) (eqb x y)) -> 
          nodupb eqb (l ++ l') = true -> 
          In x l -> 
          ~In x l'.  
        Proof. 
          intros * Hrefl Hnodupb HIn. 
          unfold not. 
          intros. 
          assert (contra: nodupb eqb (l ++ l') = false) by 
           (apply In_false_nodupb with (x := x); eauto).
          rewrite contra in Hnodupb; discriminate.
        Qed.  

        
    
    End nodup.
        
    (* The following definitions are parametrized on a global register R storing 
       the names of already declared types. It serves to solve types who are 
       references to other type, such as `Tref i`.   *)  
    Definition register := env Ide unit.   

    (* the canonical register associated to a type environment *)
    Definition accR (r: tenv) := 
     fold_right (fun '(i, _) acc => bind acc i tt (id_eqb I)) 
     (@empty_env Ide unit) r.
   
    (* 2.1. Admissible forms (AF) are algebraic data types with bound nominal references to 
       suport recursion. We exclude opaque types such as TFun, TError, the empty 
       type TEmpty who has no inhabitants, and all types obtained by their combination.*)
    Inductive AF (R: register) : KTp -> Prop := 
    |AF_TBase    : forall t, 
                    AF R (KTBase t)
    |AF_TUnit    : AF R KTUnit 
    |AF_TProd    : forall t1 t2,  
                    is_FOT t1 = true -> 
                    is_FOT t2 = true -> 
                    AF R t1 -> 
                    AF R t2 -> 
                    AF R (KTProd t1 t2)
    |AF_TList    : forall t,  
                    is_FOT t = true -> 
                    AF R t -> 
                    AF R (KTList t)
    |AF_TVariant : forall l,  
                    nodupb (constr_eqb I) (fst (split l)) = true ->
                    Forall (fun p => is_FOT (snd p) = true /\ AF R (snd p)) l ->  
                    AF R (KTVariant l)
    |AF_TRef     : forall i, 
                    includes R i = true ->  
                    AF R (KTRef i) .
    
                    
    (* 2.2. well-formed types (WF) extends AF including opaque types and the empty type *)
    Inductive WFT (R : register): KTp -> Prop :=
    |WFT_TFun     : WFT R KTFunction 
    |WFT_TBase    : forall t, WFT R (KTBase t)
    |WFT_TUnit    : WFT R KTUnit 
    |WFT_TEmpty   : WFT R KTEmpty 
    |WFT_TProd    : forall t1 t2,
                     is_FOT t1 = true -> 
                     is_FOT t2 = true -> 
                     WFT R t1 ->
                     WFT R t2 -> 
                     WFT R (KTProd t1 t2)
    |WFT_TList    : forall t,  
                     is_FOT t = true -> 
                     WFT R t -> 
                     WFT R (KTList t)
    |WFT_TVariant : forall l,  
                     nodupb (constr_eqb I) (fst (split l)) = true ->
                     Forall (fun p => is_FOT (snd p) = true /\ WFT R (snd p)) l ->  
                     WFT R (KTVariant l)
    |WFT_TRef     : forall i,  
                     includes R i = true -> 
                     WFT R (KTRef i)
    |WFT_TError   : WFT R KTError.

  
    (* 2.3. declarable types (DT) are only variant types formed by AF's *)
    Inductive DT (R : register) : KTp  -> Prop :=  
    |DT_TVariant : forall l, 
                    AF R (KTVariant l) ->  
                    DT R (KTVariant l) .


    (* 2.4. well-formed type environments *)
    Definition WFET (r: tenv) (R: register) := 
      (forall i, tdom r i <-> dom R i) /\ (forall t, timm r t -> DT R t). 
                    
    
            


    (* Induction principle for AF. *)
    Section AF_ind'. 

        Variable R: register.
        Variable Q: KTp -> Prop . 

        Hypothesis TBase_case    : forall t, Q (KTBase t) .
        Hypothesis TUnit_case    : Q KTUnit.   
        Hypothesis TProd_case    : forall t1 t2,  
                                      is_FOT t1 = true -> 
                                      is_FOT t2 = true -> 
                                      Q t1 -> 
                                      Q t2 -> 
                                      Q (KTProd t1 t2).
        Hypothesis TList_case    : forall t, 
                                      is_FOT t = true ->   
                                      Q t ->
                                      Q (KTList t). 
        Hypothesis TVariant_case : forall l,  
                                      nodupb (constr_eqb I) (fst (split l)) = true -> 
                                      Forall (fun p => is_FOT (snd p) = true /\ Q (snd p)) l -> 
                                      Q (KTVariant l).
        Hypothesis TRef_case     : forall i,
                                      includes R i = true ->  
                                      Q (KTRef i). 


        Fixpoint AF_ind' t (H: AF R t) : Q t := 
          match H with   
          |AF_TBase                              => TBase_case    
          |AF_TUnit                              => TUnit_case  
          |AF_TProd Hf1 Hf2 HAF1 HAF2            => TProd_case Hf1 Hf2 
                                                    (AF_ind' HAF1) (AF_ind' HAF2)
          |AF_TList Hf HAF                       => TList_case Hf (AF_ind' HAF) 
          |AF_TVariant Hnd Hfall                 => TVariant_case Hnd 
              ((fix lis_ind' l (H: Forall (fun p => is_FOT (snd p) = true /\ AF _ (snd p)) l): 
                                Forall (fun p => is_FOT (snd p) = true /\ Q (snd p)) l  := 
                  match H with 
                  |Forall_nil _                => Forall_nil _ 
                  |Forall_cons _ Hx Hxs => 
                      match Hx with 
                      |conj A B  => Forall_cons _ (conj A (AF_ind' B)) (lis_ind' _ Hxs) 
                      end 
                  end) _ Hfall) 
        |AF_TRef Hsome                           => TRef_case Hsome 
        end.
        
    End AF_ind'.
    
    
    
    (*3. consistency relation. It defines conditions under which we can assert 
         that two types are compatible. From a semantic point of view, the typechecking 
         will leverage the consistency relation for comparing types extracted from
         values against the types declared for these shaped values. *)     
    Inductive Consistent: KTp -> KTp -> Prop := 
    |c_TFun        : Consistent KTFunction KTFunction 
    |c_TBase       : forall t1 t2, 
                        t1 = t2 -> 
                        Consistent (KTBase t1) (KTBase t2) 
    |c_TUnit       : Consistent KTUnit KTUnit 
    |c_TEmpty      : Consistent KTEmpty KTEmpty  
    |c_TProd       : forall t1 t1' t2 t2', 
                        Consistent t1 t1' -> 
                        Consistent t2 t2' -> 
                        Consistent (KTProd t1 t2) (KTProd t1' t2')    
    |c_TList       : forall t t', 
                        Consistent t t' -> 
                        Consistent (KTList t) (KTList t')
    |c_TListNil1   : forall t,  
                        is_FOT t = true -> 
                        Consistent (KTList KTEmpty) (KTList t) 
    |c_TListNil2   : forall t,  
                        is_FOT t = true -> 
                        Consistent (KTList t) (KTList KTEmpty)
    |c_TRef        : forall i i',   
                        i = i' -> 
                        Consistent (KTRef i) (KTRef i') 
    |c_TError      : Consistent KTError KTError.
                        
                    

    (* 4.1. function for deciding if a type is an admissible form, assuming a well formed 
            type environment in input*) 
    Fixpoint is_AF (R: register) (t: KTp) :=  
      match t with 
      |KTBase t     => true 
      |KTUnit       => true 
      |KTProd t1 t2 => is_FOT t1 && is_FOT t2 && is_AF R t1 && is_AF R t2 
      |KTList t     => is_FOT t && is_AF R t 
      |KTVariant l  => nodupb (constr_eqb I) (fst (split l)) && 
                       forallb (fun p => is_FOT (snd p) && is_AF R (snd p)) l 
      |KTRef i      => includes R i
      |_            => false  
     end. 

    
    (* 4.2. function for deciding if a type is declarable *)
    Definition is_DT (R: register) (t: KTp) : bool := 
      match t with 
      |KTVariant l => is_AF R (KTVariant l) 
      |_          => false 
      end.
 

    (* 4.3. function for deciding if two types are consistent *)
     Fixpoint is_consistent  (t t': KTp ) : bool :=
       match t, t' with 
       |KTFunction, KTFunction        => true 
       |KTBase t, KTBase t'           => eqb_BaseTp P t t'
       |KTEmpty, KTEmpty              => true
       |KTUnit , KTUnit               => true 
       |KTProd t1 t2, KTProd t1' t2'  => is_consistent t1 t1' && is_consistent t2 t2' 
       |KTList KTEmpty, KTList t      => is_FOT t  
       |KTList t, KTList KTEmpty      => is_FOT t   
       |KTList t, KTList t'           => is_consistent t t' 
       |KTRef i, KTRef i'             => id_eqb I i i' 
       |KTError, KTError              => true 
       |_, _                          => false  
     end.


     (* 4.4 function for deciding if a type is a nested empty list type. 
            Empty list type is considered nested, the lowest grade of nesting 
            for that type. *)
     Fixpoint nested_empty (t : KTp) : bool := 
      match t with 
      |KTList KTEmpty => true 
      |KTList t       => nested_empty t 
      |_              => false 
      end.  

    (* common lemmas *)
      
     Lemma Forall_impl_forallb_AF1: forall R l, 
       Forall (fun p => is_FOT (snd p) = true /\ is_AF R (snd p) = true) l -> 
       forallb (fun p: Constr * KTp => is_FOT (snd p) && is_AF R (snd p)) l = true.
     Proof. 
        intros R l Hforall. 
        induction Hforall. 
        - eauto.
        - destruct H as [Hfot Himp]; simpl. 
          repeat rewrite Bool.andb_true_iff. 
          repeat split;
          eauto. 
      Qed. 


    
    Lemma Forall_impl_forallb_AF2: forall l R,
      (forall R t, AF R t <-> is_AF R t = true) -> 
      (Forall (fun p => is_FOT (snd p) = true /\ AF R (snd p)) l <-> 
      forallb (fun p: Constr * KTp => is_FOT (snd p) && is_AF R (snd p)) l = true).
    Proof. 
      intros l r HAfEqaf. 
      split.
      + intros HForall. 
        induction HForall. 
        - eauto.
        - simpl. 
          repeat rewrite Bool.andb_true_iff;
          repeat split; 
          rewrite HAfEqaf in H ;
          destruct H;   
          eauto.
      + intros Hforall. 
        induction l as [| h t Ht].
        - apply Forall_nil. 
        - apply Forall_cons; 
          simpl in Hforall;  
          repeat rewrite Bool.andb_true_iff in Hforall; 
          destruct Hforall as [[Hfot Haf] Hforall];
          rewrite <- HAfEqaf in Haf;
          try apply Ht; 
          eauto.
    Qed.    
      

    Lemma Forall_impl_forallb_DT: forall R l,  
      (forall R t, DT R t <-> is_DT R t = true) -> 
      (Forall (fun p: Ide * KTp => DT R (snd p)) l) <-> 
      forallb (fun p: Ide * KTp => is_DT R (snd p)) l = true.
    Proof.
      intros * Heq.
      split; intros. 
      + induction H. 
        ++ eauto.
        ++ simpl. rewrite Bool.andb_true_iff. 
           split; try apply Heq; eauto.
      + induction l. 
        ++ apply Forall_nil.
        ++ apply Forall_cons; inversion H; 
           rewrite Bool.andb_true_iff in H1; 
           destruct H1 as [Hdt Hforall];  
           try apply Heq; eauto.
    Qed.          

    
     Lemma NoDup_split: forall (h: Constr * KTp) t,
       NoDup (fst (split (h::t))) -> NoDup (fst (split t)).
    Proof. 
        intros h t HNoDup.
        inversion HNoDup as [contra | x l HIn HNodup eq]. 
        + destruct h. destruct t. 
          - simpl in contra. discriminate. 
          - destruct (split (p::t)). discriminate. 
        + destruct h. destruct (split t). 
          simpl in *; inversion eq; subst; eauto.   
     Qed. 
         
    

     Lemma isAF_TVariant_case_ind : forall R x l, 
       is_AF R (KTVariant (x::l)) = true -> 
       is_AF R (KTVariant l) = true.
      Proof. 
        intros. 
        simpl in H.
        repeat rewrite Bool.andb_true_iff in H.
        destruct H as [Hnodupb [_ Hforall]]. 
        generalize dependent x.
        induction l; intros. 
        - eauto.  
        - simpl in *.  
          repeat rewrite Bool.andb_true_iff; 
          repeat split;   
          repeat rewrite Bool.andb_true_iff in Hforall; 
          destruct Hforall as [[Hfot Haf] Hforall']; 
          eauto.
          rewrite <- nodupb_eq_NoDup. 
          rewrite <- nodupb_eq_NoDup in Hnodupb.
          * apply NoDup_split with (x) (a::l) in Hnodupb. 
            simpl in Hnodupb.
            eauto.
          * intros.
            apply (Bool.iff_reflect (x0 = y) (constr_eqb I x0 y)).
            apply constr_eqb_eq.
          * intros.
            apply (Bool.iff_reflect (x0 = y) (constr_eqb I x0 y)).
            apply constr_eqb_eq. 
      Qed.  
               
      
      Lemma is_consistent_list: forall t t', 
        is_consistent (KTList t) (KTList t') = true -> 
        t <> KTEmpty -> 
        t' <> KTEmpty -> 
        is_consistent t t' = true. 
      Proof. 
        intros t t' Hconst Hneq1 Hneq2. 
        simpl in Hconst. 
        generalize dependent t'.
        induction t; intros; 
        destruct t'; eauto.
      Qed.

    

     Theorem is_AF_correct : forall R t, 
      is_AF R t = true -> AF R t. 
     Proof. 
        intros R t Haf.  
        induction t using KTp_ind' ; 
        try discriminate. 
        + apply AF_TBase; eauto. 
        + apply AF_TUnit; eauto. 
        + inversion Haf as [conj]. 
          repeat rewrite Bool.andb_true_iff in conj.
          destruct conj as [[[Hfot1 Hfot2] Haft2] Haft1];  
          apply AF_TProd; eauto. 
        + inversion Haf as [conj]. 
          rewrite Bool.andb_true_iff in conj;
          destruct conj; apply AF_TList; eauto.
        + inversion Haf as [conj].  
          rewrite Bool.andb_true_iff in conj;   
          destruct conj as [Hnodup Hforall];
          apply AF_TVariant; eauto. 
          induction lis as [| h t Ht]. 
          ++ apply Forall_nil. 
          ++ apply Forall_cons; 
             inversion H as [|p l Haf_impl_Af HForall]; subst;
             simpl in Hforall; 
             repeat rewrite Bool.andb_true_iff in Hforall; 
             destruct Hforall as [[Hisfot Haf2] Hforall2]; 
             apply isAF_TVariant_case_ind in Haf; 
             rewrite <- nodupb_eq_NoDup in Hnodup;
             try apply NoDup_split in Hnodup;
             try apply Ht; 
             try rewrite <- nodupb_eq_NoDup;
             eauto; 
             intros; apply Bool.iff_reflect; apply constr_eqb_eq. 
          + apply AF_TRef; eauto.
     Qed.    

     Theorem is_AF_complete: forall R t, 
      (AF R t -> is_AF R t = true). 
     Proof. 
       intros R t HAf. 
       induction HAf using AF_ind'; eauto. 
       + simpl; 
           repeat rewrite Bool.andb_true_iff; 
           repeat split;  
           eauto. 
       + simpl; 
         rewrite Bool.andb_true_iff; 
         split; 
         eauto.  
       + simpl;
         rewrite Bool.andb_true_iff; 
         split; eauto.
         apply Forall_impl_forallb_AF1; 
         eauto.
     Qed.  

    Corollary is_AF_eq_AF : forall R t, 
     is_AF R t = true <-> AF R t.
    Proof. 
      split. 
      apply is_AF_correct.
      apply is_AF_complete.
    Qed. 

    Theorem is_DT_correct: forall R t, 
       is_DT R t = true -> DT R t. 
    Proof. 
      intros R t Hdt. 
      induction t using KTp_ind'; 
      try discriminate. 
      simpl in *. 
      rewrite Bool.andb_true_iff in Hdt. 
      destruct Hdt as [Hnodup Hforall]. 
      apply DT_TVariant; eauto;  
      apply AF_TVariant; eauto. 
      apply Forall_impl_forallb_AF2; eauto.
      split. 
      apply is_AF_complete; eauto. 
      apply is_AF_correct; eauto. 
    Qed. 


    Theorem is_DT_complete: forall R t, 
      DT R t -> is_DT R t = true. 
    Proof. 
      intros R t HDt. 
      inversion HDt; subst; 
      inversion H; subst;
      apply Forall_impl_forallb_AF2 in H2. 
      + simpl. rewrite Bool.andb_true_iff; eauto. 
      + split; intros.
        apply is_AF_complete; eauto.
        apply is_AF_correct; eauto.  
    Qed.    


    Corollary is_DT_eq_DT : forall R t, 
      is_DT R t = true <-> DT R t .
    Proof. 
      split. 
      apply is_DT_correct.
      apply is_DT_complete.
    Qed.

    
    Theorem is_consistent_correct: forall t t',  
      is_consistent t t' = true ->
      Consistent t t'. 
    Proof. 
      intros * Hc.
      generalize dependent t'. 
      induction t; intros;
      inversion Hc;
      destruct t'; 
      try discriminate ; 
      try (destruct t; discriminate).  
      + apply c_TFun.  
      + apply c_TBase. 
        assert (Bool.reflect (t = t0) (eqb_BaseTp P t t0)) 
         by (apply eqb_eq_BaseTp ).
        apply Bool.reflect_iff in H;
        apply H; eauto.
      + apply c_TUnit. 
      + apply c_TEmpty. 
      + apply c_TProd;
        rewrite Bool.andb_true_iff in H0;
        destruct H0; subst. 
        apply IHt1; eauto.
        apply IHt2; eauto. 
      + destruct t; 
        try (apply c_TListNil1; subst; eauto); 
        destruct t'; 
        try (apply c_TListNil2; subst; eauto); 
        try discriminate; 
        try (apply c_TList; subst; eauto); 
        apply IHt; inversion Hwft2; subst; eauto.
      + apply c_TRef.
        apply id_eqb_eq ; eauto.
      + apply c_TError; eauto. 
    Qed.   


    Theorem is_consistent_complete: forall t t',  
      Consistent t t' -> 
      is_consistent t t' = true. 
    Proof. 
      intros * HC.
      induction HC;  
      eauto; 
      simpl. 
      + assert (Bool.reflect (t1 = t2) (eqb_BaseTp P t1 t2)) by (apply eqb_eq_BaseTp).
        apply Bool.reflect_iff in H0; apply H0; eauto.  
      + rewrite Bool.andb_true_iff; eauto. 
      + destruct t; destruct t'; 
        eauto; 
        try inversion HC; subst;   
        subst; eauto.   
      + destruct t; eauto. 
      + subst . apply id_eqb_eq;  eauto.  
    Qed.



    (* USEFUL PROPERTIES of CONSISTENT RELATION *)

    Theorem consistent_eq_tempty: forall t, 
      Consistent t KTEmpty <-> t = KTEmpty. 
      Proof. 
        split; intros H;
        inversion H; subst; eauto; apply c_TEmpty.
      Qed.

    Theorem consistent_refl: forall t, 
      is_FOT t = true -> Consistent t t .
    Proof. 
      intros * Hfot. 
      induction t. 
      + apply c_TFun. 
      + apply c_TBase; eauto.
      + apply c_TUnit.
      + apply c_TEmpty.
      + apply c_TProd; simpl in Hfot; 
        rewrite Bool.andb_true_iff in Hfot;
        destruct Hfot; eauto.
      + apply c_TList; simpl in Hfot; eauto.
      + simpl in Hfot; discriminate.
      + apply c_TRef. eauto. 
      + apply c_TError. 
    Qed.
    
    Theorem consistent_sym : forall t t', 
      Consistent t t' -> Consistent t' t. 
    Proof. 
      intros * HC. 
      induction HC. 
      + apply c_TFun.
      + apply c_TBase. symmetry; eauto.
      + apply c_TUnit. 
      + apply c_TEmpty. 
      + apply c_TProd; eauto.
      + apply c_TList; eauto.
      + apply c_TListNil2; eauto.
      + apply c_TListNil1; eauto.
      + apply c_TRef; eauto.
      + apply c_TError. 
    Qed. 



    Theorem consistent_is_FOT: forall t t',  
      Consistent t t' -> 
      is_FOT t = true /\ is_FOT t' = true. 
    Proof. 
      intros * HC . 
      induction HC; eauto; 
      destruct IHHC1, IHHC2;
      split; simpl; rewrite Bool.andb_true_iff; 
      split; eauto. 
    Qed.



(* Here I need something powerful than nested_empty function. 
   I need a structural nested_empty function checking if some 
   nested_empty occurs in the type structure inspected. *)
    (* Theorem fnested_consistent_eq: forall t t', 
       nested_empty t = false -> 
       nested_empty t' = false ->
       Consistent t t' -> 
       t = t'. 
    Proof. 
      intros * Hne1 Hne2 HC. 
      inversion HC; subst; eauto. 
      + subst. eauto. 
      + subst; f_equal; eauto. try discriminate. simpl in *.  
         *)


    
          
End TYPE_THEORY. 






     






