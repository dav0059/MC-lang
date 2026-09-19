Require Import ids.
Require Import primitives. 
Require Import kernel_syntax.
Require Import type_env. 
Require Import env.
Require Import Lists.List Lists.ListDec. 
Require Import Bool.
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

    Ltac discard_case := 
      try (simpl in *; discriminate).

    Ltac solve_base := 
      try constructor; eauto.  
     
   (* function for deciding if a type is a first order type (FOT). 
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
       |_             => false 
       end.
    
    
    (* formalization of behaviour of nodupb auxiliary function *)
    Section nodup.
        
        Variable X: Type.

        (* decides if a list has no duplicates *)
        Fixpoint nodupb (eqb: X -> X -> bool) 
                        (l: list X) : bool := 
          match l with 
          |[]   => true 
          |h::t => match find (fun x => eqb x h) t with 
                    |None  => nodupb eqb t 
                    |Some _ => false 
                    end
          end.
                    
        (* nodupb is equivalent to the Stdlib logical characterization *)
        Lemma nodupb_eq_NoDup : forall (l: list X) eqb,
            (forall x y, reflect (x = y) (eqb x y)) ->
             NoDup l <-> nodupb eqb l = true.
        Proof.
            intros * Hrefl. split.
            (* -> *)
            + intros HNodup. induction HNodup; eauto.
              simpl. destruct (find _) eqn: eqfind; eauto. 
              apply find_some in eqfind. 
              destruct eqfind as [eqIn eqdec].
              apply (Bool.reflect_iff (x0 = x) (eqb x0 x)) in Hrefl.
              rewrite <- Hrefl in eqdec; subst.
              contradiction. 
            (* <- *)
            + intros Hnodup. induction l as [| head tail].
              (* l := [] *)
              - apply NoDup_nil.
              (* l := head::tail *)
              - apply NoDup_cons; simpl in *;
                destruct (find _) eqn: eqfind;     
                try discriminate; eauto.
                unfold not; intros HIn.
                apply find_none with (x := head) in eqfind; eauto.
                apply (Bool.reflect_iff (head = head) 
                       (eqb head head)) in Hrefl.  
                assert (H: head = head) by eauto. 
                apply Hrefl in H. rewrite H in *. discriminate. 
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
          simpl in HInl. apply IHl; eauto. 
          destruct HInl; eauto. subst.
          apply find_none with (x := x) in eqfind. 
          specialize Hrefl with x x.
          destruct Hrefl. discriminate. contradiction.
          apply in_or_app. right; eauto.
        Qed.


        Corollary nodupb_In_false: forall x l l' eqb,
          (forall x y, Bool.reflect (x = y) (eqb x y)) -> 
          nodupb eqb (l ++ l') = true -> 
          In x l -> 
          ~In x l'.  
        Proof. 
          intros * Hrefl Hnodupb HIn. 
          unfold not. intros. 
          assert (contra: nodupb eqb (l ++ l') = false) by 
           (apply In_false_nodupb with (x := x); eauto).
          rewrite contra in Hnodupb; discriminate.
        Qed.  


        Lemma nodupb_remove_r: forall l l' eqb, 
         (forall x y, Bool.reflect (x = y) (eqb x y)) ->
         nodupb eqb (l ++ l') = true -> 
         nodupb eqb l = true.
        Proof. 
          intros * Hrefl Hnodupb. 
          apply nodupb_eq_NoDup; eauto. 
          eapply NoDup_app_remove_r.
          eapply nodupb_eq_NoDup; eauto.
        Qed.

        Lemma nodupb_remove_l: forall l l' eqb, 
         (forall x y, Bool.reflect (x = y) (eqb x y)) ->
         nodupb eqb (l ++ l') = true -> 
         nodupb eqb l' = true.
        Proof. 
          intros * Hrefl Hnodupb. 
          apply nodupb_eq_NoDup; eauto. 
          eapply NoDup_app_remove_l.
          eapply nodupb_eq_NoDup; eauto.
        Qed.
           
    
    End nodup.

        
    (* The following inductive definitions are parametrized on a 
       global register R storing the names of already declared types. 
       It serves to solve types who are references to other type, 
       such as `Tref i`.   *)     
    Definition register := env Ide unit.   
(* 
    (* the canonical register associated to a type environment *)
    Definition accR (r: tenv) := 
     fold_right (fun '(i, _) acc => bind acc i tt (id_eqb I)) 
     (@empty_env Ide unit) r. *)
   
    (* Admissible forms (AF) are algebraic data types with bound
       nominal references to suport recursion. They don't allow 
       nesting variant types. We exclude opaque types such as
       TFun, TError, the empty type TEmpty who has no inhabitants, 
       and all types obtained by their combination.*)
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
                    Forall (fun p => 
                       is_FOT (snd p) = true /\ 
                       AF R (snd p)) l ->  
                    AF R (KTVariant l)
    |AF_TRef     : forall i, 
                    includes R i = true ->  
                    AF R (KTRef i) .
    
                    
    (* well-formed types (WFT) extends AF including opaque types
       and the empty type *)
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

  
    (* declarable types (DT) are only variant types formed by AF's *)
    Inductive DT (R : register) : KTp  -> Prop :=  
    |DT_TVariant : forall l, 
                    AF R (KTVariant l) ->  
                    DT R (KTVariant l) .


    (* well-formed type environments and registers: 
       Notice that the image of the env is just the set of types
       actually reachable by the lookup function, not the set of
       all stored types. *)
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
              ((fix lis_ind' l  
                    (H: Forall (fun p => is_FOT (snd p) = true /\
                                      AF _ (snd p)) l) : 
                     Forall (fun p => is_FOT (snd p) = true /\ 
                                       Q (snd p)) l  := 
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
    
    
    
    (* The consistency relation defines conditions under which we can assert 
       that two types are compatible. Only first order types can be compared
       by this relation. From a semantic point of view, the typechecking 
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
                        
                    


    (* decidable computable functions for the previous logical 
      definitions: AF, DT, Consistent *)

    Definition isAF := bool . 
    Definition isFOT := bool. 
    Definition isAF_and_isFOT: Type := isAF * isFOT.  

    Fixpoint is_AF_aux (R: register) (t: KTp) : isAF_and_isFOT :=  
      match t with 
      |KTBase t     => (true, true) 
      |KTUnit       => (true, true) 
      |KTProd t1 t2 => let '(af1, fot1) := is_AF_aux R t1 in 
                       let '(af2, fot2) := is_AF_aux R t2 in 
                       if fot1 && fot2 then (af1 && af2, true)
                       else (false, false)
      |KTList t     => let '(af, fot) := is_AF_aux R t in 
                       (fot && af, fot)  
      |KTVariant l  => if nodupb (constr_eqb I) (fst (split l)) && 
                          forallb (fun p => 
                             let '(af, fot) := is_AF_aux R (snd p) in 
                             af && fot) l 
                        then (true, false)
                        else (false, false) 
      |KTRef i      => (includes R i, true)
      |_            => (false, true)  
     end. 

    
    Definition is_AF (R: register) (t: KTp) : bool := 
      match t with 
      |KTVariant _  => fst (is_AF_aux R t) 
      |_            => let '(af, fot) := is_AF_aux R t in 
                        af && fot  
      end.  


    Definition is_DT (R: register) (t: KTp) : bool := 
      match t with 
      |KTVariant l => is_AF R (KTVariant l) 
      |_          => false 
      end.
 

     Fixpoint is_consistent  (t t': KTp ) : bool :=
       match t, t' with 
       |KTFunction, KTFunction        => true 
       |KTBase t, KTBase t'           => eqb_BaseTp P t t'
       |KTEmpty, KTEmpty              => true
       |KTUnit , KTUnit               => true 
       |KTProd t1 t2, KTProd t1' t2'  => is_consistent t1 t1' && 
                                         is_consistent t2 t2' 
       |KTList KTEmpty, KTList t      => is_FOT t  
       |KTList t, KTList KTEmpty      => is_FOT t   
       |KTList t, KTList t'           => is_consistent t t' 
       |KTRef i, KTRef i'             => id_eqb I i i' 
       |KTError, KTError              => true 
       |_, _                          => false  
     end.


     (* function for deciding if a type is a nested empty list type. 
        Empty list type is considered nested, the lowest grade of nesting 
        for that type. *)
     Fixpoint nested_empty (t : KTp) : bool := 
      match t with 
      |KTList KTEmpty => true 
      |KTList t       => nested_empty t 
      |_              => false 
      end.  



     Lemma is_AF_aux_snd_is_FOT: forall R t, 
       snd (is_AF_aux R t) = true <-> is_FOT t = true.
     Proof. 
       split. 
       + intros Hsnd. induction t; solve_base. 
         (* t := KTProd t1 t2 *)
         * simpl in *. destruct (is_AF_aux R t1), 
           (is_AF_aux R t2), i0, i2; try discriminate. 
           simpl in *. rewrite andb_true_iff in *; 
           split; eauto.
         (* t := KTList t' *)
         * simpl in *. destruct (is_AF_aux _). eauto.   
          (* t := KTVariant tags *)
         * simpl in Hsnd. destruct (nodupb _), (forallb _); 
           discard_case.
       + intro Hfot. induction t; solve_base; discard_case. 
        (* t := KTProd t1 t2 *)
         * simpl in *. destruct (is_AF_aux R t1), 
           (is_AF_aux R t2), i0, i2; 
           rewrite andb_true_iff in Hfot; 
           destruct Hfot; simpl; eauto.
        (* t := KTList t' *)
         * simpl in *. destruct (is_AF_aux _). eauto.    
      Qed.     


     Lemma is_AF_aux_fst_AF_Ind : forall R (lis: list (Constr * KTp)),
       Forall (fun p => 
        fst (is_AF_aux R (snd p)) = true -> 
        AF R (snd p)) lis -> 
       forallb (fun p => 
          let '(af, fot) := is_AF_aux R (snd p) in 
          af && fot) lis = true ->  
       Forall (fun p =>  
         is_FOT (snd p) = true /\ 
         AF R (snd p)) lis.   
      Proof.
        intros * Hind Hfall. induction Hind. solve_base.
        apply Forall_cons; simpl in Hfall;
        rewrite andb_true_iff in Hfall;
        destruct Hfall as [Hlet Hfall]; eauto.
        destruct (is_AF_aux R (snd x)) eqn: eqaf.
        rewrite andb_true_iff in Hlet; 
        destruct Hlet; subst. split.
        (* Goal: is_FOT (snd a) = true *)
        * eapply is_AF_aux_snd_is_FOT. 
          rewrite eqaf. eauto.
        (* Goal: AF R (snd a) *)
        * eauto.  
      Qed.  
          

     Lemma is_AF_aux_fst_AF_Ind2: forall R (l: list(Constr * KTp)), 
       Forall (fun p => 
         is_FOT (snd p) = true /\ 
         fst (is_AF_aux R (snd p)) = true) l ->
       forallb (fun p => 
         let '(af, fot) := is_AF_aux R (snd p) in  
           af && fot) l = true .
      Proof. 
        intros * HFall. induction HFall; solve_base.
        destruct H as [Hfot Haf]. simpl. 
        eapply is_AF_aux_snd_is_FOT in Hfot. 
        destruct (is_AF_aux R (snd x)) eqn: eqaf.
        rewrite eqaf in Hfot. simpl in *; subst. eauto.
      Qed. 
 
      
     Lemma is_AF_aux_fst_AF : forall R t, 
       fst (is_AF_aux R t) = true <-> AF R t.
     Proof.
       split.
      (* -> *)
       + intro Hfst. induction t using KTp_ind'; 
         discard_case.
         (* t := KTBase t *)
         * constructor.
         (* t := KTUnit *)
         * constructor.
         (* t := KTProd t1 t2 *)
         * simpl in Hfst. destruct (is_AF_aux R t1) eqn: eq1, 
           (is_AF_aux R t2) eqn: eq2, i0, i2; try discriminate.
           assert (H1: snd (is_AF_aux R t1) = true) 
            by (rewrite eq1; eauto);
           assert (H2: snd (is_AF_aux R t2) = true)
            by (rewrite eq2; eauto); 
           rewrite is_AF_aux_snd_is_FOT in H1, H2;
           simpl in *; rewrite andb_true_iff in Hfst;
           destruct Hfst; constructor; eauto.
         (* t := KTList t *)
         * simpl in Hfst. destruct (is_AF_aux _) eqn: eqt; 
           simpl in Hfst; rewrite andb_true_iff in Hfst;
           destruct Hfst. constructor; eauto.
           subst. eapply is_AF_aux_snd_is_FOT. 
           rewrite eqt. eauto. 
         (* t := KTVariant l *)
         * simpl in Hfst. destruct (nodupb _) eqn: eqnd, 
           (forallb _) eqn: eqfb; try discriminate.
           constructor; eauto. 
           eapply is_AF_aux_fst_AF_Ind; eauto.
         (* t := KTRef i *)
         * constructor; eauto.
      (* <- *)
       + intros HAf. induction HAf using AF_ind'; 
         solve_base.
         (* AF R (KTProd t1 t2) *)
         * eapply is_AF_aux_snd_is_FOT in H, H0.
           simpl. destruct (is_AF_aux R t1) eqn: eqaf1, 
           (is_AF_aux R t2) eqn: eqaf2. simpl in *. subst.
           rewrite eqaf1 in H; rewrite eqaf2 in H0. 
           simpl in *. subst. eauto.
          (* AF R (KTList t) *)
         * eapply is_AF_aux_snd_is_FOT in H. simpl.
           destruct (is_AF_aux R t) eqn: eqaf.
           rewrite eqaf in H. simpl in *. subst. eauto.
          (* AF R (KTVAriant l) *)
         * eapply is_AF_aux_fst_AF_Ind2 in H0.  
           simpl. rewrite H, H0. eauto. 
     Qed.      
             
            
     Lemma AF_is_AF_Ind: forall R (l: list (Constr * KTp)), 
       nodupb (constr_eqb I) (fst (split l)) = true ->
       Forall (fun p => 
        is_FOT (snd p) = true /\ 
        is_AF R (snd p) = true) l ->
       is_AF R (KTVariant l) = true.
     Proof. 
       intros * Hnd HAf. induction HAf; solve_base.
       simpl in *. destruct x, (split l). simpl in *.
       destruct (find _); discard_case. rewrite Hnd in *.
       simpl. destruct (is_AF_aux _) eqn: eqaf. 
       destruct H as [Hfot Haf]. unfold is_AF in Haf.
       eapply is_AF_aux_snd_is_FOT in Hfot.
       rewrite eqaf in Hfot. simpl in *; subst.
       destruct (fst (is_AF_aux R k)) eqn: eqfaf.
       (* eqfaf : true *)
       + rewrite eqaf in eqfaf. simpl in *; subst; 
         simpl; eauto.
       (* eqfaf : false *)
       + rewrite eqaf in *. simpl in *; subst.
         destruct k; discard_case.
     Qed.   

    
                  
     Theorem is_AF_correct : forall R t, 
      is_AF R t = true -> AF R t. 
     Proof. 
        intros * Haf. unfold is_AF in Haf.
        eapply is_AF_aux_fst_AF. 
        destruct t; discard_case; eauto;
        destruct (is_AF_aux _) eqn: eqaf;
        rewrite andb_true_iff in Haf; 
        destruct Haf; subst; eauto.      
     Qed.    

     Theorem is_AF_complete: forall R t, 
       AF R t -> is_AF R t = true. 
     Proof. 
       intros * HAf. induction HAf using AF_ind'; 
       solve_base; discard_case.
       (* AF R (kTProd t1 t2) *)
       + eapply is_AF_aux_snd_is_FOT in H, H0.
         eapply is_AF_correct in IHHAf, IHHAf0.
         eapply is_AF_aux_fst_AF in IHHAf, IHHAf0.
         simpl. destruct (is_AF_aux R t1) eqn: eqaf1, 
         (is_AF_aux R t2) eqn: eqaf2. 
         rewrite eqaf1 in H; rewrite eqaf2 in H0.
         simpl in *; subst; eauto.
       (* AF R (KTList t) *)
       + eapply is_AF_aux_snd_is_FOT in H. 
         eapply is_AF_correct in IHHAf. 
         eapply is_AF_aux_fst_AF in IHHAf. 
         simpl. destruct (is_AF_aux R t) eqn: eqaf. 
         rewrite eqaf in H; simpl in *; subst; eauto.
       (* AF R (KTVariant l) *)
       + eapply AF_is_AF_Ind; eauto.
       (* AF R (KTRef i) *)
       + simpl; rewrite H; eauto.
     Qed. 
           

    Corollary is_AF_eq_AF : forall R t, 
     is_AF R t = true <-> AF R t.
    Proof. 
      split. 
      apply is_AF_correct.
      apply is_AF_complete.
    Qed.


    Corollary is_DT_correct: forall R t, 
       is_DT R t = true -> DT R t. 
    Proof. 
      intros R t Hdt.  
      destruct t; discard_case.
      unfold is_DT in Hdt. 
      eapply is_AF_correct in Hdt.
      constructor; eauto. 
    Qed.

    Corollary is_DT_complete: forall R t, 
      DT R t -> is_DT R t = true. 
    Proof. 
      intros R t HDt. 
      destruct t; inversion HDt; subst; clear HDt.
      unfold is_DT. eapply is_AF_complete. eauto.
    Qed.    

    Corollary is_DT_eq_DT : forall R t, 
      is_DT R t = true <-> DT R t .
    Proof. 
      split. 
      apply is_DT_correct.
      apply is_DT_complete.
    Qed.

    Corollary Forall_DT_forall_is_DT : 
      forall R (B: list (Ide * KTp)), 
        forallb (fun p => is_DT R (snd p)) B = true <-> 
        Forall (fun p => DT R (snd p)) B.
    Proof. 
      split.
      (* -> *)
      + intro Hforall. induction B.
        * apply Forall_nil. 
        * simpl in *. rewrite andb_true_iff in Hforall.
          destruct Hforall. apply Forall_cons; eauto. 
          apply is_DT_correct. eauto. 
      (* <- *)
      + intro HForall. induction HForall; eauto. 
        simpl. rewrite andb_true_iff. split; eauto.
        apply is_DT_complete; eauto.
    Qed.    

    Lemma is_consistent_list: forall t t', 
      is_consistent (KTList t) (KTList t') = true -> 
      t <> KTEmpty -> 
      t' <> KTEmpty -> 
      is_consistent t t' = true. 
    Proof. 
      intros * Hc Hneq1 Hneq2. 
      simpl in *. 
      generalize dependent t'.
      induction t; intros; 
      destruct t'; eauto.
    Qed.

    Definition is_KTEmpty (t: KTp) := 
      match t with KTEmpty => true | _ => false end.

    Theorem is_consistent_correct: forall t t',  
      is_consistent t t' = true ->
      Consistent t t'. 
    Proof. 
      intros * Hc.
      generalize dependent t'. 
      induction t; intros; 
      inversion Hc; subst; clear Hc; 
      destruct t'; discard_case; 
      try (destruct t; discriminate).
      (* t := KTFunction *)
      + constructor.
      (* t := KTBase t *)
      + constructor. assert (Bool.reflect 
         (t = t0) (eqb_BaseTp P t t0)) 
         by apply eqb_eq_BaseTp.
        apply Bool.reflect_iff in H.
        apply H; eauto. 
      (* t := KTUnit *)
      + constructor.
      (* t := KTEmpty *)
      + constructor.
      (* t := KTProd t1 t2 *)
      + rewrite Bool.andb_true_iff in H0;
        destruct H0; subst. constructor. 
        apply IHt1. eauto. apply IHt2; eauto.
      (* t := KTList t *)
      + destruct (is_KTEmpty t) eqn: eqempty.
        * destruct t; discard_case. 
          apply c_TListNil1; eauto.
        * destruct t; discard_case; 
          destruct (is_KTEmpty t') eqn: eqempty'; 
          destruct t'; discard_case; 
          try apply c_TListNil2; eauto; 
          try apply c_TList; eauto.
      (* t := KTRef i *)
      + constructor. rewrite id_eqb_eq. eauto.
      (* t := KTError *)
      + constructor.     
    Qed.   


    Theorem is_consistent_complete: forall t t',  
      Consistent t t' -> 
      is_consistent t t' = true. 
    Proof. 
      intros * HC. induction HC; solve_base.  
      (* Consistent (KTBase t1) (KTBase t2) *)
      + assert (Bool.reflect 
         (t1 = t2) (eqb_BaseTp P t1 t2)) by (apply eqb_eq_BaseTp).
        apply Bool.reflect_iff in H0; apply H0; eauto. 
      (* Consistent (KTProd t1 t2) (KTProd t1' t2')*)
      + simpl. rewrite Bool.andb_true_iff; eauto.
      (* Consistent (KTList t) (KTList t') *)
      + simpl. destruct t; destruct t'; 
        eauto; 
        try inversion HC; subst;   
        subst; eauto.
      (* Consistent (KTList t) (KTList KTEmpty) *)
      + destruct t; eauto. 
      (* Consistent (KTRef i) (KTRef i') *)
      + subst . apply id_eqb_eq;  eauto.  
    Qed.


    (* Basic properties of Consistent relation *)
    
    Lemma consistent_is_FOT: forall t t',  
      Consistent t t' -> 
      is_FOT t = true /\ is_FOT t' = true. 
    Proof. 
      intros * HC . 
      induction HC; eauto; 
      destruct IHHC1, IHHC2;
      split; simpl; rewrite Bool.andb_true_iff; 
      split; eauto. 
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
      induction HC; 
      try apply c_TListNil1;
      try apply c_TListNil2; 
      try constructor; eauto.
    Qed. 
    
          
End TYPE_THEORY. 






     






