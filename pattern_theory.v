Require Import ids primitives kernel_syntax type_env env type_theory. 
Require Import Lists.List. 
Import ListNotations. 

Set Implicit Arguments. 
Set Contextual Implicit. 

Section PATTERN_THEORY. 
    
    Context (I: IDS). 
    Context (P: PRIM_DATA). 
    
    Local Notation " 'Ide' " := (@Ide I). 
    Local Notation " 'KPat' " := (@KPat I P). 
    Local Notation " 'Constr' " := (@Constr I).
    Local Notation " 'KTp' " := (@KTp I P).
    Local Notation " 'tenv' " := (@tenv I P).
    Local Notation " 'register' " := (@register I).

    (* function for computing the list of pattern variables *)
    Fixpoint pv (p: KPat) : list Ide := 
      match p with 
      |KPVar i         => [i]
      |KPLit _         => [] 
      |KPAny           => []
      |KPAs p i        => i::(pv p)
      |KPUnit          => []
      |KPNil           => []
      |KPPair p1 p2    => pv p1 ++ pv p2 
      |KPCons p1 p2    => pv p1 ++ pv p2 
      |KPVariant c p   => pv p 
      end.

      
    (* function for deciding if two Id lists intersects at some point *)
    Fixpoint intersect (l l': list Ide) : bool :=  
      match l, l' with 
      |_, [] | [], _ => false 
      |h::t, _       => match find (fun x => id_eqb I x h) l' with  
                        |Some _ => true 
                        |None   => intersect t l'
                        end 
      end.

    
    Lemma find_none_not_In : forall {X: Type} i l eqb,
      (forall (x y: X), Bool.reflect (x = y) (eqb x y)) -> 
      find (fun x => eqb x i) l = None -> 
      ~In i l. 
    Proof. 
      intros * Hrefl Hfind Hcontra. 
      induction l. 
      + destruct Hcontra. 
      + destruct (eqb a i) eqn: eq; 
        simpl in Hfind; rewrite eq in Hfind. 
        - discriminate.  
        - inversion Hcontra; subst. 
          -- specialize Hrefl with i i. 
             destruct Hrefl. discriminate. contradiction.
          -- eauto.            
    Qed.

      
    Theorem intersect_correct: forall l l', 
           (exists x, In x l /\ In x l') <-> intersect l l' = true. 
    Proof. 
            split. 
            - intros Hex. induction l. 
              + destruct Hex as [x Hex]; 
                destruct Hex as [contra _].
                destruct contra.  
              + destruct Hex as [x Hex]; destruct l'. 
                ++ destruct Hex as [_ contra]; 
                   destruct contra. 
                ++ destruct Hex as [Hxa Hxi]. 
                   simpl; destruct (id_eqb I i a) eqn: eqai; eauto. 
                   destruct (find (fun x => id_eqb I x a) l') eqn: eqfind; eauto.
                   apply IHl.
                   exists x.
                   split; eauto. 
                   inversion Hxa as [Ha | Hl]. 
                   * rewrite <- id_eqb_neq in eqai; subst. 
                     apply find_none_not_In in eqfind. 
                     inversion Hxi; subst; contradiction.
                     apply ids_refl. 
                   * eauto. 
                          
            - intros Hintrs. 
              induction l as [| x t]. 
              + simpl in Hintrs. destruct l'; discriminate. 
              + simpl in Hintrs. 
                destruct l' as [| x' t']. discriminate.  
                destruct (find (fun x0 => id_eqb I x0 x) (x' :: t')) eqn: eqfind. 
                * apply find_some in eqfind. 
                  destruct eqfind as [Hin Heq]. 
                  rewrite <- id_eqb_eq in Heq; subst.
                  exists x. 
                  split; eauto. 
                  unfold In. left; eauto. 
                * apply IHt in Hintrs .
                  destruct Hintrs as [x0 [Hxt Hxx']].
                  exists x0.
                  split.  
                  unfold In. right. eauto. 
                  eauto.
    Qed.  
        

    Corollary contra_intersect_correct: forall l l', 
      ~(exists x, In x l /\ In x l') <-> ~(intersect l l' = true). 
    Proof. 
      intros.  
      apply not_iff_compat. 
      apply intersect_correct. 
    Qed. 
    


    Definition constr_env := env Constr (Ide * KTp). 

    
    Definition WFEC (d: constr_env) (r: tenv) (R: register) :=
      WFET r R /\  
      forall i t c,
        lookup d c = Some (i, t) -> 
        exists l, last_type_def r c = Some (i, KTVariant l) /\ In (c, t) l.
    
        
    (* Well formed patterns *) 
    Inductive WFP (d : constr_env) (r: tenv) (R: register): KPat -> Prop := 
    |WFP_PVar     : forall i, 
                      WFEC d r R -> 
                      WFP d r R (KPVar i)
    |WFP_PLit     : forall x, 
                      WFEC d r R  -> 
                      WFP d r R (KPLit x)
    |WFP_PAny     :  WFEC d r R -> 
                     WFP d r R KPAny 
    |WFP_PAs      : forall i p,
                      WFEC d r R ->  
                      WFP d r R p -> 
                      intersect (pv p) [i] = false -> 
                      WFP d r R (KPAs p i)    
    |WFP_PUnit    : WFEC d r R -> 
                    WFP d r R KPUnit 
    |WFP_PNil     : WFEC d r R -> 
                    WFP d r R KPNil 
    |WFP_PPair    : forall p1 p2,
                      WFEC d r R ->   
                      WFP d r R p1 -> 
                      WFP d r R p2 -> 
                      intersect (pv p1) (pv p2) = false -> 
                      WFP d r R (KPPair p1 p2)
    |WFP_PCons    : forall p1 p2,
                      WFEC d r R ->  
                      WFP d r R p1 -> 
                      WFP d r R p2 -> 
                      intersect (pv p1) (pv p2) = false -> 
                      WFP d r R (KPCons p1 p2)
    |WFP_PVariant : forall c p ,
                      WFEC d r R ->  
                      includes d c = true ->  
                      WFP d r R p -> 
                      WFP d r R (KPVariant c p) . 


  (* function for deciding if a pattern is well formed *)
   Fixpoint is_WFP (d: constr_env) p :=  
     match p with 
     |KPVar _       => true 
     |KPLit _       => true  
     |KPAny         => true 
     |KPAs p i      => is_WFP d p && negb (intersect (pv p) [i])
     |KPUnit        => true 
     |KPNil         => true 
     |KPPair p1 p2  => is_WFP d p1 && is_WFP d p2 && 
                        negb (intersect (pv p1) (pv p2))
     |KPCons p1 p2  => is_WFP d p1 && is_WFP d p2 && 
                        negb (intersect (pv p1) (pv p2))
     |KPVariant c p => includes d c && is_WFP d p
    end.
    
       
    Theorem is_WFP_correct: forall d r R p, 
      WFEC d r R -> is_WFP d p = true -> WFP d r R p .
    Proof. 
      intros * Hwfec Hwfp. 
      induction p. 
      + apply WFP_PVar; eauto.
      + apply WFP_PLit; eauto.  
      + apply WFP_PAs; eauto;
        simpl in Hwfp;
        rewrite Bool.andb_true_iff in Hwfp; 
        destruct Hwfp as [Hwfp Hintrs]; eauto.
        destruct (pv p) as [| x t] eqn : eq.  
        - eauto.  
        - destruct (find (fun x => id_eqb I x i) (x::t)) eqn: eqi.  
          * rewrite Bool.negb_true_iff in Hintrs; eauto. 
          * apply Bool.not_true_is_false. 
            apply contra_intersect_correct.
            unfold not; intros contra.
            destruct contra as [x0 [HInxt HIni]];
            destruct HIni; subst; 
            apply find_none_not_In in eqi; 
            try contradiction.
            apply ids_refl. 
      + apply WFP_PAny; eauto.  
      + apply WFP_PUnit; eauto. 
      + apply WFP_PNil; eauto. 
      + apply WFP_PPair; eauto; 
        simpl in Hwfp;
        repeat rewrite Bool.andb_true_iff in Hwfp;
        destruct Hwfp as [[Hwfp1 Hwfp2] Hnintrs] ; eauto.
        apply Bool.negb_true_iff; 
        eauto. 
      + apply WFP_PCons; eauto; 
        simpl in Hwfp;
        repeat rewrite Bool.andb_true_iff in Hwfp;
        destruct Hwfp as [[Hwfp1 Hwfp2] Hnintrs] ; eauto.
        apply Bool.negb_true_iff; 
        eauto.
      + simpl in *; apply WFP_PVariant; eauto; 
        rewrite Bool.andb_true_iff in Hwfp;
        destruct Hwfp; eauto.
    Qed.  
       
  
    Theorem is_WFP_complete: forall d r R p , 
      WFEC d r R -> WFP d r R p -> is_WFP d p = true. 
    Proof. 
      intros * Hwfec Hwfp. 
      induction Hwfp; try eauto.   
      + simpl.  
        rewrite Bool.andb_true_iff.
        split; eauto. 
        rewrite Bool.negb_true_iff; eauto.
      + simpl. 
        repeat (rewrite Bool.andb_true_iff; simpl; split); 
        try rewrite Bool.negb_true_iff; 
        eauto. 
      + simpl. 
        repeat (rewrite Bool.andb_true_iff; simpl; split); 
        try rewrite Bool.negb_true_iff; 
        eauto.
      + simpl. rewrite H0; eauto.
    Qed. 





End PATTERN_THEORY.

