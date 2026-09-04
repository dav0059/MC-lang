Require Import ids primitives kernel_syntax env type_theory pattern_theory elaboration.
Require Import Lists.List.
Require Import Bool. 
Import ListNotations.


Set Implicit Arguments. 
Set Contextual Implicit. 

Section Values. 
    
    Context (I : IDS). 
    Context (P: PRIM_DATA). 

    Local Notation " 'Ide' " := (@Ide I). 
    Local Notation " 'Constr' " := (@Constr I). 
    Local Notation " 'Message' " := (@Message I). 
    Local Notation " 'BaseVl' " := (@BaseVl P).
    Local Notation " 'KPat' " := (@KPat I P).
    Local Notation " 'LExpr' " := (@LExpr I P). 
    Local Notation " 'KTp' " := (@KTp I P).
    Local Notation " 'base_tp_of_base_vl' x " := (@base_tp_of_base_vl P x) (at level 50) .
    Local Notation " 'id_eqb' " := (@id_eqb I).
    

    Inductive Val : Type := 
    |VCls (arg: KPat ) (body: LExpr) (cls_env: env Ide Val)
    |VRecCls (name : Ide) (arg: KPat) (body: LExpr) (cls_env: env Ide Val)
    |VLit (x: BaseVl)
    |VUnit 
    |VNil 
    |VPair (v1: Val * KTp) (v2: Val * KTp)
    |VCons (v1 v2: Val) (el_type: KTp)
    |VVariant (c: Constr) (inf: Ide * KTp) (v: Val)
    |VError (m: Message). 


    Definition v_env := env Ide Val.
                      
    Inductive Typeof : Val -> KTp -> Prop := 
     |TOf_Cls      : forall arg body cls_env, 
                      Typeof (VCls arg body cls_env) KTFunction
     |TOf_RCls     : forall name arg body cls_env, 
                      Typeof (VRecCls name arg body cls_env) KTFunction  
     |TOf_VLit     : forall x, Typeof (VLit x) (KTBase (base_tp_of_base_vl x)) 
     |TOf_VUnit    : Typeof VUnit KTUnit 
     |TOf_VNil     : Typeof VNil (KTList KTEmpty) 
     |TOf_VPair    : forall v1 v2 t1 t2, 
                      Typeof (VPair (v1, t1) (v2, t2)) (KTProd t1 t2)
     |TOf_VCons    : forall v1 v2 el_type,        
                      Typeof (VCons v1 v2 el_type) (KTList el_type)
     |TOf_VVariant : forall c i t v, 
                      Typeof (VVariant c (i, t) v) (KTRef i)
     |TOf_VError   : forall m, Typeof (VError m) (KTError) .
     
 
    Inductive WFV : Val -> Prop :=
     |WFV_Cls      : forall arg body cls_env,
                      WFEV cls_env -> 
                      WFV (VCls arg body cls_env)
     |WFV_RCls     : forall name arg body cls_env, 
                      WFEV cls_env -> 
                      WFV (VRecCls name arg body cls_env)
     |WFV_VLit     : forall x, WFV (VLit x)
     |WFV_VUnit    :  WFV VUnit 
     |WFV_VNil     :  WFV VNil  
     |WFV_VPair    : forall v1 t1 v2 t2, 
                      WFV v1 -> 
                      Typeof v1 t1 ->
                      WFV v2 ->
                      Typeof v2 t2 -> 
                      WFV (VPair (v1, t1) (v2, t2))
     |WFV_VCons    : forall v1 v2 t1 t2 el_type, 
                      WFV v1 -> 
                      WFV v2 -> 
                      Typeof v1 t1 -> 
                      Typeof v2 t2 -> 
                      Consistent t1 el_type ->
                      Consistent t2 (KTList el_type) -> 
                      WFV (VCons v1 v2 el_type)
     |WFV_VVariant : forall v tv t c i, 
                      WFV v -> 
                      Typeof v tv -> 
                      Consistent tv t ->
                      WFV (VVariant c (i, t) v)
     |WFV_VError   : forall m, WFV (VError m)

     with WFEV : v_env -> Prop := 
      |WFEV_none : WFEV (@empty_env Ide Val)
      |WFEV_some : forall i v s, 
                    WFV v -> 
                    WFEV s -> 
                    WFEV (bind s i v (id_eqb)) .
      
    
     
    Inductive Match : KPat -> Val -> Prop := 
     |Match_PVar     : forall i v, Match (KPVar i) v
     |Match_PLit     : forall p v, 
                        eqb_BaseVl P p v = true ->
                        Match (KPLit p) (VLit v) 
     |Match_PAs      : forall p v i,
                        Match p v ->
                        Match (KPAs p i) v
     |Match_PAny     : forall v, Match KPAny v 
     |Match_PUnit    : Match KPUnit VUnit
     |Match_PNil     : Match KPNil VNil 
     |Match_PPair    : forall p1 p2 v1 v2,  
                        Match p1 (fst v1) -> 
                        Match p2 (fst v2) -> 
                        Match (KPPair p1 p2) (VPair v1 v2) 
     |Match_PCons    : forall p1 p2 v1 v2 el_type,  
                        Match p1 v1 -> 
                        Match p2 v2 -> 
                        Match (KPCons p1 p2) (VCons v1 v2 el_type)
     |Match_PVariant : forall c c' p v inf,  
                        c = c' -> 
                        Match p v -> 
                        Match (KPVariant c p) (VVariant c' inf v) .
                        


    Inductive MatchEnv : KPat -> Val -> v_env -> v_env -> Prop := 
     |MEnv_PVar    :  forall i v s, 
                           MatchEnv (KPVar i) v s (bind s i v id_eqb)
     |MEnv_PLit    :  forall p v s,   
                           MatchEnv (KPLit p) (VLit v) s s 
     |MEnv_PAs     :  forall p i v s s',  
                           MatchEnv p v s s' ->
                           MatchEnv (KPAs p i) v s (bind s' i v id_eqb)
     |MEnv_PAny    :  forall v s, 
                           MatchEnv KPAny v s s 
     |MEnv_PUnit   :  forall s,  
                           MatchEnv KPUnit VUnit s s 
     |MEnv_PNil    :  forall s,  
                           MatchEnv KPNil VNil s s 
     |MEnv_PPair   :  forall p1 p2 v1 v2 s s' s'',   
                           MatchEnv p1 (fst v1) s s' -> 
                           MatchEnv p2 (fst v2) s' s'' -> 
                           MatchEnv (KPPair p1 p2) (VPair v1 v2) s s'' 
     |MEnv_PCons    : forall p1 p2 v1 v2 el_type s s' s'',
                           MatchEnv p1 v1 s s' -> 
                           MatchEnv p2 v2 s' s'' -> 
                           MatchEnv (KPCons p1 p2) (VCons v1 v2 el_type) s s'' 
     |MEnv_PVariant : forall c c' p inf v s s', 
                           MatchEnv p v s s' -> 
                           MatchEnv (KPVariant c p) (VVariant c' inf v) s s' .



    Section FirstMatchProp. 

      Variable X : Set. 
    
      Inductive FirstMatch : 
        (X -> Prop) -> list X -> option X -> Prop := 
      |FirstMatch_Nil  : forall P, FirstMatch P [] None 
      |FirstMatch_Head : forall P head tail, 
                          P head ->  
                          FirstMatch P (head::tail) (Some head)
      |FirstMatch_Tail : forall P head tail result,
                          ~P head ->   
                          FirstMatch P tail result -> 
                          FirstMatch P (head::tail) result .

      
      Theorem find_eq_Find_some: 
        forall l f x P,
          (forall x, P x <-> f x = true)->  
           find f l = Some x <-> FirstMatch P l (Some x) .
      Proof.
        intros * Hrefl. 
        split. 
        + induction l; intro Hf. 
          * simpl in Hf; discriminate. 
          * simpl in *. destruct (f a) eqn: eqf. 
            - inversion Hf; subst; clear Hf. 
              apply FirstMatch_Head. apply Hrefl. eauto.
            - apply FirstMatch_Tail; specialize Hrefl with a;
              apply not_iff_compat in Hrefl;
              rewrite <- not_true_iff_false in eqf;
              try apply Hrefl; eauto. 
        + induction l; intros HF. 
          * inversion HF. 
          * inversion HF as [| Q h t Hq | Q h t res Hnq Htail]; 
            subst; clear HF. 
            - apply Hrefl in Hq. simpl. rewrite Hq. eauto.
            - specialize Hrefl with a.
              apply not_iff_compat in Hrefl. 
              rewrite Hrefl in Hnq. 
              rewrite not_true_iff_false in Hnq. simpl. 
              rewrite Hnq. eauto.   
      Qed. 


      Theorem find_eq_Find_none:
        forall l f P, 
         (forall x, P x <-> f x = true) -> 
         find f l = None <-> FirstMatch P l None .
      Proof.
        intros * Hrefl. split. 
        + intro Hf. induction l.
          * constructor.
          * simpl in Hf. destruct (f a) eqn: eqf.
            - discriminate.
            - apply IHl in Hf. apply FirstMatch_Tail.
              specialize Hrefl with a. 
              apply not_iff_compat in Hrefl. 
              rewrite <- not_true_iff_false in eqf.
              apply Hrefl; eauto.
              eauto.
        + intro HF. induction HF;  
          eauto; simpl; pose proof Hrefl as Hrefl'; 
          specialize Hrefl with head. 
          * apply Hrefl in H. rewrite H. eauto.
          * apply not_iff_compat in Hrefl. 
            apply Hrefl in H. rewrite not_true_iff_false in H.
            rewrite H. eauto.
      Qed.


      Theorem FirstMatch_deterministic : 
        forall P l res res', 
         FirstMatch P l res -> 
         FirstMatch P l res' ->
         res = res'.  
      Proof. 

    End FirstMatchProp.

     
    Definition typeof (v: Val) : KTp := 
       match v with 
       |VCls _ _ _            => KTFunction
       |VRecCls _ _ _ _       => KTFunction 
       |VLit x                => KTBase (base_tp_of_base_vl x) 
       |VUnit                 => KTUnit 
       |VNil                  => KTList (KTEmpty)
       |VPair (_, t1) (_, t2) => KTProd t1 t2
       |VCons _ _ t           => KTList t 
       |VVariant _ (i, _) _   => KTRef i
       |VError _              => KTError 
       end. 
       
       
    Fixpoint has_match (p: KPat) (v: Val) : bool :=
      match p, v with 
      |KPVar _ , _                    => true 
      |KPLit x, VLit x'               => eqb_BaseVl P x x' 
      |KPAs p _, _                    => has_match p v  
      |KPAny, _                       => true 
      |KPUnit, VUnit                  => true 
      |KPNil, VNil                    => true 
      |KPPair p1 p2, VPair v1 v2      => has_match p1 (fst v1) && has_match p2 (fst v2) 
      |KPCons p1 p2, VCons v1 v2 _    => has_match p1 v1 && has_match p2 v2 
      |KPVariant c p, VVariant c' _ v => constr_eqb I c c' && has_match p v   
      |_, _                           => false 
      end.


    Fixpoint match_env (p: KPat) (v: Val) (s: v_env) : option v_env := 
      match p, v with 
      |KPVar i, _                     => Some (bind s i v id_eqb) 
      |KPLit _, VLit _                => Some s  
      |KPAs p i, v                    => match match_env p v s with  
                                         |Some s' => Some (bind s' i v id_eqb) 
                                         |None    => None 
                                         end
      |KPAny, _                       => Some s 
      |KPUnit, VUnit                  => Some s
      |KPNil, VNil                    => Some s 
      |KPPair p1 p2, VPair v1 v2      => match match_env p1 (fst v1) s with 
                                         |Some s' => match_env p2 (fst v2) s' 
                                         |None    => None 
                                         end 
      |KPCons p1 p2, VCons v1 v2 _    => match match_env p1 v1 s with 
                                         |Some s' => match_env p2 v2 s' 
                                         |None    => None 
                                         end
      |KPVariant _ p, VVariant _ _ v  => match_env p v s   
      |_, _                           => None
      end.   
     

    Theorem typeof_correct: forall v t, 
     typeof v = t -> Typeof v t.
    Proof. 
        intros * Ht. 
        destruct v; simpl in Ht; inversion Ht; subst; clear; 
        try constructor. 
        destruct v1, v2. apply TOf_VPair.
        destruct inf. apply TOf_VVariant.
    Qed.
    
    
    Theorem typeof_complete: forall v t, 
      Typeof v t -> typeof v = t.
    Proof.
        intros * HT; inversion HT; subst; eauto.
    Qed.
    
    
    
    Theorem has_match_correct: forall p v, 
      has_match p v = true -> Match p v. 
    Proof. 
        intros .
        generalize dependent v. 
        induction p; intros; simpl in *; 
        first [destruct v; try discriminate; try constructor; 
        eauto]; 
        apply andb_prop in H; destruct H; eauto.
        rewrite <- constr_eqb_eq in H; eauto.
    Qed. 
    
    
    Theorem has_match_complete: forall p v, 
      Match p v -> has_match p v = true. 
    Proof. 
      intros * HMatch. induction HMatch; simpl; eauto;
      apply andb_true_intro; try rewrite <- constr_eqb_eq; 
      eauto. 
    Qed. 

    
    
    Theorem MatchEnv_preservs_wfev: forall s p v s', 
     WFV v ->
     WFEV s ->  
     MatchEnv p v s s' ->
     WFEV s'.
    Proof. 
      intros * Hwfv Hwfev HME. 
      induction HME; eauto;  
      try apply WFEV_some; eauto;
      inversion Hwfv; subst; 
      try apply IHHME2; 
      try apply IHHME1; eauto.
    Qed.

    Theorem match_env_correct: forall p v s s', 
      match_env p v s = Some s' -> 
      MatchEnv p v s s'.
    Proof. 
      intros * Hm.
      generalize dependent s'.
      generalize dependent s. 
      generalize dependent v.
      induction p; intros; simpl in *. 
      + inversion Hm; subst; apply MEnv_PVar; eauto. 
      + destruct v; try discriminate; inversion Hm; 
        subst; apply MEnv_PLit; eauto.
      + destruct (match_env _) eqn: eqm; try discriminate; 
        inversion Hm. subst; apply MEnv_PAs; eauto.
      + inversion Hm; subst; apply MEnv_PAny; eauto. 
      + destruct v; try discriminate;
        inversion Hm; subst; apply MEnv_PUnit; eauto.   
      + destruct v; try discriminate;
        inversion Hm; subst; apply MEnv_PNil.  
      + destruct v; try discriminate.
        destruct (match_env p1 _) eqn: eqm; try discriminate. 
        destruct v1, v2; apply MEnv_PPair with (s' := v);
        simpl in *; try apply IHp1; try apply IHp2; eauto.
      + destruct v; try discriminate. 
        destruct (match_env _) eqn: eqm; try discriminate.
        apply MEnv_PCons with (s' := v); 
        try apply IHp1; try apply IHp2; eauto.
      + destruct v; try discriminate; apply MEnv_PVariant; 
        apply IHp; eauto.
    Qed.
    
    
    Theorem match_env_complete: forall p v s s', 
      MatchEnv p v s s' -> 
      match_env p v s = Some s'. 
    Proof. 
      intros * HME.     
      induction HME; subst; eauto; simpl;
      destruct (match_env _) eqn: eqm; try discriminate;
      try inversion IHHME; 
      try inversion IHHME1; 
      try inversion IHHME2; subst; eauto.
    Qed.
        

    Theorem Match_implies_MatchEnv: forall p v s, 
      Match p v ->  
      exists s', MatchEnv p v s s'. 
    Proof. 
      intros * HM .
      generalize dependent s.
      induction HM; intros.   
      + exists (bind s i v id_eqb). constructor.
      + exists s; constructor.  
      + specialize IHHM with s. 
        destruct IHHM as [s' *]. exists (bind s' i v id_eqb).
        constructor; eauto.
      + exists s; constructor.
      + exists s; constructor.
      + exists s; constructor. 
      + specialize IHHM1 with s. destruct IHHM1 as [s' *].
        specialize IHHM2 with s'. destruct IHHM2 as [s'' *].  
        exists s''. apply MEnv_PPair with (s' := s');eauto.
      + specialize IHHM1 with s. destruct IHHM1 as [s' *].
        specialize IHHM2 with s'. destruct IHHM2 as [s'' *].  
        exists s''. apply MEnv_PCons with (s' := s');eauto. 
      + specialize IHHM with s. destruct IHHM as [s' *].
        exists s'. constructor. eauto.
    Qed.
       
      
    Theorem Typeof_eq_err: forall v, 
     Typeof v KTError <-> exists m, v = VError m.
    Proof. 
      split; intros H. 
      + destruct v; inversion H.
        exists m; eauto.
      + destruct H; subst; constructor.
    Qed. 
 
    Theorem Typeof_eq_lit: forall v t, 
     Typeof v (KTBase t) <-> 
     exists x, v = VLit x /\ base_tp_of_base_vl x = t. 
    Proof. 
      split; intros H. 
      + destruct v; inversion H.
        exists x. eauto.
      + destruct H as [x [Heq Hbtp]]. subst. constructor.
    Qed.
    

    Theorem tempty_is_empty: ~exists v, Typeof v KTEmpty.
    Proof. 
      unfold not. intro contra.
      inversion contra as [v H]; destruct v; inversion H. 
    Qed.  
  
       
    Theorem Typeof_eq_listempty: forall v , 
     WFV v -> 
     Typeof v (KTList KTEmpty) <-> v = VNil. 
    Proof. 
      intros * Hwfv ;split. 
      + intro HTof. destruct v; inversion HTof; subst; eauto.
        inversion Hwfv; subst.
        inversion H6; try discriminate; subst.
        apply ex_intro with (x := v1) in H4.
        apply tempty_is_empty in H4; contradiction.
      + intro. subst; constructor.
    Qed. 


    Theorem Typeof_neq_tvariant: forall v t l, 
      Typeof v t ->
      t <> KTVariant l. 
    Proof. 
      intros * Htof.
      inversion Htof; subst; unfold not; intro; try discriminate. 
    Qed. 


    Theorem Typeof_is_FOT: forall v t,
      WFV v -> 
      Typeof v t -> 
      is_FOT t = true.
    Proof. 
      intros * Hwfv Htof. 
      generalize dependent v.
      induction t; intros; eauto. 
      + inversion Htof; subst; inversion Hwfv; subst.  
        simpl. rewrite Bool.andb_true_iff. split; 
        try apply IHt1 with (v := v1); 
        try apply IHt2 with (v := v2); 
        eauto. 
      + simpl. inversion Htof; subst; inversion Hwfv; subst; eauto. 
        apply consistent_is_FOT in H6; destruct H6; eauto.
      + apply Typeof_neq_tvariant with (l := tags) in Htof.
        contradiction.
    Qed.
    
    

End Values. 



    
    


