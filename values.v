Require Import ids primitives kernel_syntax env type_theory pattern_theory elaboration.



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
    |VCls (name: option Ide) (arg: KPat ) (body: LExpr) (cls_env: env Ide Val)
    |VLit (x: BaseVl)
    |VUnit 
    |VNil (el_type: option KTp)
    |VPair (v1: Val * KTp) (v2: Val * KTp)
    |VCons (v1 v2: Val) (el_type: option KTp)
    |VVariant (c: Constr) (inf: Ide * KTp) (v: Val)
    |VError (m: Message). 


    Definition v_env := env Ide Val.
                      
    Inductive Typeof : Val -> KTp -> Prop := 
     |TOf_Cls      : forall name p e s, Typeof (VCls name p e s) (KTFunction) 
     |TOf_VLit     : forall x, Typeof (VLit x) (KTBase (base_tp_of_base_vl x)) 
     |TOf_VUnit    : Typeof VUnit KTUnit 
     |TOf_VNil     : Typeof (VNil None) (KTList KTEmpty) 
     |TOf_VPair    : forall v1 v2 t1 t2, 
                      Typeof (VPair (v1, t1) (v2, t2)) (KTProd t1 t2)
     |TOf_VCons    : forall v1 v2 el_type t,  
                      el_type = Some t ->      
                      Typeof (VCons v1 v2 el_type) (KTList t)
     |TOf_VVariant : forall c inf v, Typeof (VVariant c inf v) (KTRef (fst inf))
     |TOf_VError   : forall m, Typeof (VError m) (KTError) .
     
 
    Inductive WFV : Val -> Prop :=
     |WFV_Cls      : forall name p e s,
                      WFEV s -> 
                      WFV (VCls name p e s)
     |WFV_VLit     : forall x, WFV (VLit x)
     |WFV_VUnit    :  WFV VUnit 
     |WFV_VNil     :  WFV (VNil None)  
     |WFV_VPair    : forall v1 v2 t1 t2, 
                      WFV v1 -> 
                      Typeof v1 t1 ->
                      WFV v2 ->
                      Typeof v2 t2 -> 
                      WFV (VPair (v1, t1) (v2, t2))
     |WFV_VCons    : forall v1 v2 el_type t t1 t2, 
                      el_type = Some t -> 
                      WFV v1 -> 
                      WFV v2 -> 
                      Typeof v1 t1 -> 
                      Typeof v2 t2 -> 
                      Consistent t1 t ->
                      Consistent t2 (KTList t) -> 
                      WFV (VCons v1 v2 el_type)
     |WFV_VVariant : forall c inf v t, 
                      WFV v -> 
                      Typeof v t -> 
                      Consistent t (snd inf) ->
                      WFV (VVariant c inf v)
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
     |Match_PAs      : forall p i v,
                        Match p v ->
                        Match (KPAs p i) v
     |Match_PAny     : forall v, Match KPAny v 
     |Match_PUnit    : Match KPUnit VUnit
     |Match_PNil     : Match KPNil (VNil None) 
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
                           WFEV s -> 
                           MatchEnv (KPVar i) v s (bind s i v id_eqb)
     |MEnv_PLit    :  forall p v s, 
                           WFEV s ->  
                           MatchEnv (KPLit p) (VLit v) s s 
     |MEnv_PAs     :  forall p i v s s',
                           WFEV s ->  
                           MatchEnv p v s s' ->
                           MatchEnv (KPAs p i) v s (bind s' i v id_eqb)
     |MEnv_PAny    :  forall v s, 
                           WFEV s ->
                           MatchEnv KPAny v s s 
     |MEnv_PUnit   :  forall s, 
                           WFEV s -> 
                           MatchEnv KPUnit VUnit s s 
     |MEnv_PNil    :  forall s, 
                           WFEV s -> 
                           MatchEnv KPNil (VNil None) s s 
     |MEnv_PPair   :  forall p1 p2 v1 v2 s s' s'',
                           WFEV s ->   
                           MatchEnv p1 (fst v1) s s' -> 
                           MatchEnv p2 (fst v2) s' s'' -> 
                           MatchEnv (KPPair p1 p2) (VPair v1 v2) s s'' 
     |MEnv_PCons    : forall p1 p2 v1 v2 el_type s s' s'',
                           WFEV s ->   
                           MatchEnv p1 v1 s s' -> 
                           MatchEnv p2 v2 s' s'' -> 
                           MatchEnv (KPCons p1 p2) (VCons v1 v2 el_type) s s'' 
     |MEnv_PVariant : forall c c' p inf v s s', 
                           WFEV s ->   
                           MatchEnv p v s s' -> 
                           MatchEnv (KPVariant c p) (VVariant c' inf v) s s' .

    
     
    Definition typeof (v: Val) : option KTp := 
       match v with 
       |VCls _ _ _ _          => Some KTFunction 
       |VLit x                => Some (KTBase (base_tp_of_base_vl x)) 
       |VUnit                 => Some KTUnit 
       |VNil None             => Some (KTList (KTEmpty))
       |VPair v1 v2           => Some (KTProd (snd v1) (snd v2))
       |VCons _ _ (Some t)    => Some (KTList t) 
       |VVariant _ inf _      => Some (KTRef (fst inf))
       |VError _              => Some KTError
       |_                     => None 
       end. 
       
       
    Fixpoint has_match (p: KPat) (v: Val) : bool :=
      match p, v with 
      |KPVar _ , _                    => true 
      |KPLit x, VLit x'               => eqb_BaseVl P x x' 
      |KPAs p _, _                    => has_match p v  
      |KPAny, _                       => true 
      |KPUnit, VUnit                  => true 
      |KPNil, VNil None               => true 
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
      |KPNil, VNil None               => Some s 
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
     typeof v = Some t -> Typeof v t.
    Proof. 
        intros * Ht. 
        destruct v; simpl in Ht; inversion Ht; subst. 
        + apply TOf_Cls.
        + apply TOf_VLit.
        + apply TOf_VUnit. 
        + destruct el_type; try discriminate; 
          inversion Ht; subst; apply TOf_VNil.
        + destruct v1, v2. apply TOf_VPair.
        + destruct el_type; try discriminate; 
          inversion Ht; subst; apply TOf_VCons; eauto.
        + apply TOf_VVariant.
        + apply TOf_VError.
    Qed.
    
    
    Theorem typeof_complete: forall v t, 
      Typeof v t -> typeof v = Some t.
    Proof.
        intros * HT; inversion HT; subst; eauto.
    Qed.
    
    
    
    Theorem has_match_correct: forall p v, 
      has_match p v = true -> Match p v. 
    Proof. 
        intros .
        generalize dependent v. 
        induction p; intros; simpl in *.
        + apply Match_PVar.
        + destruct v; try discriminate; apply Match_PLit; eauto.
        + apply Match_PAs. eauto.
        + apply Match_PAny. 
        + destruct v; try discriminate; apply Match_PUnit.
        + destruct v; try discriminate.
          destruct el_type; try discriminate. apply Match_PNil.
        + destruct v; try discriminate. destruct v1, v2. 
          apply Match_PPair; apply andb_prop in H; 
          destruct H; eauto. 
        + destruct v; try discriminate. apply Match_PCons;
          apply andb_prop in H; destruct H; eauto.
        + destruct v; try discriminate; apply Match_PVariant; 
          apply andb_prop in H; destruct H; rewrite <- constr_eqb_eq in H; 
          eauto.
    Qed. 
    
    
    Theorem has_match_complete: forall p v, 
      Match p v -> has_match p v = true. 
    Proof. 
      intros * HMatch. induction HMatch; simpl; eauto;
      apply andb_true_intro; try rewrite <- constr_eqb_eq; 
      eauto. 
    Qed. 


    Theorem match_env_preservers_wfev: forall s p v s', 
     WFEV s ->
     WFV v -> 
     MatchEnv p v s s' ->
     WFEV s'.
    Proof. 
      intros * Hwfev Hwfv HME. 
      induction HME; eauto; 
      try apply WFEV_some; eauto;
      inversion Hwfv; subst; 
      try apply IHHME2; 
      try apply IHHME1; eauto.
    Qed.
    
    
    Theorem match_env_correct: forall p v s s',
      WFEV s ->  
      WFV v -> 
      match_env p v s = Some s' -> 
      MatchEnv p v s s'.
    Proof. 
      intros * Hwfev Hwfv Hmatch.
      generalize dependent s'.
      generalize dependent s. 
      generalize dependent v.
      induction p; intros; simpl in *. 
      + inversion Hmatch; subst; apply MEnv_PVar; eauto. 
      + destruct v; try discriminate; inversion Hmatch; 
        subst; apply MEnv_PLit; eauto.
      + destruct (match_env _) eqn: eqm; try discriminate; 
        inversion Hmatch. subst; apply MEnv_PAs; eauto.
      + inversion Hmatch; subst; apply MEnv_PAny; eauto. 
      + destruct v; try discriminate;
        inversion Hmatch; subst; apply MEnv_PUnit; eauto.   
      + destruct v; try destruct el_type; try discriminate.
        inversion Hmatch; subst; apply MEnv_PNil. eauto. 
      + destruct v; try discriminate.
        destruct (match_env p1 _) eqn: eqm; try discriminate. 
        destruct v1, v2; apply MEnv_PPair with (s' := v);
        simpl in *; try apply IHp1; try apply IHp2;  
        inversion Hwfv; subst; eauto.
        assert (Hp1: MatchEnv p1 v0 s v) by (apply IHp1; eauto).
        apply match_env_preservers_wfev with (s := s) (p := p1) (v := v0);
        eauto.
      + destruct v; try discriminate. 
        destruct (match_env _) eqn: eqm; try discriminate.
        apply MEnv_PCons with (s' := v); 
        try apply IHp1; try apply IHp2; 
        inversion Hwfv; subst; eauto.
        assert (Hp1: MatchEnv p1 v1 s v) by (apply IHp1; eauto).
        apply match_env_preservers_wfev with (s := s) (p := p1) (v := v1);
        eauto.
      + destruct v; try discriminate; apply MEnv_PVariant; 
        try apply IHp; inversion Hwfv; subst; eauto.
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
        

   
    Theorem typeof_eq_err: forall v, 
     typeof v = Some KTError <-> exists m, v = VError m.
    Proof. 
      split; intros H. 
      + destruct v; try destruct el_type; try discriminate. 
        exists m; eauto.
      + destruct H; subst; eauto.
    Qed. 
 
    Theorem typeof_eq_lit: forall v t, 
     typeof v = Some (KTBase t) <-> 
     exists x, v = VLit x /\ base_tp_of_base_vl x = t. 
    Proof. 
      split; intros H. 
      + destruct v; try destruct el_type; try discriminate. 
        exists x. split. reflexivity. simpl in H. 
        inversion H; eauto.
      + destruct H as [x [Heq Hbtp]]. subst. eauto.
    Qed.
    

    Theorem tempty_empty: ~exists v, typeof v = Some KTEmpty.
    Proof. 
      unfold not. intro contra. 
      destruct contra as [x]. destruct x; 
      try destruct el_type; try discriminate.
    Qed.  
  
       
    Theorem typeof_eq_lempty: forall v , 
     WFV v ->
     typeof v = Some (KTList KTEmpty) <-> v = VNil None. 
    Proof. 
      split; intros H'. 
      + destruct v; try destruct el_type eqn: eqelt; 
        simpl in *; try discriminate; eauto. 
        inversion H; inversion H3; inversion H'; subst. 
        inversion H8; subst.
        apply typeof_complete in H6.
        assert (Hyp: exists v, typeof v = Some KTEmpty) by 
         (exists v1; eauto). 
        apply tempty_empty in Hyp; contradiction.
      + subst; eauto.
    Qed. 


    Theorem typeof_neq_tvariant: forall v t l, 
      Typeof v t ->
      t <> KTVariant l. 
    Proof. 
      intros * Htof.
      inversion Htof; subst; unfold not; intro; try discriminate. 
    Qed. 


    Theorem typeof_is_FOT: forall v t,
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
      + inversion Htof; subst; inversion Hwfv; subst; eauto.
        simpl. inversion H2; subst. 
        apply consistent_is_FOT in H7; destruct H7; eauto.
      + apply typeof_neq_tvariant with (l := tags) in Htof.
        contradiction.
    Qed.
    

    Theorem nestempty_inconsistent_with_terr : forall v1 t1 v2 t2, 
      typeof v1 = Some t1 -> 
      typeof v2 = Some (KTList t2) ->
      nested_empty t2 = true -> 
      is_consistent t1 t2 = true ->
      t1 <> KTError. 
    Proof.
      intros * Htof1 Htof2 Hn Hc . 
      destruct t1, t2; simpl in *; discriminate.
    Qed. 

    
    
    


End Values. 


    
    


