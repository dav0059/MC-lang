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
    Local Notation " 'base_tp_of_base_vl' x " := 
      (@base_tp_of_base_vl P x) (at level 50) .
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


    Definition val_env := env Ide Val.
                      
    Inductive Typeof : Val -> KTp -> Prop := 
     |Typeof_Cls      : forall arg body cls_env, 
                         Typeof (VCls arg body cls_env) KTFunction
     |Typeof_RCls     : forall name arg body cls_env, 
                         Typeof (VRecCls name arg body cls_env) KTFunction  
     |Typeof_VLit     : forall x, Typeof (VLit x) (KTBase (base_tp_of_base_vl x)) 
     |Typeof_VUnit    :  Typeof VUnit KTUnit 
     |Typeof_VNil     : Typeof VNil (KTList KTEmpty) 
     |Typeof_VPair    : forall v1 v2 t1 t2, 
                         Typeof (VPair (v1, t1) (v2, t2)) (KTProd t1 t2)
     |Typeof_VCons    : forall v1 v2 el_type,        
                         Typeof (VCons v1 v2 el_type) (KTList el_type)
     |Typeof_VVariant : forall c i t v, 
                         Typeof (VVariant c (i, t) v) (KTRef i)
     |Typeof_VError   : forall m, Typeof (VError m) (KTError) .
     
 
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

     with WFEV : val_env -> Prop := 
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
     |Match_PUnit    :  Match KPUnit VUnit
     |Match_PNil     :  Match KPNil VNil 
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
                        


    Inductive MatchEnv : KPat -> Val -> val_env -> val_env -> Prop := 
     |MatchEnv_PVar    : forall i v s, 
                           MatchEnv (KPVar i) v s (bind s i v id_eqb)
     |MatchEnv_PLit    : forall p v s,   
                           MatchEnv (KPLit p) (VLit v) s s 
     |MatchEnv_PAs     : forall p i v s s',  
                           MatchEnv p v s s' ->
                           MatchEnv (KPAs p i) v s (bind s' i v id_eqb)
     |MatchEnv_PAny    : forall v s, 
                           MatchEnv KPAny v s s 
     |MatchEnv_PUnit   : forall s,  
                           MatchEnv KPUnit VUnit s s 
     |MatchEnv_PNil    : forall s,  
                           MatchEnv KPNil VNil s s 
     |MatchEnv_PPair   : forall p1 p2 v1 v2 s s' s'',   
                           MatchEnv p1 (fst v1) s s' -> 
                           MatchEnv p2 (fst v2) s' s'' -> 
                           MatchEnv (KPPair p1 p2) (VPair v1 v2) s s'' 
     |MatchEnv_PCons   : forall p1 p2 v1 v2 el_type s s' s'',
                           MatchEnv p1 v1 s s' -> 
                           MatchEnv p2 v2 s' s'' -> 
                           MatchEnv (KPCons p1 p2) (VCons v1 v2 el_type) s s'' 
     |MatchEnv_PVariant: forall c c' p inf v s s', 
                           MatchEnv p v s s' -> 
                           MatchEnv (KPVariant c p) (VVariant c' inf v) s s' .
 
      
    Definition branch : Type := KPat * LExpr.  
    Definition cases := list (KPat * LExpr).

    Inductive FirstMatch : Val -> cases -> option branch -> Prop := 
    |FirstMatch_Nil  : forall v, FirstMatch v [] None 
    |FirstMatch_Head : forall head v tail, 
                        Match (fst head) v ->  
                        FirstMatch v (head::tail) (Some head)
    |FirstMatch_Tail : forall head v tail result,
                        ~Match (fst head) v ->   
                        FirstMatch v tail result -> 
                        FirstMatch v (head::tail) result .
   
   
    (* each value has exactly one type: determinism + totality of Typeof *)
    Lemma Typeof_deterministic: 
      forall v t t', 
      Typeof v t -> 
      Typeof v t' -> 
      t = t'.
    Proof. 
      intros * Htof1 Htof2. 
      induction Htof1; 
      inversion Htof2; subst; eauto.
    Qed. 


    Lemma Typeof_total: 
      forall v, exists t, Typeof v t.
    Proof. 
      intros. destruct v. 
      + exists KTFunction. constructor. 
      + exists KTFunction. constructor.
      + exists (KTBase (base_tp_of_base_vl x)).
        constructor.
      + exists KTUnit. constructor. 
      + exists (KTList KTEmpty). constructor.
      + destruct v1 as (v1, t1), v2 as (v2, t2).  
        exists (KTProd t1 t2). constructor.
      + exists (KTList el_type). constructor.
      + destruct inf as (i, t). exists (KTRef i). 
        constructor.
      + exists KTError. constructor.
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
      
    
    (* a proof of Match ensures the existence of an env to 
      construct a proof of MatchEnv *)
    Theorem Match_ex_MatchEnv: forall p v s, 
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
        exists s''. apply MatchEnv_PPair with (s' := s');eauto.
      + specialize IHHM1 with s. destruct IHHM1 as [s' *].
        specialize IHHM2 with s'. destruct IHHM2 as [s'' *].  
        exists s''. apply MatchEnv_PCons with (s' := s');eauto. 
      + specialize IHHM with s. destruct IHHM as [s' *].
        exists s'. constructor. eauto.
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
    

    Lemma MatchEnv_deterministic: forall p v s s' s'', 
      MatchEnv p v s s' -> 
      MatchEnv p v s s'' -> 
      s' = s'' . 
    Proof. 
      intros * HMe1 HMe2 .
      generalize dependent s''. 
      induction HMe1; intros; 
      inversion HMe2; subst; clear HMe2; eauto.
      + apply IHHMe1 in H4; subst; reflexivity.
      + apply IHHMe1_1 in H5; subst. 
        apply IHHMe1_2 in H6; subst.
        reflexivity.  
      + apply IHHMe1_1 in H6; subst. 
        apply IHHMe1_2 in H7; subst.
        reflexivity.
    Qed.
    
    
    Lemma FirstMatch_deterministic : 
      forall v l res res', 
        FirstMatch v l res -> 
        FirstMatch v l res' ->
        res = res'.  
    Proof. 
      intros * Hfm1 Hfm2. 
      induction Hfm1; 
      inversion Hfm2; subst; eauto; try contradiction.
    Qed. 
      
 
     

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
      |KPPair p1 p2, VPair v1 v2      => has_match p1 (fst v1) && 
                                         has_match p2 (fst v2) 
      |KPCons p1 p2, VCons v1 v2 _    => has_match p1 v1 && has_match p2 v2 
      |KPVariant c p, VVariant c' _ v => constr_eqb I c c' && has_match p v   
      |_, _                           => false 
      end.


    Fixpoint match_env (p: KPat) (v: Val) (s: val_env) : option val_env := 
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
        destruct v1, v2. apply Typeof_VPair.
        destruct inf. apply Typeof_VVariant.
    Qed.
    
    
    Theorem typeof_complete: forall v t, 
      Typeof v t -> typeof v = t.
    Proof.
        intros * HT; inversion HT; subst; eauto.
    Qed.
    
    Corollary typeof_eq_Typeof: forall v t, 
      typeof v = t <-> Typeof v t.
    Proof. 
      split. 
      apply typeof_correct.
      apply typeof_complete.
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

    
    Corollary has_match_eq_Match: forall p v, 
      has_match p v = true <-> Match p v.
    Proof. 
      split. 
      apply has_match_correct.
      apply has_match_complete.
    Qed.


    Corollary has_match_eq_Match_contra: forall p v, 
      has_match p v = false <-> ~Match p v.
    Proof. 
      intros. rewrite <- not_true_iff_false.
      apply not_iff_compat. apply has_match_eq_Match.
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
      + inversion Hm; subst; apply MatchEnv_PVar; eauto. 
      + destruct v; try discriminate; inversion Hm; 
        subst; apply MatchEnv_PLit; eauto.
      + destruct (match_env _) eqn: eqm; try discriminate; 
        inversion Hm. subst; apply MatchEnv_PAs; eauto.
      + inversion Hm; subst; apply MatchEnv_PAny; eauto. 
      + destruct v; try discriminate;
        inversion Hm; subst; apply MatchEnv_PUnit; eauto.   
      + destruct v; try discriminate;
        inversion Hm; subst; apply MatchEnv_PNil.  
      + destruct v; try discriminate.
        destruct (match_env p1 _) eqn: eqm; try discriminate. 
        destruct v1, v2; apply MatchEnv_PPair with (s' := v);
        simpl in *; try apply IHp1; try apply IHp2; eauto.
      + destruct v; try discriminate. 
        destruct (match_env _) eqn: eqm; try discriminate.
        apply MatchEnv_PCons with (s' := v); 
        try apply IHp1; try apply IHp2; eauto.
      + destruct v; try discriminate; apply MatchEnv_PVariant; 
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

    Corollary match_env_eq_MatchEnv: forall p v s s', 
      match_env p v s = Some s' <-> MatchEnv p v s s'.
    Proof. 
      split. 
      apply match_env_correct. 
      apply match_env_complete.
    Qed.

    Theorem FirstMatch_eq_find_match : 
      forall v l result,  
        find (fun x => has_match (fst x) v) l = result <->
        FirstMatch v l result.
    Proof. 
      intros. split. 
      + intro Hfind.
        induction l; intros.
        * simpl in Hfind; subst. constructor.
        * simpl in Hfind. destruct (has_match _) eqn: eqm. 
          apply has_match_correct in eqm; subst.
          apply FirstMatch_Head. eauto.
          apply has_match_eq_Match_contra in eqm.
          apply IHl in Hfind. apply FirstMatch_Tail; eauto.
      + intro HFm. induction HFm; eauto. 
        * apply has_match_complete in H. 
          simpl. rewrite H. eauto.
        * apply has_match_eq_Match_contra in H. 
          simpl. rewrite H. eauto.
    Qed.  


End Values. 



    
    


