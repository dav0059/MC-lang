Require Import ids.
Require Import primitives.
Require Import result_type.
Require Import env.
Require Import kernel_syntax.
Require Import type_theory.
Require Import elaboration.
Require Import values.
Require Import Strings.String.
Require Import Lists.List.
Require Import Bool.
Import ListNotations.
Open Scope string_scope.

Set Implicit Arguments.  
Set Contextual Implicit. 

Section EVALUATION. 
    
    Context (I : IDS).
    Context (P: PRIM_DATA). 
    
    Local Notation " 'LExpr' " := (LExpr I P).
    Local Notation " 'Val' " := (Val I P).
    Local Notation " 'val_env' " := (val_env I P). 
    Local Notation " 'WFEV' " := (@WFEV I P).
    Local Notation " 'interp_op' " := (interp_op P).
    Local Notation " 'BaseVl' " := (BaseVl P).
    Local Notation " 'id_eqb' " := (id_eqb I). 
    Local Notation " 'base_tp_of_base_vl' " := (base_tp_of_base_vl P).
    
    Fixpoint getBaseVl (l: list Val) : list BaseVl :=
      match l with 
      |(VLit x)::t => x::getBaseVl t 
      |_           => []
      end. 

    Definition all_lit (l: list Val) : Prop := 
      Forall (fun x => exists t, Typeof x (KTBase t)) l. 
      
    Definition one_error (l: list Val) : Prop := 
      exists m, l = [VError m].

    Lemma one_error_contra: forall mssg, 
      ~one_error [VError mssg] -> False.
    Proof. 
      intros * Herr. unfold not, one_error in Herr.
      apply Herr. exists mssg; eauto.
    Qed. 
        
    
    Inductive EVal : LExpr -> val_env -> Val -> Prop := 
    |EVal_Var      : forall i s v, 
                     WFEV s -> 
                     lookup s i = Some v -> 
                     EVal (LVar i) s v 
    |EVal_Lit      : forall x s , 
                     WFEV s -> 
                     EVal (LLit x) s (VLit x)  
    |EVal_LOp      : forall s le lv lbv op v,       
                     WFEV s -> 
                     EValOp (rev le) s lv ->
                     ~one_error lv -> 
                     getBaseVl (rev lv) = lbv -> 
                     interp_op op lbv = Some v ->
                     EVal (LOp op le) s (VLit v) 
    |EVal_LOpErr   : forall s le op mssg, 
                     WFEV s -> 
                     EValOp (rev le) s [VError mssg] ->
                     EVal (LOp op le) s (VError mssg)
    |EVal_LLam     : forall s arg body, 
                     WFEV s -> 
                     EVal (LLam arg body) s (VCls arg body s)
    |EVal_LApp     : forall s e1 arg body cls_env 
                          e2 v cls_env' v', 
                     WFEV s -> 
                     EVal e1 s (VCls arg body cls_env) -> 
                     EVal e2 s v -> 
                     ~Typeof v KTError ->     
                     Match arg v -> 
                     MatchEnv arg v cls_env cls_env' -> 
                     EVal body cls_env' v' ->
                     EVal (LApp e1 e2) s v'  
    |EVal_LAppRec  : forall s e1 name arg body cls_env 
                          e2 v cls_env' v', 
                     WFEV s ->  
                     EVal e1 s (VRecCls name arg body cls_env) ->
                     EVal e2 s v -> 
                     ~Typeof v KTError ->
                     Match arg v -> 
                     MatchEnv arg v cls_env cls_env' -> 
                     EVal body (bind cls_env' name 
                       (VRecCls name arg body cls_env) id_eqb) v' -> 
                     EVal (LApp e1 e2) s v'
    |EVal_LAppErr_fun  : forall s e1 e2 mssg, 
                     WFEV s -> 
                     EVal e1 s (VError mssg) -> 
                     EVal (LApp e1 e2) s (VError mssg) 
    |EVal_LAppErr_arg  : forall s e1 v e2 mssg, 
                     WFEV s -> 
                     EVal e1 s v -> 
                     Typeof v KTFunction ->  
                     EVal e2 s (VError mssg) -> 
                     EVal (LApp e1 e2) s (VError mssg) 
    |EVal_LUnit     : forall s, 
                     WFEV s -> 
                     EVal LUnit s VUnit 
    |EVal_LNil      : forall s, 
                     WFEV s -> 
                     EVal LNil s VNil
    |EVal_LPair     : forall s e1 e2 v1 t1 v2 t2,
                     WFEV s -> 
                     EVal e1 s v1 ->  
                     Typeof v1 t1 ->
                     t1 <> KTError -> 
                     EVal e2 s v2 -> 
                     Typeof v2 t2 ->
                     t2 <> KTError -> 
                     EVal (LPair e1 e2) s 
                          (VPair (v1, t1) (v2, t2))
    |EVal_LPairErr_fst : forall e1 s mssg e2, 
                     WFEV s -> 
                     EVal e1 s (VError mssg) ->
                     EVal (LPair e1 e2) s (VError mssg)
    |EVal_LPairErr_snd : forall s e1 v1 e2 mssg, 
                     WFEV s -> 
                     EVal e1 s v1 ->
                     ~Typeof v1 KTError -> 
                     EVal e2 s (VError mssg) ->
                     EVal (LPair e1 e2) s (VError mssg)
    |EVal_LCons      : forall s e1 v1 t1 e2,  
                       WFEV s -> 
                       EVal e1 s v1 -> 
                       Typeof v1 t1 -> 
                       t1 <> KTError -> 
                       EVal e2 s VNil -> 
                       EVal (LCons e1 e2) s (VCons v1 VNil t1)
    |EVal_LCons_nestt  : forall s e1 v1 t1 e2 v2 t, 
                       WFEV s -> 
                       EVal e1 s v1 ->
                       Typeof v1 t1 ->
                       EVal e2 s v2 ->
                       Typeof v2 (KTList t) -> 
                       Consistent t1 t ->
                       nested_empty t = true ->  
                       EVal (LCons e1 e2) s (VCons v1 v2 t1)
    |EVal_LCons_nestf     : forall s e1 v1 t1 e2 v2 t, 
                       WFEV s -> 
                       EVal e1 s v1 -> 
                       Typeof v1 t1 -> 
                       t1 <> KTError -> 
                       EVal e2 s v2 -> 
                       Typeof v2 (KTList t) -> 
                       Consistent t1 t -> 
                       nested_empty t = false -> 
                       EVal (LCons e1 e2) s (VCons v1 v2 t)
    |EVal_LConsErr_head   : forall s e1 mssg e2, 
                       WFEV s -> 
                       EVal e1 s (VError mssg) ->
                       EVal (LCons e1 e2) s (VError mssg)
    |EVal_LConsErr_tail   : forall e1 s v1 e2 mssg , 
                       WFEV s -> 
                       EVal e1 s v1 -> 
                       ~Typeof v1 KTError -> 
                       EVal e2 s (VError mssg) -> 
                       EVal (LCons e1 e2) s (VError mssg)
    |EVal_LVariant    : forall s e v t' t c i, 
                       WFEV s -> 
                       EVal e s v -> 
                       Typeof v t' -> 
                       t' <> KTError -> 
                       Consistent t t' -> 
                       EVal (LVariant c (i, t) e) s 
                             (VVariant c (i, t) v)
    |EVal_LVariantErr : forall e s mssg c inf, 
                       WFEV s -> 
                       EVal e s (VError mssg) -> 
                       EVal (LVariant c inf e) s (VError mssg)
    |EVal_LFix        : forall s e arg body cls_env name,
                       WFEV s -> 
                       EVal e s (VCls arg body cls_env) ->  
                       EVal (LFix name e) s 
                            (VRecCls name arg body cls_env)
    |EVal_LFixErr     : forall e s mssg name, 
                       WFEV s -> 
                       EVal e s (VError mssg) -> 
                       EVal (LFix name e) s (VError mssg)
    |EVal_LMatch      : forall s e v p' e' s' v' l, 
                       WFEV s -> 
                       EVal e s v -> 
                       ~Typeof v KTError -> 
                       FirstMatch v l (Some (p', e')) ->
                       MatchEnv p' v s s' -> 
                       EVal e' s' v' -> 
                       EVal (LMatch e l) s v' 
    |EVal_LMatchErr   : forall e s m l, 
                       WFEV s -> 
                       EVal e s (VError m) -> 
                       EVal (LMatch e l) s (VError m) 
    |EVal_LError      : forall s m, 
                       WFEV s -> 
                       EVal (LError m) s (VError m)

    
    with EValOp : list LExpr -> val_env -> list Val -> Prop := 
     |EValOp_nil      : forall s, 
                        WFEV s ->
                        EValOp [] s []
     |EValOp_cons     : forall s tail tail' head x,
                        WFEV s -> 
                        EValOp tail s tail' -> 
                        ~one_error tail' -> 
                        EVal head s (VLit x) -> 
                        EValOp (head::tail) s (VLit x::tail') 
     |EValOpErr_head : forall s tail tail' head mssg, 
                        WFEV s ->   
                        EValOp tail s tail' -> 
                        ~one_error tail' -> 
                        EVal head s (VError mssg) -> 
                        EValOp (head::tail) s [VError mssg] 
     |EValOpErr_tail : forall s head tail mssg,
                        WFEV s ->  
                        EValOp tail s [VError mssg] ->
                        EValOp (head::tail) s [VError mssg] .
                      
                    
    (* we need a powerful induction principle for mutually recursive types. 
       Let's Scheme command generates one for us. *)
    Scheme EVal_mut := Induction for EVal Sort Prop
    with EValOp_mut := Induction for EValOp Sort Prop.


    Theorem canonical_EValOp_result: forall l s l',
      EValOp l s l' -> 
      all_lit l' \/ one_error l'. 
    Proof. 
      intros * Hevop.
      generalize dependent l'.  
      induction l; intros.  
      + inversion Hevop; subst. left. unfold all_lit.
        apply Forall_nil.
      + inversion Hevop; subst; 
        try (right;unfold one_error; exists mssg; reflexivity). 
        left. apply IHl in H2. destruct H2; try contradiction.
        unfold all_lit; apply Forall_cons; eauto. 
        exists (base_tp_of_base_vl x). constructor.
    Qed. 

    Corollary EvalOp_result_noerror: forall l s l', 
      EValOp l s l' -> 
      ~one_error l' -> 
      all_lit l'.
    Proof. 
      intros * Hevop Hnerr. 
      apply canonical_EValOp_result in Hevop. 
      destruct Hevop. eauto. contradiction.
    Qed.

    Lemma getBaseVl_safe: forall l s l', 
      EValOp l s l' ->
      ~one_error l' -> 
      length (getBaseVl l') = length l'.
    Proof. 
      intros * Hevop Hnerr.
      generalize dependent l'. 
      induction l; intros. 
      + inversion Hevop; subst. eauto.
      + inversion Hevop; subst; clear Hevop; 
        try (apply one_error_contra in Hnerr; contradiction); 
        simpl; f_equal; eauto.
    Qed.   
          
      

    (* The following lemmas establish that each rule has a short-circuited
       propagation behaviour determined by the left-to-right 
       evaluation order for VError values. *)
    Lemma lop_propagates_leftmost_verror: forall l s l' m op, 
      EValOp (rev l) s l' -> 
      l' = [VError m] -> 
      EVal (LOp op l) s (VError m).
    Proof. 
      intros * Hevop Hl'. 
      destruct l. 
      + inversion Hevop; subst. discriminate.
      + inversion Hevop; subst; try discriminate; 
        constructor; eauto. 
    Qed. 
      

    Lemma lapp_propagates_left_verror: forall e1 s mssg e2, 
      EVal e1 s (VError mssg) -> 
      EVal (LApp e1 e2) s (VError mssg).
    Proof. 
      intros * HEv. 
      constructor; eauto.
      inversion HEv; eauto.
    Qed. 

    Lemma lapp_propagates_right_verror: forall e1 s v e2 mssg, 
      EVal e1 s v ->
      Typeof v KTFunction -> 
      EVal e2 s (VError mssg) -> 
      EVal (LApp e1 e2) s (VError mssg).
    Proof. 
      intros * HEv1 HEv2. 
      apply EVal_LAppErr_arg with (v := v) ; eauto.
      inversion HEv1; eauto.
    Qed. 


    Lemma lpair_propagates_left_verror: forall e1 s mssg e2, 
      EVal e1 s (VError mssg) -> 
      EVal (LPair e1 e2) s (VError mssg). 
    Proof. 
      intros * HEv. 
      constructor; eauto. 
      inversion HEv; eauto. 
    Qed. 


    Lemma lpair_propagates_right_verror: forall e1 s v e2 mssg, 
      EVal e1 s v -> 
      ~Typeof v KTError ->  
      EVal e2 s (VError mssg) ->
      EVal (LPair e1 e2) s (VError mssg). 
    Proof. 
      intros * HEv1 Htof HEv2. 
      apply EVal_LPairErr_snd with (v1 := v); eauto. 
      inversion HEv2; eauto. 
    Qed. 
    
    
    Lemma lcons_propagates_left_verror: forall e1 s mssg e2, 
      EVal e1 s (VError mssg) -> 
      EVal (LCons e1 e2) s (VError mssg).
    Proof. 
      intros * HEv. 
      constructor; eauto. 
      inversion HEv; eauto. 
    Qed. 


    Lemma lcons_propagates_right_verror: forall e1 s v e2 mssg,
      EVal e1 s v -> 
      ~Typeof v KTError ->  
      EVal e2 s (VError mssg) -> 
      EVal (LCons e1 e2) s (VError mssg).
    Proof. 
      intros * HEv1 Htof HEv2. 
      apply EVal_LConsErr_tail with (v1 := v); eauto.
      inversion HEv1; eauto.
    Qed. 
    
    
    Lemma lvariant_propagates_verror: forall e s mssg c inf, 
      EVal e s (VError mssg) -> 
      EVal (LVariant c inf e) s (VError mssg).
    Proof. 
      intros * HEv. 
      constructor; eauto. 
      inversion HEv; eauto. 
    Qed. 
    
    
    Lemma lfix_propagates_verror: forall e s mssg i, 
      EVal e s (VError mssg) -> 
      EVal (LFix i e) s (VError mssg). 
    Proof. 
      intros * HEnv. 
      constructor; eauto. 
      inversion HEnv; eauto. 
    Qed. 


    Lemma lmatch_propagates_verror: forall e s mssg l, 
      EVal e s (VError mssg) -> 
      EVal (LMatch e l) s (VError mssg). 
    Proof. 
      intros * HEv. 
      constructor; eauto. 
      inversion HEv; eauto. 
    Qed.


    (* the evaluation semantics produces well-formed values *)
    Theorem EVal_wfv: forall e s v, 
      EVal e s v -> 
      WFV v. 
    Proof. 
      intros * HEv. 
      induction HEv using EVal_mut with 
       (P0 := fun l s l' _ => EValOp l s l' -> 
         Forall (fun v => WFV v) l'); 
      try constructor; eauto. 
      + induction w; subst; unfold lookup, empty_env in e. 
        discriminate. unfold bind in e.
        destruct (id_eqb i i0) eqn: eqid; 
        inversion e; subst; eauto. 
      + apply WFV_VCons with (t1 := t1) (t2 := KTList KTEmpty); 
        eauto. constructor.
        * apply consistent_refl; eauto.
          apply Typeof_is_FOT with (v := v1); eauto.
        * apply c_TListNil1, Typeof_is_FOT with (v := v1); eauto.
      + apply WFV_VCons with (t1 := t1) (t2 := KTList t); eauto.
        * apply consistent_refl, Typeof_is_FOT with (v := v1); eauto.
        * apply c_TList, consistent_sym; eauto.
      + apply WFV_VCons with (t1 := t1) (t2 := KTList t); eauto.
        apply c_TList, consistent_refl. 
        apply consistent_is_FOT in c; destruct c; eauto.
      + apply WFV_VVariant with (t := t) (tv := t'); eauto.
        apply consistent_sym; eauto.
      + inversion IHHEv; eauto.
      + apply WFV_VError.
    Qed. 
         
        

    (* the evaluation semantic is deterministic *)
    Theorem EVal_deterministic : forall e s v v',
      WFEV s ->  
      EVal e s v -> 
      EVal e s v' -> 
      v = v'.
    Proof.
      intros e s v v' Hwfev HEv1 HEv2.
      generalize dependent v'.
      induction HEv1 using EVal_mut with 
        (P0 := fun l s l' _ => forall l'', 
          WFEV s -> EValOp l s l' -> EValOp l s l'' -> l' = l'' );
       intros.
      + inversion HEv2; subst; rewrite H1 in e; 
        inversion e; eauto.
      + inversion HEv2; subst; eauto. 
      + inversion HEv2; subst; clear HEv2.
        * assert (lv = lv0) by (apply IHHEv1; eauto); subst.
          rewrite H7 in e1. inversion e1; eauto.
        * assert (lv = [VError mssg]) by (apply IHHEv1; eauto).
          subst. apply one_error_contra in n. contradiction.
      + inversion HEv2; subst; clear HEv2.
        * assert ([VError mssg] = lv) by (apply IHHEv1; eauto); 
          subst. apply one_error_contra in H3; contradiction.
        * assert (Heq: [VError mssg] = [VError mssg0]) by 
          (apply IHHEv1; eauto); inversion Heq; subst; reflexivity.  
      + inversion HEv2; subst; reflexivity.  
      + inversion HEv2; subst; clear HEv2. 
        * assert (Hp1: VCls arg body cls_env =
                        VCls arg0 body0 cls_env0) 
          by (apply IHHEv1_1; eauto).
          assert (Hp2: v = v0) by (apply IHHEv1_2; eauto). 
          inversion Hp1; subst; clear Hp1.
          assert (cls_env' = cls_env'0) by 
           (apply MatchEnv_deterministic with (p:= arg0) (v := v0) 
            (s := cls_env0); eauto ); subst.          
          apply IHHEv1_3; eauto. apply EVal_wfv in HEv1_1, HEv1_2. 
          inversion HEv1_1;  
          apply MatchEnv_preservs_wfev with (s := cls_env0)
            (p := arg0) (v := v0); eauto.  
        * assert (VCls arg body cls_env = 
                       VRecCls name arg0 body0 cls_env0) 
          by (apply IHHEv1_1; eauto). 
          discriminate. 
        * assert (VCls arg body cls_env = VError mssg) 
          by (apply IHHEv1_1; eauto). 
          discriminate .
        * assert (v = VError mssg) by (apply IHHEv1_2; eauto); 
          subst. apply Typeof_err_contra in n. contradiction.
      + inversion HEv2; subst; clear HEv2. 
        * assert (VRecCls name arg body cls_env = 
                  VCls arg0 body0 cls_env0)  
          by (apply IHHEv1_1; eauto). 
          discriminate.
        * assert (Hp1: VRecCls name arg body cls_env = 
                  VRecCls name0 arg0 body0 cls_env0) 
          by (apply IHHEv1_1; eauto); 
          inversion Hp1; subst; clear Hp1. 
          assert (v = v0) by (apply IHHEv1_2; eauto); subst.
          assert (cls_env' = cls_env'0) by (apply MatchEnv_deterministic
            with (p := arg0) (v := v0) (s := cls_env0); eauto); subst. 
          apply IHHEv1_3; eauto.
          apply EVal_wfv in HEv1_1, H3; inversion HEv1_1; subst.
          apply MatchEnv_preservs_wfev in H6; eauto. 
          constructor; eauto.
        * assert (VRecCls name arg body cls_env = VError mssg) 
          by (apply IHHEv1_1; eauto). 
          discriminate.
        * assert (v = VError mssg) by (apply IHHEv1_2; eauto); 
          subst; apply Typeof_err_contra in n; contradiction.
      + inversion HEv2; subst; clear HEv2; eauto.
        * apply IHHEv1 with (v' := VCls arg body cls_env) in H2. 
          discriminate. eauto.
        * apply IHHEv1 with (v' := VRecCls name arg body cls_env)
          in H2. discriminate. eauto. 
        * apply IHHEv1 with (v' := v) in H2; subst. inversion H3. 
          eauto.
      + inversion HEv2; subst; clear HEv2; eauto. 
        * apply IHHEv1_2 with (v' := v0) in H3; subst.
          apply Typeof_err_contra in H4; contradiction. eauto.
        * apply IHHEv1_2 with (v' := v0) in H3; subst.
          apply Typeof_err_contra in H4; contradiction. eauto.
        * apply IHHEv1_1 in H4; subst; eauto. inversion t.
      + inversion HEv2; eauto.
      + inversion HEv2; eauto.
      + inversion HEv2; subst; clear HEv2. 
        * assert (v1 = v0) by (apply IHHEv1_1; eauto); subst.
          assert (v2 = v3) by (apply IHHEv1_2; eauto); subst;
          repeat f_equal. 
          apply Typeof_deterministic with (v := v0); eauto.
          apply Typeof_deterministic with (v := v3); eauto.
        * assert (v1 = VError mssg) by (apply IHHEv1_1 ; eauto); 
          subst. inversion t; subst. contradiction. 
        * assert (v2 = VError mssg) by (apply IHHEv1_2 ; eauto); 
          subst. inversion t0; subst; contradiction.
      + inversion HEv2; subst; clear HEv2; eauto. 
        * assert (VError mssg = v1) by (apply IHHEv1; eauto); 
          subst. inversion H3; subst; contradiction.
        * assert (VError mssg = v1) by (apply IHHEv1; eauto). 
          subst. apply Typeof_err_contra in H3; contradiction.
      + inversion HEv2; subst; clear HEv2; eauto.  
        * assert (VError mssg = v2) by (apply IHHEv1_2; eauto); 
          subst. inversion H6; subst. contradiction.
        * assert (v1 = VError mssg0) by 
          (apply IHHEv1_1 in H4; eauto); 
          subst. apply Typeof_err_contra in n; contradiction.
      + inversion HEv2; subst; clear HEv2. 
        * apply IHHEv1_1 in H2; eauto; subst.
          f_equal. apply Typeof_deterministic with (v := v0); 
          eauto. 
        * apply IHHEv1_1 in H2; eauto; subst. 
          apply IHHEv1_2 in H4; eauto; subst.
          f_equal. apply Typeof_deterministic with (v := v0); 
          eauto.
        * apply IHHEv1_1 in H2; eauto; subst. 
          apply IHHEv1_2 in H5; eauto; subst.
          f_equal. inversion H6; subst. inversion H7; subst. 
          apply Typeof_deterministic with (v := v0); eauto.
        * apply IHHEv1_1 in H4; eauto; subst.
          inversion t; subst; contradiction.
        * apply IHHEv1_2 in H6; eauto; subst. discriminate.
      + inversion HEv2; subst; clear HEv2.
        * apply IHHEv1_1 in H2; eauto; subst. 
          apply IHHEv1_2 in H7; eauto; subst.
          f_equal. apply Typeof_deterministic with (v := v0); 
          eauto.
        * apply IHHEv1_1 in H2; eauto; subst. 
          apply IHHEv1_2 in H4; eauto; subst.
          f_equal. apply Typeof_deterministic with (v := v0); 
          eauto.
        * apply IHHEv1_1 in H2; eauto; subst. 
          apply IHHEv1_2 in H5; eauto; subst.
          repeat f_equal.
          assert (t1 = t3) by ( 
           apply Typeof_deterministic with (v := v0); eauto); subst.
          assert (H: KTList t = KTList t4) by (
           apply Typeof_deterministic with (v := v3); 
           eauto); inversion H; subst.   
          rewrite H10 in e; discriminate.
        * apply IHHEv1_1 in H4; eauto; subst.
          inversion t0; subst. inversion c; subst.
          simpl in *. discriminate.
        * apply IHHEv1_2 in H6; eauto; subst.
          inversion t2.
      + inversion HEv2; subst; clear HEv2. 
        * apply IHHEv1_1 in H2; eauto; subst. 
          apply IHHEv1_2 in H7; eauto; subst.
          inversion t2; subst. inversion c; subst.
          repeat f_equal. apply Typeof_deterministic with 
          (v := v0); eauto.
        * apply IHHEv1_1 in H2; eauto; subst. 
          apply IHHEv1_2 in H4; eauto; subst.
          assert (H: KTList t = KTList t4) by (
           apply Typeof_deterministic with (v := v3); 
           eauto); inversion H; subst.   
          rewrite H9 in e; discriminate.     
        * apply IHHEv1_1 in H2; eauto; subst. 
          apply IHHEv1_2 in H5; eauto; subst. 
          repeat f_equal.
          assert (H: KTList t = KTList t4) by (
           apply Typeof_deterministic with (v := v3); 
           eauto); inversion H; subst. eauto.
        * apply IHHEv1_1 in H4; eauto; subst.
          inversion t0; subst; contradiction.  
        * apply IHHEv1_2 in H6; eauto; subst.
          inversion t2.  
      + inversion HEv2; subst; eauto; clear HEv2; 
        try(apply IHHEv1 in H2; eauto; subst;
          inversion H3; subst; contradiction); 
        apply IHHEv1 in H2; eauto; subst.
        * inversion H3; subst. inversion H6; subst.
          simpl in *; discriminate.
        * apply Typeof_err_contra in H3; contradiction.
      + inversion HEv2; subst; eauto; clear HEv2.
        * apply IHHEv1_2 in H7; eauto; discriminate.
        * apply IHHEv1_2 in H4; eauto; subst. inversion H5.
        * apply IHHEv1_2 in H5; eauto; subst; inversion H6.
        * apply IHHEv1_1 in H4; eauto; subst. 
          apply Typeof_err_contra in n; contradiction.
      + inversion HEv2; subst; clear HEv2. 
        * apply IHHEv1 in H4; subst; eauto.
        * apply IHHEv1 in H5; eauto; subst. 
          inversion t0; subst. contradiction.
      + inversion HEv2; subst; eauto; clear HEv2. 
        apply IHHEv1 in H3; eauto ; subst.  
        inversion H4; subst; contradiction. 
      + inversion HEv2; subst; clear HEv2. 
        * apply IHHEv1 in H4; inversion H4; subst; eauto.
        * apply IHHEv1 in H4; eauto; discriminate.
      + inversion HEv2; subst; clear HEv2; eauto.
        apply IHHEv1 in H4; eauto; discriminate.
      + inversion HEv2; subst; clear HEv2. 
        * apply IHHEv1_1 in H2; subst; eauto.
          assert (Hs: Some (p', e') = Some (p'0, e'0)) by 
            (apply FirstMatch_deterministic with (v := v0) (l := l); 
             eauto); inversion Hs; subst; clear Hs.
          apply IHHEv1_2. 
          apply MatchEnv_preservs_wfev in m; eauto.
          apply EVal_wfv in HEv1_1; eauto.
          assert (s' = s'0) by (apply MatchEnv_deterministic 
            with (p := p'0) (v := v0) (s := s); eauto); 
          subst; eauto.
        * apply IHHEv1_1 in H4; eauto; subst. 
          apply Typeof_err_contra in n; contradiction.
      + inversion HEv2; subst; eauto.
        apply IHHEv1 in H2; eauto; subst. 
        apply Typeof_err_contra in H3; contradiction.
      + inversion HEv2; subst; eauto.
      + inversion H1; eauto.
      + inversion H1; subst; eauto; clear H1.
        * f_equal. apply IHHEv0 in H9; eauto.
          apply IHHEv1; eauto.  
        * apply IHHEv0 in H9; eauto; discriminate.
        * apply IHHEv1 in H7; eauto; subst. 
          apply one_error_contra in n; contradiction.
      + inversion H1; subst; clear H1.
        * apply IHHEv0 in H9; eauto; discriminate.
        * apply IHHEv0 in H9; eauto; inversion H9; reflexivity.  
        * apply IHHEv1 in H7; eauto; subst.
          apply one_error_contra in n; contradiction.
      + inversion H1; subst; clear H1; eauto; 
         assert (contra : [VError mssg] = tail') by (
              apply IHHEv1; eauto); subst; 
          apply one_error_contra in H6; contradiction.
        
    Qed.   
        

    Definition eval_result := result Val string.  
    Definition evalop_result := result (list Val) string.       

    Fixpoint eval (n: nat) (e: LExpr) (s: v_env) : eval_result := 
      match n with 
      |O    => Error("stack overflow"%string)
      |S n' => match e with 
              |LVar i     => match lookup s i with 
                             |Some v => Ok v 
                             |None   => Error("unbound variable"%string)
                             end
              |LLit x     => Ok(VLit x) 
              |LOp op []  => match interp_op op [] with 
                             |Some v => Ok(VLit v) 
                             |None   => Error("primitive operation failure"%string)
                             end 
              |LOp op l   => let lv := evalop n' (rev l) s in
                             match lv with 
                             |Error m          => Error m 
                             |Ok []            => Error("impossible"%string)
                             |Ok (VError m::_) => Ok (VError m) 
                             |Ok ((_::_) as lv)  => match interp_op op (getBaseVl (rev lv)) with 
                                                  |Some v => Ok(VLit v) 
                                                  |None   => Error("primitive operation failure"%string)
                                                  end 
                             end 
              |LLam p e   => Ok (VCls None p e s)
              |LApp e1 e2 => match eval n' e1 s with 
                             |Error m                  => Error m 
                             |Ok(VError m)             => Ok(VError m)  
                             |Ok(VCls None p e s_cls)  => 
                                let v := eval n' e2 s in 
                                match v with 
                                |Error m      => Error m 
                                |Ok(VError m) => Ok(VError m)
                                |Ok v         =>
                                    if has_match p v then 
                                      match match_env p v s_cls with 
                                      |None       => Error("impossible"%string)
                                      |Some s_ext => eval n' e s_ext 
                                      end 
                                    else Error("pattern matching failure"%string)       
                                end 
                             |Ok((VCls (Some i) p e s_rcls) as fclosure) =>
                                let v := eval n' e2 s in 
                                match v with 
                                |Error m      => Error m 
                                |Ok(VError m) => Ok(VError m)  
                                |Ok v         => if has_match p v then 
                                                   match match_env p v s_rcls with 
                                                   |None       => Error("impossible"%string)
                                                   |Some s_ext => eval n' e (bind s_ext i fclosure (id_eqb))
                                                   end 
                                                 else Error("pattern matching failure"%string)
                                end
                             |_                            => Error("Illegal application"%string)
                             end 
              |LUnit       => Ok(VUnit)
              |LNil        => Ok(VNil None)
              |LPair e1 e2 => match eval n' e1 s with 
                              |Error m      => Error m 
                              |Ok(VError m) => Ok(VError m)
                              |Ok v1        => match eval n' e2 s with 
                                               |Error m      => Error m 
                                               |Ok(VError m) => Ok(VError m)
                                               |Ok v2        => 
                                                  match typeof v1, typeof v2 with
                                                  |Some t1, Some t2 => Ok (VPair (v1, t1) (v2, t2))
                                                  |_, _             => Error ("impossibile"%string)
                                                  end 
                                              end 
                              end
              |LCons e1 e2 => match eval n' e1 s with 
                              |Error m      => Error m 
                              |Ok(VError m) => Ok(VError m)
                              |Ok v1        => match eval n' e2 s with 
                                               |Error m         => Error m 
                                               |Ok(VError m)    => Ok(VError m)
                                               |Ok(VNil None)   => 
                                                 match typeof v1 with 
                                                 |Some t1  => Ok(VCons v1 (VNil None) (Some t1)) 
                                                 |None     => Error("impossibile"%string)
                                                 end 
                                               |Ok v2            => 
                                                 match typeof v1, typeof v2 with 
                                                 |Some t1, Some (KTList t2) => 
                                                   if is_consistent t1 t2 then 
                                                     if nested_empty t2 then Ok(VCons v1 v2 (Some t1)) 
                                                     else Ok(VCons v1 v2 (Some t2))
                                                   else Error("typechecking failure"%string) 
                                                 |Some t1, Some _     => Error("typechecking failure"%string)   
                                                 |None, _  | _, None  => Error("impossibile"%string)
                                                 end 
                                              end 
                              end  
              |LVariant c (i, t) e => match eval n' e s with 
                                      |Error m      => Error m 
                                      |Ok(VError m) => Ok(VError m)
                                      |Ok v         => match typeof v with 
                                                       |Some tv  => 
                                                         if is_consistent t tv then
                                                           Ok(VVariant c (i, t) v)
                                                         else Error("typechecking failure"%string)
                                                       |None     => Error("impossibile"%string)
                                                       end 
                                      end 
              |LFix i e            => match eval n' e s with 
                                      |Error m                                => Error m 
                                      |Ok(VError m)                           => Ok(VError m)
                                      |Ok((VCls None p e' s_cls) as fclosure) => 
                                        Ok(VCls (Some i) p e' (bind s_cls i fclosure id_eqb))   
                                      |_                                      => 
                                        Error ("Illegal recursive construction"%string)
                                      end 
              |LMatch e l          => match eval n' e s with 
                                      |Error m      => Error m 
                                      |Ok(VError m) => Ok(VError m)
                                      |Ok v         => match find (fun '(p, _) => has_match p v) l with 
                                                       |Some (p', e') => match match_env p' v s with 
                                                                         |Some s'  => eval n' e' s' 
                                                                         |None     => Error("impossibile"%string)
                                                                         end 
                                                       |None          => Error("pattern matching failure"%string)
                                                       end 
                                      end 
              |LError m            => Ok(VError m)                         
              end 
      end
  
    with evalop (n: nat) (l: list LExpr) (s:v_env) : evalop_result := 
      match n with 
      |O    => Error("stack overflow"%string)
      |S n' =>
          match l with 
          |[]   => Ok []
          |h::t => let tv := evalop n' t s in 
                    match tv with 
                    |Error m           => Error m 
                    |Ok (VError m::_ ) => tv
                    |Ok l              => match eval n' h s with 
                                          |Error m       => Error m 
                                          |Ok(VError m)  => Ok(VError m::l)
                                          |Ok(VLit x)    => Ok(VLit x::l)
                                          |_             => 
                                            Error("Illegal primitive operation construction"%string)
                                          end 
                    end
          end
      end.        






































    (* la dimostrazione di questa proprietà richiede
       la previa dimostrazione del fatto che ogni 
       estensione dell'ambiente s durante la valutazione 
       di una qualsiasi espressione e non aggiunge mai 
       un VError, perchè le regole lo propagano subito.
       Ma la formalizzazione big step della EVal non consente 
       di ragionare sugli stati intermedi e su come l'ambiente 
       di valutazione evolve, oltre al fatto di rimanere ben
       formato.  
       Allo stato attuale in cui la proprietà sotto è 
       formulata essa è semplicemente falsa, infatti un ambiente
       ben formato s di partenza può ben contenere un Verror
       associato ad una qualche nome i. *)
    Lemma verror_not_in_venv: forall s i v, 
      EVal (LVar i) s v -> 
      typeof v <> Some KTError. 
    Proof. 
    Abort. 
    
           
           
          
      
      
                    

                        


End EVALUATION.