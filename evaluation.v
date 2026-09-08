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
    
    Local Notation " 'Ide' " := (Ide I).
    Local Notation " 'LExpr' " := (LExpr I P).
    Local Notation " 'Val' " := (Val I P).
    Local Notation " 'val_env' " := (val_env I P). 
    Local Notation " 'WFEV' " := (@WFEV I P).
    Local Notation " 'interp_op' " := (interp_op P).
    Local Notation " 'BaseVl' " := (BaseVl P).
    Local Notation " 'id_eqb' " := (id_eqb I). 
    Local Notation " 'base_tp_of_base_vl' " := (base_tp_of_base_vl P).
   
    
    Ltac destruct_pairs := 
      repeat match goal with 
      | x: ?A * ?B |- _  => destruct x 
      end . 
    
    Ltac inversion_subst H := 
      inversion H; subst; clear H.


    Ltac destruct_elim e := 
      destruct e; try discriminate.
(* 
    Ltac solve_base_case H :=  *)
       
      

   
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
        
    Lemma not_one_error_empty: ~one_error [].
    Proof. 
      unfold not, one_error. intro contra. 
      destruct contra. discriminate. 
    Qed.

    Lemma not_one_error_lit: forall x l, 
      ~one_error (VLit x::l).
    Proof. 
      unfold not, one_error; intros * contra.
      destruct contra. discriminate. 
    Qed.


    
    Inductive EVal : LExpr -> val_env -> Val -> Prop := 
    |EVal_Var      : forall i s v, 
                     WFEV s -> 
                     lookup s i = Some v -> 
                     EVal (LVar i) s v 
    |EVal_Lit      : forall x s , 
                     WFEV s -> 
                     EVal (LLit x) s (VLit x)  
    |EVal_LOp      : forall s le lv op v,       
                     WFEV s -> 
                     EValOp (rev le) s lv ->
                     ~one_error lv ->  
                     interp_op op (getBaseVl (rev lv)) = Some v ->
                     EVal (LOp op le) s (VLit v) 
    |EVal_LOpErr   : forall s le op mssg, 
                     WFEV s -> 
                     EValOp (rev le) s [VError mssg] ->
                     EVal (LOp op le) s (VError mssg)
    |EVal_LLam     : forall s arg body, 
                     WFEV s -> 
                     EVal (LLam arg body) s (VCls NotRecursive arg body s)
    |EVal_LApp     : forall s e1 arg body cls_env 
                          e2 v cls_env' v', 
                     WFEV s -> 
                     EVal e1 s (VCls NotRecursive arg body cls_env) -> 
                     EVal e2 s v -> 
                     ~Typeof v KTError ->     
                     Match arg v -> 
                     MatchEnv arg v cls_env cls_env' -> 
                     EVal body cls_env' v' ->
                     EVal (LApp e1 e2) s v'  
    |EVal_LAppRec  : forall s e1 name arg body cls_env 
                          e2 v cls_env' v', 
                     WFEV s ->  
                     EVal e1 s (VCls (Recursive name) arg body cls_env) ->
                     EVal e2 s v -> 
                     ~Typeof v KTError ->
                     Match arg v -> 
                     MatchEnv arg v cls_env cls_env' -> 
                     EVal body (bind cls_env' name 
                      (VCls (Recursive name) arg body cls_env) id_eqb) v' -> 
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
                       EVal e s (VCls NotRecursive arg body cls_env) ->  
                       EVal (LFix name e) s 
                            (VCls (Recursive name) arg body cls_env)
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
      all_lit l' -> 
      ~one_error l'.
    Proof. 
      intros * Hevop Hall. 
      apply canonical_EValOp_result in Hevop. 
      destruct Hevop. 
      + inversion Hall; try apply not_one_error_empty.
        intro contra. unfold one_error in contra.
        destruct H0 as [t Htof]. apply tbase_Typeof_lit 
        in Htof. destruct Htof as [* [*]]; subst.
        destruct contra as [m contra]. inversion contra.
      + inversion Hall; try apply not_one_error_empty.
        inversion H. inversion H3; subst. 
        inversion H4; subst. destruct H0. inversion H0.
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
          rewrite H6 in e0. inversion e0; eauto.
        * assert (lv = [VError mssg]) by (apply IHHEv1; eauto).
          subst. apply one_error_contra in n. contradiction.
      + inversion HEv2; subst; clear HEv2.
        * assert ([VError mssg] = lv) by (apply IHHEv1; eauto); 
          subst. apply one_error_contra in H3; contradiction.
        * assert (Heq: [VError mssg] = [VError mssg0]) by 
          (apply IHHEv1; eauto); inversion Heq; subst; reflexivity.  
      + inversion HEv2; subst; reflexivity.  
      + inversion HEv2; subst; clear HEv2. 
        * assert (Hp1: VCls NotRecursive arg body cls_env =
                        VCls NotRecursive arg0 body0 cls_env0) 
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
        * assert (VCls NotRecursive arg body cls_env = 
                  VCls (Recursive name) arg0 body0 cls_env0) 
          by (apply IHHEv1_1; eauto). 
          discriminate. 
        * assert (VCls NotRecursive arg body cls_env = VError mssg) 
          by (apply IHHEv1_1; eauto). 
          discriminate .
        * assert (v = VError mssg) by (apply IHHEv1_2; eauto); 
          subst. apply Typeof_err_contra in n. contradiction.
      + inversion HEv2; subst; clear HEv2. 
        * assert (VCls (Recursive name) arg body cls_env = 
                  VCls (NotRecursive) arg0 body0 cls_env0)  
          by (apply IHHEv1_1; eauto). 
          discriminate.
        * assert (Hp1: VCls (Recursive name) arg body cls_env = 
                       VCls (Recursive name0) arg0 body0 cls_env0) 
          by (apply IHHEv1_1; eauto); 
          inversion Hp1; subst; clear Hp1. 
          assert (v = v0) by (apply IHHEv1_2; eauto); subst.
          assert (cls_env' = cls_env'0) by 
           (apply MatchEnv_deterministic 
             with (p := arg0) (v := v0) (s := cls_env0); eauto); subst. 
          apply IHHEv1_3; eauto.
          apply EVal_wfv in HEv1_1, H3; inversion HEv1_1; subst.
          apply MatchEnv_preservs_wfev in H6; eauto. 
          constructor; eauto.
        * assert (VCls (Recursive name) arg body cls_env = VError mssg) 
          by (apply IHHEv1_1; eauto). 
          discriminate.
        * assert (v = VError mssg) by (apply IHHEv1_2; eauto); 
          subst; apply Typeof_err_contra in n; contradiction.
      + inversion HEv2; subst; clear HEv2; eauto.
        * apply IHHEv1 with 
           (v' := VCls NotRecursive arg body cls_env) in H2. 
          discriminate. eauto.
        * apply IHHEv1 with (v' := VCls (Recursive name) arg body cls_env)
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
    
  
    Fixpoint eval (fuel: nat) (e: LExpr) (s: val_env) : eval_result := 
      match fuel with 
      |O    => Error("stack overflow")
      |S n' => match e with 
              |LVar i     => match lookup s i with 
                             |Some v => Ok v 
                             |None   => Error("unbound variable")
                             end
              |LLit x     => Ok(VLit x) 
              |LOp op l   => let lv := evalop n' (rev l) s in
                             match lv with 
                             |Error mssg       => Error mssg 
                             |Ok [VError mssg] => Ok (VError mssg) 
                             |Ok (_ as lv)  => 
                               match interp_op op (getBaseVl (rev lv)) with 
                               |Some v => Ok(VLit v) 
                               |None   => Error("primitive operation failure"%string)
                               end 
                             end 
              |LLam arg body => Ok (VCls NotRecursive arg body s)
              |LApp e1 e2 => 
                match eval n' e1 s with 
                |Error mssg                     => Error mssg 
                |Ok(VError mssg)                => Ok(VError mssg) 
                |Ok ((VCls typ arg body cls_env) as vcls) =>
                    match eval n' e2 s with 
                    |Error mssg      => Error mssg 
                    |Ok(VError mssg) => Ok(VError mssg)
                    |Ok v2           =>   
                      if (has_match arg v2) then 
                        match typ with 
                        |NotRecursive   => 
                          eval n' body (match_env arg v2 cls_env)  
                        |Recursive name => 
                          eval n' body (bind 
                            (match_env arg v2 cls_env) name vcls id_eqb) 
                        end  
                      else Error("pattern matching failure"%string)
                    end   
                |_  => Error ("Illegal application"%string) 
                end 
              |LUnit       => Ok VUnit
              |LNil        => Ok VNil 
              |LPair e1 e2 => 
                match eval n' e1 s with 
                |Error mssg      => Error mssg 
                |Ok(VError mssg) => Ok(VError mssg)
                |Ok v1           => 
                    match eval n' e2 s with 
                    |Error m      => Error m 
                    |Ok(VError m) => Ok(VError m)
                    |Ok v2        => 
                      Ok (VPair (v1, typeof v1) (v2, typeof v2))
                    end 
                end
              |LCons e1 e2 => 
                match eval n' e1 s with 
                |Error mssg      => Error mssg 
                |Ok(VError mssg) => Ok(VError mssg)
                |Ok v1           => 
                  match eval n' e2 s with 
                  |Error mssg        => Error mssg 
                  |Ok(VError mssg)   => Ok(VError mssg)
                  |Ok VNil           => Ok (VCons v1 VNil (typeof v1))
                  |Ok((VCons _ _ t) as v2) =>  
                      if is_consistent (typeof v1) t then 
                        if nested_empty t then Ok(VCons v1 v2 (typeof v1)) 
                        else Ok(VCons v1 v2 t)
                      else Error("typechecking failure"%string) 
                  |_  => Error("typechecking failure"%string)
                  end 
                end  
              |LVariant c (i, t) e =>
                match eval n' e s with 
                |Error mssg      => Error mssg 
                |Ok(VError mssg) => Ok(VError mssg)
                |Ok v         =>  
                    if is_consistent t (typeof v) then
                      Ok(VVariant c (i, t) v)
                    else Error("typechecking failure"%string) 
                end 
              |LFix name e  => 
                match eval n' e s with 
                |Error mssg       => Error mssg 
                |Ok(VError mssg)  => Ok(VError mssg)
                |Ok(VCls NotRecursive arg body cls_env) => 
                  Ok(VCls (Recursive name) arg body cls_env)   
                |_                                      => 
                  Error ("Illegal recursive construction"%string)
                end 
              |LMatch e l   => 
                match eval n' e s with 
                |Error mssg      => Error mssg 
                |Ok(VError mssg) => Ok(VError mssg)
                |Ok v            => 
                    match find (fun '(p, _) => has_match p v) l with 
                    |Some (p', e') => eval n' e' (match_env p' v s)   
                    |None          => Error("pattern matching failure"%string)
                    end 
                end 
              |LError m            => Ok(VError m)                         
              end 
      end
  
    with evalop (fuel: nat) (l: list LExpr) (s:val_env) : evalop_result := 
      match fuel with 
      |O    => Error("stack overflow"%string)
      |S n' => match l with 
               |[]   => Ok []
               |h::t => 
                  match evalop n' t s with 
                  |Error mssg       => Error mssg 
                  |Ok [VError mssg] => Ok [VError mssg]
                  |Ok lv            => 
                    match eval n' h s with 
                    |Error mssg      => Error mssg 
                    |Ok(VError mssg) => Ok [VError mssg]
                    |Ok(VLit x)      => Ok(VLit x::lv)
                    |_               => 
                      Error("Illegal primitive operation construction"%string)
                    end 
                  end
               end
      end.

          
    Lemma wfev_cls_env_extension: 
      forall e1 s typ arg body cls_env e2 v,
        EVal e1 s (VCls typ arg body cls_env) ->  
        EVal e2 s v ->  
        Match arg v -> 
        WFEV (match_env arg v cls_env) . 
    Proof.
      intros * HEv1 HEv2 Hm. 
      apply MatchEnv_preservs_wfev with (p := arg)
      (v := v) (s := cls_env).
      + apply EVal_wfv in HEv2; eauto.
      + apply EVal_wfv in HEv1. 
        inversion HEv1; subst; eauto.
      + apply match_env_safe; eauto.
    Qed.
    
    Corollary wfev_cls_env_rec_extension: 
      forall e1 s name arg body cls_env e2 v,
        EVal e1 s (VCls (Recursive name) arg body cls_env) ->  
        EVal e2 s v ->  
        Match arg v -> 
        WFEV (bind (match_env arg v cls_env) name 
          (VCls (Recursive name) arg body cls_env) id_eqb) .
    Proof. 
      intros * HEv1 HEv2 Hm. constructor. 
      apply EVal_wfv with (e := e1) (s := s); eauto.
      eapply wfev_cls_env_extension; eauto.
    Qed.  


    Lemma eval_op_correct: 
      forall s n op l v, 
       (forall s e v, 
         WFEV s -> 
         eval n e s = Ok v -> 
         EVal e s v) /\ 
       (forall s l lv, 
         WFEV s -> 
         evalop n l s = Ok lv -> 
         EValOp l s lv) -> 
       WFEV s -> 
       eval (S n) (LOp op l) s = Ok v ->
       EVal (LOp op l) s v.
    Proof. 
      intros * Hind Hwfev Hev. 
      destruct Hind as [HindEv HindEvop]; simpl in Hev.
      destruct (evalop _) as [| l0] eqn: evop;
      try discriminate.
      destruct l0 as [| v0 l0'].
      (* l0 := [] *)
      + simpl in *. destruct (interp_op _) eqn: eqintop; 
        try discriminate. inversion_subst Hev; 
        eapply EVal_LOp; eauto. apply not_one_error_empty.
      (* l0 := v0::l0 *)
      + apply HindEvop in evop; eauto. 
        pose proof evop as evop'. 
        apply canonical_EValOp_result in evop.
        destruct evop as [Hall | Herr].
        (* v0 := VLit _ /\ all_lit l0 *)
        * inversion_subst Hall.
          destruct H1 as [t Htof]. 
          apply tbase_Typeof_lit in Htof.
          destruct Htof as [x [*]]; subst.
          destruct (interp_op _) eqn: eqintop; 
          try discriminate. inversion_subst Hev;
          eapply EVal_LOp; eauto.
          apply not_one_error_lit.
        (* v0 := VError _ /\ l0 = []*)
        * unfold one_error in Herr; 
          destruct Herr as [m Heq];
          inversion_subst Heq; 
          inversion_subst Hev.   
          constructor; eauto.
    Qed.

    Lemma eval_app_correct: 
      forall s n e1 e2 v, 
       (forall s e v, 
         WFEV s -> 
         eval n e s = Ok v -> 
         EVal e s v) -> 
       WFEV s -> 
       eval (S n) (LApp e1 e2) s = Ok v ->
       EVal (LApp e1 e2) s v.
    Proof. 
      intros * Hind Hwfev Hev; simpl in *.
      destruct (eval _) as [ v0 |] eqn: eqev; 
      try discriminate.
      destruct_elim v0.
      (* v0 := VCls _  *)
      + destruct (eval n e2 s) as [v1 | ] eqn: eqev2. 
        * destruct (is_verror v1) eqn: eqerr.
          (* v1 := VError _ *)
          - destruct_elim v1; inversion_subst Hev; 
            eapply EVal_LAppErr_arg; eauto. 
            constructor.
          (* v1 <> VError _ *)
          - destruct (has_match _) eqn: eqm.
            (* has_match := true *)
            -- apply has_match_correct in eqm.
               destruct typ.
              (* recursive application *)
               {eapply EVal_LAppRec; eauto.
                + apply is_verror_false_not_typeof_terr; 
                  eauto.
                + apply match_env_safe; eauto.
                + apply Hind; destruct_elim v1; eauto;
                  eapply wfev_cls_env_rec_extension; 
                  eauto. }
              (* normal application *)
               {eapply EVal_LApp; eauto.
                + apply is_verror_false_not_typeof_terr; 
                  eauto.
                + apply match_env_safe; eauto.
                + apply Hind; destruct_elim v1; eauto;
                  eapply wfev_cls_env_extension; 
                  eauto. }
            (* has_match := false *)
            -- destruct_elim v1. 
        (* eval n e2 s := Error _ *)
        * discriminate.
      (* v0 := VError _ *)
      + inversion Hev; constructor ; eauto.
    Qed.


     
    Lemma eval_pair_correct: 
      forall s n e1 e2 v, 
       (forall s e v, 
          WFEV s -> 
          eval n e s = Ok v -> 
          EVal e s v) -> 
       WFEV s ->  
       eval (S n) (LPair e1 e2) s = Ok v -> 
       EVal (LPair e1 e2) s v.
    Proof. 
      intros * HInd Hwfev Hev. simpl in Hev. 
      destruct (eval _) eqn: eqv1; try discriminate. 
      destruct (is_verror v0) eqn: eqerr0. 
    (* v0 := VError _ *)
      + destruct_elim v0; inversion_subst Hev; 
        constructor; eauto. 
     (* v0 <> VError _ *)
      + destruct (eval n e2 s) eqn: eqev2.
       (* eval n e2 s := Ok v1 *)
        * destruct (is_verror v1) eqn: eqerr1.
          (* v1 := VError _ *)
          - destruct_elim v0; destruct_elim v1; 
            inversion_subst Hev;  
            eapply EVal_LPairErr_snd; eauto; 
            eapply Typeof_neq_terr; discriminate.
          (* v1 <> VError _ *)
          -  destruct_elim v0; destruct_elim v1;
             inversion_subst Hev.  
             all: eapply EVal_LPair; eauto; 
                 destruct_pairs; try discriminate; 
                 constructor.
        (* eval n e2 s := Error _ *)
        * destruct_elim v0; inversion_subst Hev.
    Qed.


    Lemma eval_cons_result_tail: 
      forall n e1 e2 s v v1 v2, 
       eval (S n) (LCons e1 e2) s = Ok v -> 
       eval n e1 s = Ok v1 ->  
       eval n e2 s = Ok v2 ->
       is_verror v1 = false -> 
       is_verror v2 = false ->
       v2 = VNil \/ (exists v v' t, v2 = VCons v v' t).
    Proof. 
       intros * Hev Hev1 Hev2 Herr1 Herr2.
       simpl in *; rewrite Hev1, Hev2 in Hev.
       destruct_elim v1; destruct_elim v2; 
       eauto.
    Qed. 
         

    Lemma eval_cons_correct: 
      forall n e1 s e2 v,
        (forall s e v, 
          WFEV s -> 
          eval n e s = Ok v -> 
          EVal e s v) -> 
        WFEV s ->    
        eval (S n) (LCons e1 e2) s = Ok v -> 
        EVal (LCons e1 e2) s v.
    Proof.    
      intros * HInd Hwfev Hev. 
      pose proof Hev as Hev'. simpl in Hev. 
      destruct (eval _ ) as [v0 |] eqn : eqev1; try discriminate. 
      destruct (eval n e2 s) as [v1 |] eqn: eqev2.
      (* eval n e2 s := Ok v1   *) 
      + destruct (is_verror v0) eqn: eqerr0. 
        (* v0 := VError _ *)
        * destruct_elim v0.  
          inversion_subst Hev.
          constructor; eauto. 
        (* v0 <> VError _ *)
        * destruct (is_verror v1) eqn: eqerr1.
          (* v1 := VError _ *)
          - destruct_elim v0; destruct_elim v1; 
            inversion_subst Hev;
            eapply EVal_LConsErr_tail ; 
            apply is_verror_false_not_typeof_terr in eqerr0; 
            eauto.
          (* v1 <> VError _ *)
          - assert (H: v1 = VNil \/ 
             (exists v v' t, v1 = VCons v v' t)) 
            by (eapply eval_cons_result_tail; eauto).
            destruct H as [HNil | HCons]. 
            (* v1 := VNil *)
            -- subst; destruct_elim v0; 
               inversion_subst Hev.
               all: eapply EVal_LCons; eauto; 
                    destruct_pairs; 
                    try discriminate;
                    constructor.
            (* v1 := VCons _ *)
            -- destruct HCons as [vh [vt [t HCons]]]. 
               subst; destruct (is_consistent _) eqn: eqc. 
               (* is_consistent = true *)
               ** destruct (nested_empty _) eqn: eqnest.
                  (* nested_empty = true *)
                  {destruct_elim v0; inversion_subst Hev;
                   apply is_consistent_correct in eqc. 
                   all : eapply EVal_LCons_nestt; eauto;
                         destruct_pairs; constructor. }
                  (* nested_empty = false *)
                  {destruct_elim v0; inversion_subst Hev; 
                   apply is_consistent_correct in eqc. 
                   all : eapply EVal_LCons_nestf; eauto; simpl;
                         destruct_pairs; try discriminate; 
                         constructor.  }
              (* is_consistent = false *)
              ** destruct_elim v0; inversion_subst Hev.
      (* v1 := Error _ *)
      + destruct_elim v0; inversion_subst Hev; 
        constructor; eauto.
    Qed.

    
    Lemma eval_variant_correct: 
     forall n s c inf e v,
        (forall s e v, 
          WFEV s -> 
          eval n e s = Ok v -> 
          EVal e s v) -> 
        WFEV s ->    
        eval (S n) (LVariant c inf e) s = Ok v -> 
        EVal (LVariant c inf e) s v.
    Proof. 
      intros * Hind Hwfev Hev .
      simpl in Hev. destruct inf. 
      destruct (eval n e s) eqn: eqev; 
      try discriminate.
      destruct (is_verror v0) eqn: eqerr.
       (* v0 := VError _ *)
      + destruct_elim v0; inversion_subst Hev;  
        constructor; eauto.
      (* v0 <> VError _ *)
      + destruct (is_consistent _) eqn: eqc; 
        destruct_elim v0; inversion_subst Hev; 
        apply is_consistent_correct in eqc.
        all: eapply EVal_LVariant; eauto; simpl; 
             destruct_pairs; try discriminate; 
             constructor.
    Qed.
        

    Lemma eval_fix_correct : 
      forall n s name e v,
        (forall s e v, 
          WFEV s -> 
          eval n e s = Ok v -> 
          EVal e s v) -> 
        WFEV s ->    
        eval (S n) (LFix name e) s = Ok v -> 
        EVal (LFix name e) s v.
    Proof. 
      intros * Hind Hwfev Hev. simpl in Hev.
      destruct (eval _) eqn: eqev; try discriminate.
      destruct_elim v0.
      (* v0 := VCls typ *)
      + destruct_elim typ; inversion_subst Hev; 
        constructor; eauto.
      (* v0 := VError *)
      + inversion_subst Hev; constructor; eauto.
    Qed. 

    
    Lemma eval_match_correct: 
     forall n s e cases v,
        (forall s e v, 
          WFEV s -> 
          eval n e s = Ok v -> 
          EVal e s v) -> 
        WFEV s ->    
        eval (S n) (LMatch e cases) s = Ok v -> 
        EVal (LMatch e cases) s v.
    Proof. 
      intros * Hind Hwfev Hev. simpl in Hev.
      destruct (eval _) eqn: eqev; 
      try discriminate.  
      destruct (is_verror v0) eqn: eqerr.
      (* v0 := VError _ *)
      + destruct_elim v0; inversion_subst Hev; 
        constructor; eauto.
      (* v0 <> VError _  *)
      + destruct (find _) eqn: eqfind.
        (* find = Some p *)
        * pose proof eqfind as eqfind'; 
          eapply FirstMatch_eq_find_match in eqfind; 
          inversion_subst eqfind; 
          destruct_elim v0; destruct p; 
          apply is_verror_false_not_typeof_terr in eqerr; 
          apply FirstMatch_eq_find_match in eqfind';
          eapply EVal_LMatch; eauto; 
          eapply Hind in Hev; eauto;
          try eapply MatchEnv_preservs_wfev; eauto; 
          try eapply match_env_safe; eauto; 
          try eapply EVal_wfv; eauto; 
               eapply FirstMatch_Match; eauto.
        (* find = None *)
        * destruct_elim v0.
    Qed.


    Lemma evalop_correct: 
      forall s n l lv, 
      (forall s e v, 
        WFEV s -> 
        eval n e s = Ok v -> 
        EVal e s v) /\
      (forall s l lv, 
        WFEV s -> 
        evalop n l s = Ok lv -> 
        EValOp l s lv) ->
      WFEV s -> 
      evalop (S n) l s = Ok lv -> 
      EValOp l s lv.
    Proof.
      intros * Hind Hwfev Hev. 
      destruct Hind as [HinEv HinEvop]; simpl in*; 
      destruct l as [| head tail].
      (* l := []  *)
      * inversion_subst Hev; constructor; eauto.
      (* l := head::tail *)
      * destruct (evalop _) as [l' |] eqn: eqevop;
        try discriminate.
        pose proof eqevop as eqvop'; 
        apply HinEvop, canonical_EValOp_result in eqevop;
        eauto. destruct eqevop as [Hall | Herr].
        (* Hall : all_lit l' *)
        - inversion Hall; subst.
          (* l' := [] *)
          {destruct (eval _) eqn: eqev; try discriminate.
            apply HinEvop in eqvop'; 
            inversion_subst eqvop'; eauto.
            destruct_elim v; inversion_subst Hev. 
            (* v := VLit _ *)
            * eapply EValOp_cons; try constructor;  
              eauto; apply not_one_error_empty.
            (* v := VError _ *)
            * eapply EValOpErr_head; try constructor;  
              eauto; apply not_one_error_empty. }
          (* l' := x::l *)
          {destruct H as [t Htof].
            apply tbase_Typeof_lit in Htof. 
            destruct Htof as [* [*]]; subst.   
            destruct (eval _) eqn: eqv; try discriminate. 
            destruct_elim v; inversion_subst Hev.
            (* v := VLit _ *)
            * eapply EValOp_cons; eauto. apply not_one_error_lit. 
            * eapply EValOpErr_head; eauto. apply not_one_error_lit. }
        (* Herr : one_error l' *)
        - unfold one_error in Herr. 
          destruct Herr; subst. 
          inversion_subst Hev; constructor; eauto.
    Qed. 
      


    Theorem eval_evalop_correct : 
      forall n, 
        (forall s e v, 
          WFEV s -> 
          eval n e s = Ok v -> 
          EVal e s v)  /\ 
        (forall s l lv, 
          WFEV s -> 
          evalop n l s = Ok lv  ->
          EValOp l s lv) .
    Proof.
      induction n; 
      split; intros * Hwfev Hev; try discriminate. 
      + generalize dependent s. 
        induction e; intros; destruct IHn; 
        try (inversion_subst Hev; constructor; eauto).
        * simpl in H2. destruct (lookup _) eqn: eqlkp; 
          inversion_subst H2; constructor; eauto.
        * eapply eval_op_correct; eauto.
        * eapply eval_app_correct; eauto.
        * eapply eval_pair_correct; eauto.
        * eapply eval_cons_correct; eauto.
        * eapply eval_variant_correct; eauto.
        * eapply eval_fix_correct; eauto.
        * eapply eval_match_correct; eauto.
      + eapply evalop_correct; eauto.
    Qed. 

 
    Fixpoint depth (e: LExpr) : nat := 
      match e with 
      |LVar _          => 1  
      |LLit _          => 1
      |LOp _ l         => 1 + list_max (map depth l) 
      |LLam _ _        => 1   
      |LApp e1 e2      => 1 + max (depth e1) (depth e1)
      |LUnit           => 1 
      |LNil            => 1 
      |LPair e1 e2     => 1 + max (depth e1) (depth e1)
      |LCons e1 e2     => 1 + max (depth e1) (depth e2)
      |LFix _ e        => 1 + (depth e)
      |LVariant _ _ e  => 1 + (depth e) 
      |LMatch e l      => max (depth e) (list_max (
                            map (fun '(_, e) => depth e) l)) 
      |LError _        => 1
      end.
        

    Theorem eval_evalop_monotone_fuel :  
        forall n, 
          (forall e s v, 
             eval n e s = Ok v -> 
             forall m, n <= m -> eval m e s = Ok v) /\ 
         (forall l s lv, 
             evalop n l s = Ok lv -> 
             forall m, n <= m -> evalop m l s = Ok lv ).
    Proof.  
      intro. induction n; split; try discriminate.
      + intros * Hev * Hleq.
        destruct m; inversion_subst Hleq; eauto.
        (* S n <= m *)
        apply Le.le_Sn_le_stt in H0. 
        destruct IHn as [IHnEv IHnEvop].
        simpl in *. destruct e; eauto.  
        * destruct (evalop n _) eqn: eqevop;  
          try discriminate.
          eapply IHnEvop in eqevop; eauto.
          rewrite eqevop; eauto.
        * destruct (eval n e1 s) eqn: eqev1; try discriminate. 
          eapply IHnEv in eqev1; eauto; rewrite eqev1. 
          destruct_elim v0.
          (* v0 := VCls _ *)
          - destruct (eval n e2 s) as [v1 |] eqn: eqev2.
            (* eqev2 := Ok v1 *)
            ** eapply IHnEv in eqev2; eauto. rewrite eqev2.  
               destruct (is_verror v1) eqn: eqerr. 
              (* v1 := VError _  *)
              -- destruct_elim v1. inversion_subst Hev.
                 reflexivity.
              (* v1 <> VError _ *)
              -- destruct (has_match _) eqn: eqm.
                (* has_match = true *)
                 --- destruct typ eqn: eqt; 
                     destruct_elim v1; eapply IHnEv; eauto.
                (* has_match = false *)
                 --- destruct_elim v1. 
           (* eqev2 := Error _ *)
            ** discriminate.
         (* v0 := VError _ *)
          - inversion_subst Hev. constructor.
        *       

            
          (* eqev2 := Ok _ *)
          - eapply IHnEv in eqev2; eauto. rewrite eqev2.
            destruct_elim v0.

          eauto.
        *  
           
      simpl in *; destruct e. 


      
    Theorem eval_evalop_complete: 
      forall e s v, 
        EVal e s v -> 
        exists n, eval n e s = Ok v. 
    Proof. 
      intros * HEv. induction HEv using EVal_mut 
       with (P0 := fun l s lv _ => 
         EValOp l s lv -> 
         exists n, evalop n l s = Ok lv). 
      + exists 1. simpl. rewrite e. reflexivity. 
      + exists 1. eauto. 
      + apply IHHEv in e. destruct e as [n' e]. 
        exists (S n'). simpl. rewrite e, e0.
        destruct_elim lv; eauto .
        destruct_elim v0; eauto.
        destruct_elim lv ;eauto.
        apply one_error_contra in n. contradiction.
      + apply IHHEv in e. destruct e as [n' e]. 
        exists (S n'). simpl. rewrite e. reflexivity.
      + exists 1. eauto.
      + destruct IHHEv1 as [n1 Heq1].
        exists (S n1). simpl. rewrite Heq1.  



                     






































    
           
           
          
      
      
                    

                        


End EVALUATION.