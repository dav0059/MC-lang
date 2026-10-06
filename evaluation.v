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
Require Import PeanoNat.
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

    Ltac discard_case := 
     simpl in *; try discriminate; 
     try contradiction.

    Ltac discard_case_m_using H := 
     try (apply Nat.nlt_0_r in H; contradiction).

    Ltac solve_n_lt_m := 
     eapply Arith_prebase.lt_S_n_stt; eauto.

       
   
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
                     EValOp le s lv ->
                     ~one_error lv ->  
                     interp_op op (getBaseVl lv) = Some v ->
                     EVal (LOp op le) s (VLit v) 
    |EVal_LOpErr   : forall s le op mssg, 
                     WFEV s -> 
                     EValOp le s [VError mssg] ->
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
    |EVal_LAppErr_fun : forall s e1 e2 mssg, 
                        WFEV s -> 
                        EVal e1 s (VError mssg) -> 
                        EVal (LApp e1 e2) s (VError mssg) 
    |EVal_LAppErr_arg : forall s e1 v e2 mssg, 
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
    |EVal_LCons       : forall s e1 v1 t1 e2,  
                        WFEV s -> 
                        EVal e1 s v1 -> 
                        Typeof v1 t1 -> 
                        t1 <> KTError -> 
                        EVal e2 s VNil -> 
                        EVal (LCons e1 e2) s (VCons v1 VNil t1)
    |EVal_LCons_nestt : forall s e1 v1 t1 e2 v2 t, 
                        WFEV s -> 
                        EVal e1 s v1 ->
                        Typeof v1 t1 ->
                        EVal e2 s v2 ->
                        Typeof v2 (KTList t) -> 
                        Consistent t1 t ->
                        nested_empty t = true ->  
                        EVal (LCons e1 e2) s (VCons v1 v2 t1)
    |EVal_LCons_nestf : forall s e1 v1 t1 e2 v2 t, 
                        WFEV s -> 
                        EVal e1 s v1 -> 
                        Typeof v1 t1 -> 
                        t1 <> KTError -> 
                        EVal e2 s v2 -> 
                        Typeof v2 (KTList t) -> 
                        Consistent t1 t -> 
                        nested_empty t = false -> 
                        EVal (LCons e1 e2) s (VCons v1 v2 t)
    |EVal_LConsErr_head : forall s e1 mssg e2, 
                          WFEV s -> 
                          EVal e1 s (VError mssg) ->
                          EVal (LCons e1 e2) s (VError mssg)
    |EVal_LConsErr_tail : forall e1 s v1 e2 mssg , 
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
     |EValOp_cons     : forall s head x tail tail',
                        WFEV s -> 
                        EVal head s (VLit x) ->
                        EValOp tail s tail' -> 
                        ~one_error tail' ->  
                        EValOp (head::tail) s (VLit x::tail') 
     |EValOpErr_tail : forall s head x tail mssg, 
                        WFEV s ->   
                        EVal head s (VLit x) ->
                        EValOp tail s [VError mssg] -> 
                        EValOp (head::tail) s [VError mssg] 
     |EValOpErr_head : forall s head mssg tail,
                        WFEV s ->  
                        EVal head s (VError mssg) ->
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
        left. apply IHl in H3. destruct H3; try contradiction.
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
        inversion_subst H. inversion_subst H3.
        inversion_subst H0. inversion H. 
    Qed.


    Corollary EValOp_result_all_lit: forall l s l', 
      EValOp l s l' -> 
      ~one_error l' -> 
      all_lit l'.
    Proof.
      intros * Hevop Hnerr. 
      apply canonical_EValOp_result in Hevop. 
      destruct Hevop; eauto. contradiction.
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
          
      

    (* the evaluation semantics produces well-formed values *)
    Theorem EVal_wfv: forall e s v, 
      EVal e s v -> 
      WFV v. 
    Proof. 
      intros * HEv. 
      induction HEv using EVal_mut with 
       (P0 := fun l s l' _ => EValOp l s l' -> 
         Forall (fun v => WFV v) l');      
      eauto; try constructor; eauto. 
      (* EVal_LVar *)
      + induction w; subst; unfold lookup, empty_env in e. 
        discriminate. unfold bind in e.
        destruct (id_eqb i i0) eqn: eqid; 
        inversion_subst e; eauto.
      (* EVal_LCons *)
      + eapply WFV_VCons; eauto. constructor.
        * apply consistent_refl; eauto.
          apply Typeof_is_FOT with (v := v1); eauto.
        * apply c_TListNil1, Typeof_is_FOT with (v := v1); eauto.
      (* EVal_LCons_nestt *)
      + eapply WFV_VCons; eauto.
        * apply consistent_refl, Typeof_is_FOT with (v := v1); eauto.
        * apply c_TList, consistent_sym; eauto.
      (* EVal_LCons_nestf *)
      + eapply WFV_VCons; eauto.
        apply c_TList, consistent_refl. 
        apply consistent_is_FOT in c; destruct c; eauto.
      (* EVal_LVariant *)
      + eapply WFV_VVariant; eauto.
        apply consistent_sym; eauto.
      (* EVal_LFix *)
      + inversion IHHEv; eauto.
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
              |LOp op l   => let lv := evalop n' l s in
                             match lv with 
                             |Error mssg       => Error mssg 
                             |Ok [VError mssg] => Ok (VError mssg) 
                             |Ok (_ as lv)  => 
                               match interp_op op (getBaseVl lv) with 
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
                  match eval n' h s with 
                  |Error mssg       => Error mssg 
                  |Ok (VError mssg) => Ok [VError mssg]
                  |Ok (VLit x)           => 
                    match evalop n' t s with 
                    |Error mssg       => Error mssg 
                    |Ok [VError mssg] => Ok [VError mssg]
                    |Ok lv            => Ok(VLit x::lv)
                    end            
                  |_                => 
                    Error("Illegal primitive operation construction"%string)
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
      * destruct (eval _) as [v |] eqn: eqev;
        try discriminate.
        pose proof eqev as eqev'; destruct_elim v.
        (* v := VLit x *)
        - destruct (evalop _) as [lv'|] eqn: eqevop; 
          discard_case. pose proof eqevop as eqevop'.
          destruct lv' as [|v lvt']; 
          inversion_subst Hev.
          (* lv' :=  [] *)
          -- constructor; eauto. apply not_one_error_empty.
          (* lv' := v::lvt' *) 
          -- eapply HinEvop, canonical_EValOp_result in eqevop;
             eauto. destruct eqevop as [Hall | Herr].
             (* Hall : all_lit l' *)
             {unfold all_lit in Hall. inversion_subst Hall.
              destruct H2 as [t Htof]. 
              apply tbase_Typeof_lit in Htof.
              destruct Htof as [x' [eqv _]]. subst.
              inversion_subst H0. constructor; eauto. 
              apply not_one_error_lit. }
             (* Herr : one_error (v::lvt') *)
             {unfold one_error in Herr. 
              destruct Herr as [m Herr]; inversion_subst Herr.
              inversion_subst H0. eapply EValOpErr_tail; 
              eauto. }
        (* v := VError m *)
        - inversion_subst Hev. constructor; eauto.    
      Qed. 
      

    (* the fuelled interpreter is correct w.r.t evaluation semantics *)
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


    Corollary eval_correct: 
      forall n s e v, 
        WFEV s -> 
        eval n e s = Ok v -> 
        EVal e s v.
    Proof. 
     apply eval_evalop_correct.
    Qed.  
 
      
    (* MeasureEVal H n means that n is a uniform fuel bound 
       for the recursive subderivations of the EVal derivation H. *)
    Inductive MeasureEVal : forall e s v, EVal e s v -> nat -> Prop :=
    |Measure_EVal_Var : 
       forall i s v n (Hwfev : WFEV s)
                    (Hlookup : lookup s i = Some v),
          1 <= n -> 
          MeasureEVal (@EVal_Var i s v Hwfev Hlookup) n
    |Measure_EVal_Lit : 
       forall x s n (Hwfev : WFEV s),
          1 <= n ->
          MeasureEVal (@EVal_Lit x s Hwfev) n 
    |Measure_EVal_LOp :
        forall s le lv op v n
              (Hwfev : WFEV s)
              (Hop : EValOp le s lv)
              (Herr : ~ one_error lv)
              (HInt : interp_op op (getBaseVl lv) = Some v),
          MeasureEValOp Hop n ->
          MeasureEVal
            (@EVal_LOp s le lv op v Hwfev Hop Herr HInt)
            (S n)
    |Measure_EVal_LOpErr :
        forall s le op mssg n
              (Hwfev : WFEV s)
              (Hop : EValOp le s [VError mssg]),
          MeasureEValOp Hop n ->
          MeasureEVal
            (@EVal_LOpErr s le op mssg Hwfev Hop)
            (S n)

    |Measure_EVal_LLam :
        forall s arg body n (Hwfev : WFEV s),
          1 <= n -> 
          MeasureEVal (@EVal_LLam s arg body Hwfev) n

    |Measure_EVal_LApp :
        forall s e1 arg body cls_env
              e2 v cls_env' v' n
              (Hwfev : WFEV s)
              (Hfun : EVal e1 s
                       (VCls NotRecursive arg body cls_env))
              (Harg : EVal e2 s v)
              (Hnoterr : ~ Typeof v KTError)
              (Hmatch : Match arg v)
              (Henv : MatchEnv arg v cls_env cls_env')
              (Hbody : EVal body cls_env' v'),
          MeasureEVal Hfun n ->
          MeasureEVal Harg n ->
          MeasureEVal Hbody n ->
          MeasureEVal
            (@EVal_LApp s e1 arg body cls_env
              e2 v cls_env' v'
              Hwfev Hfun Harg Hnoterr Hmatch Henv Hbody)
            (S n)

    |Measure_EVal_LAppRec :
        forall s e1 name arg body cls_env
              e2 v cls_env' v' n 
              (Hwfev : WFEV s)
              (Hfun :
                  EVal e1 s
                    (VCls (Recursive name) arg body cls_env))
              (Harg : EVal e2 s v)
              (Hnoterr : ~ Typeof v KTError)
              (Hmatch : Match arg v)
              (Henv : MatchEnv arg v cls_env cls_env')
              (Hbody :
                  EVal body
                    (bind cls_env' name
                      (VCls (Recursive name) arg body cls_env)
                      id_eqb)
                    v'),
          MeasureEVal Hfun n ->
          MeasureEVal Harg n ->
          MeasureEVal Hbody n ->
          MeasureEVal
            (@EVal_LAppRec s e1 name arg body cls_env
              e2 v cls_env' v'
              Hwfev Hfun Harg Hnoterr Hmatch Henv Hbody)
            (S n) 

    |Measure_EVal_LAppErr_fun :
        forall s e1 e2 mssg n
              (Hwfev : WFEV s)
              (Hfun : EVal e1 s (VError mssg)),
          MeasureEVal Hfun n ->
          MeasureEVal
            (@EVal_LAppErr_fun s e1 e2 mssg Hwfev Hfun)
            (S n)

    |Measure_EVal_LAppErr_arg :
        forall s e1 v e2 mssg n
              (Hwfev : WFEV s)
              (Hfun : EVal e1 s v)
              (Htype : Typeof v KTFunction)
              (Harg : EVal e2 s (VError mssg)),
          MeasureEVal Hfun n ->
          MeasureEVal Harg n ->
          MeasureEVal
            (@EVal_LAppErr_arg s e1 v e2 mssg
              Hwfev Hfun Htype Harg)
            (S n)

    |Measure_EVal_LUnit :
        forall s n
              (Hwfev : WFEV s),
          1 <= n -> 
          MeasureEVal (@EVal_LUnit s Hwfev) n

    |Measure_EVal_LNil :
        forall s n 
              (Hwfev : WFEV s),
          1 <= n -> 
          MeasureEVal (@EVal_LNil s Hwfev) n

    |Measure_EVal_LPair :
        forall s e1 e2 v1 t1 v2 t2 n
              (Hwfev : WFEV s)
              (Hfst : EVal e1 s v1)
              (Htype1 : Typeof v1 t1)
              (Hnoterr1 : t1 <> KTError)
              (Hsnd : EVal e2 s v2)
              (Htype2 : Typeof v2 t2)
              (Hnoterr2 : t2 <> KTError),
          MeasureEVal Hfst n ->
          MeasureEVal Hsnd n ->
          MeasureEVal
            (@EVal_LPair s e1 e2 v1 t1 v2 t2
              Hwfev Hfst Htype1 Hnoterr1
              Hsnd Htype2 Hnoterr2)
            (S n)

    |Measure_EVal_LPairErr_fst :
        forall e1 s mssg e2 n
              (Hwfev : WFEV s)
              (Hfst : EVal e1 s (VError mssg)),
          MeasureEVal Hfst n ->
          MeasureEVal
            (@EVal_LPairErr_fst e1 s mssg e2 Hwfev Hfst)
            (S n)

    |Measure_EVal_LPairErr_snd :
        forall s e1 v e2 mssg n
              (Hwfev : WFEV s)
              (Hfst : EVal e1 s v)
              (Hnoterr : ~ Typeof v KTError)
              (Hsnd : EVal e2 s (VError mssg)),
          MeasureEVal Hfst n ->
          MeasureEVal Hsnd n ->
          MeasureEVal
            (@EVal_LPairErr_snd s e1 v e2 mssg
              Hwfev Hfst Hnoterr Hsnd)
            (S n)

    |Measure_EVal_LCons :
        forall s e1 v1 t1 e2 n
              (Hwfev : WFEV s)
              (Hhead : EVal e1 s v1)
              (Htype : Typeof v1 t1)
              (Hnoterr : t1 <> KTError)
              (Htail : EVal e2 s VNil),
          MeasureEVal Hhead n ->
          MeasureEVal Htail n ->
          MeasureEVal
            (@EVal_LCons s e1 v1 t1 e2
              Hwfev Hhead Htype Hnoterr Htail)
            (S n)

    |Measure_EVal_LCons_nestt :
        forall s e1 v1 t1 e2 v2 t n
              (Hwfev : WFEV s)
              (Hhead : EVal e1 s v1)
              (Htype1 : Typeof v1 t1)
              (Htail : EVal e2 s v2)
              (Htype2 : Typeof v2 (KTList t))
              (Hconsistent : Consistent t1 t)
              (Hnested : nested_empty t = true),
          MeasureEVal Hhead n ->
          MeasureEVal Htail n ->
          MeasureEVal
            (@EVal_LCons_nestt s e1 v1 t1 e2 v2 t
              Hwfev Hhead Htype1 Htail Htype2
              Hconsistent Hnested)
            (S n)

    |Measure_EVal_LCons_nestf :
        forall s e1 v1 t1 e2 v2 t n
              (Hwfev : WFEV s)
              (Hhead : EVal e1 s v1)
              (Htype1 : Typeof v1 t1)
              (Hnoterr : t1 <> KTError)
              (Htail : EVal e2 s v2)
              (Htype2 : Typeof v2 (KTList t))
              (Hconsistent : Consistent t1 t)
              (Hnested : nested_empty t = false),
          MeasureEVal Hhead n ->
          MeasureEVal Htail n ->
          MeasureEVal
            (@EVal_LCons_nestf s e1 v1 t1 e2 v2 t
              Hwfev Hhead Htype1 Hnoterr Htail Htype2
              Hconsistent Hnested)
            (S n)

    |Measure_EVal_LConsErr_head :
        forall s e1 mssg e2 n
              (Hwfev : WFEV s)
              (Hhead : EVal e1 s (VError mssg)),
          MeasureEVal Hhead n ->
          MeasureEVal
            (@EVal_LConsErr_head s e1 mssg e2 Hwfev Hhead)
            (S n)

    |Measure_EVal_LConsErr_tail :
        forall e1 s v1 e2 mssg n
              (Hwfev : WFEV s)
              (Hhead : EVal e1 s v1)
              (Hnoterr : ~ Typeof v1 KTError)
              (Htail : EVal e2 s (VError mssg)),
          MeasureEVal Hhead n ->
          MeasureEVal Htail n ->
          MeasureEVal
            (@EVal_LConsErr_tail e1 s v1 e2 mssg
              Hwfev Hhead Hnoterr Htail)
            (S n)

    |Measure_EVal_LVariant :
        forall s e v t' t c i n
              (Hwfev : WFEV s)
              (He : EVal e s v)
              (Htype : Typeof v t')
              (Hnoterr : t' <> KTError)
              (Hconsistent : Consistent t t'),
          MeasureEVal He n ->
          MeasureEVal
            (@EVal_LVariant s e v t' t c i
              Hwfev He Htype Hnoterr Hconsistent)
            (S n)

    |Measure_EVal_LVariantErr :
        forall e s mssg c inf n
              (Hwfev : WFEV s)
              (He : EVal e s (VError mssg)),
          MeasureEVal He n ->
          MeasureEVal
            (@EVal_LVariantErr e s mssg c inf Hwfev He)
            (S n)

    |Depth_EVal_LFix :
        forall s e arg body cls_env name n
              (Hwfev : WFEV s)
              (He :
                  EVal e s
                    (VCls NotRecursive arg body cls_env)),
          MeasureEVal He n ->
          MeasureEVal
            (@EVal_LFix s e arg body cls_env name Hwfev He)
            (S n)

    |Measure_EVal_LFixErr :
        forall e s mssg name n
              (Hwfev : WFEV s)
              (He : EVal e s (VError mssg)),
          MeasureEVal He n ->
          MeasureEVal
            (@EVal_LFixErr e s mssg name Hwfev He)
            (S n)

    |Measure_EVal_LMatch :
        forall s e v p' e' s' v' l n
              (Hwfev : WFEV s)
              (He : EVal e s v)
              (Hnoterr : ~ Typeof v KTError)
              (Hfirst : FirstMatch v l (Some (p', e')))
              (Henv : MatchEnv p' v s s')
              (Hbranch : EVal e' s' v'),
          MeasureEVal He n ->
          MeasureEVal Hbranch n ->
          MeasureEVal
            (@EVal_LMatch s e v p' e' s' v' l
              Hwfev He Hnoterr Hfirst Henv Hbranch)
            (S n) 

    |Measure_EVal_LMatchErr :
        forall e s m l n
              (Hwfev : WFEV s)
              (He : EVal e s (VError m)),
          MeasureEVal He n ->
          MeasureEVal
            (@EVal_LMatchErr e s m l Hwfev He)
            (S n)

    |Measure_EVal_Error :
        forall s m n
              (Hwfev : WFEV s),
          1 <= n -> 
          MeasureEVal (@EVal_LError s m Hwfev) n 

    with MeasureEValOp :
      forall l s lv, EValOp l s lv -> nat -> Prop :=

    |Measure_EValOp_Nil :
        forall s n 
              (Hwfev : WFEV s),
          1 <= n ->   
          MeasureEValOp (@EValOp_nil s Hwfev) n 

    |Measure_EValOp_cons :
        forall s head x tail tail' n
              (Hwfev : WFEV s)
              (Hhead : EVal head s (VLit x))
              (Htail : EValOp tail s tail')
              (Hnoterr : ~ one_error tail'),
          MeasureEValOp Htail n ->
          MeasureEVal Hhead n ->
          MeasureEValOp
            (@EValOp_cons s head x tail tail'
              Hwfev Hhead Htail Hnoterr)
            (S n)

    |Measure_EValOpErr_tail :
        forall s head x tail mssg n
              (Hwfev : WFEV s)
              (Hhead : EVal head s (VLit x))
              (Htail : EValOp tail s [VError mssg]),
          MeasureEVal Hhead n ->
          MeasureEValOp Htail n ->
          MeasureEValOp
            (@EValOpErr_tail s head x tail mssg
              Hwfev Hhead Htail)
            (S n)

    |Measure_EValOpErr_head :
        forall s head mssg tail n
              (Hwfev : WFEV s)
              (Hhead : EVal head s (VError mssg)),
          MeasureEVal Hhead n ->
          MeasureEValOp
            (@EValOpErr_head s head mssg tail 
              Hwfev Hhead)
            (S n).

     
    Scheme MeasureEVal_mut := Induction for MeasureEVal Sort Prop
    with MeasureEValOp_mut := Induction for MeasureEValOp Sort Prop.


    (* the fueled interpreter evaluates every finite Eval 
       derivation H whenever its fuel satisfies MeasureEval H. *)
    Theorem eval_complete: 
       forall e s v (H: EVal e s v) n,  
          MeasureEVal H n -> 
          eval n e s = Ok v .
    Proof.
      intros * HMEv.
      induction HMEv using MeasureEVal_mut with ( 
         P0 := fun l s lv H n _ =>     
            evalop n l s = Ok lv); intros.
      (* EVal_LVar *)
      + destruct n. inversion l.
        simpl. rewrite Hlookup. reflexivity.
      (* EVal_Lit *)
      + destruct n. inversion l. eauto. 
      (* EVal_LOp *)
      + simpl. rewrite IHHMEv. 
        destruct lv as [| hv tv] . 
        (* lv := [] *)
        - simpl in *. rewrite HInt. reflexivity.
        (* lv := hv::tv *)
        - pose proof Hop as Hop'. 
          apply canonical_EValOp_result in Hop'.
          destruct Hop' as [Hall | *]; try contradiction.
          inversion_subst Hall. destruct H1 as [t H1]; 
          apply tbase_Typeof_lit in H1; 
          destruct H1 as [x []]; subst. 
          destruct (interp_op _) eqn: eqint; try discriminate.
          inversion_subst HInt; eauto.
      (* EVal_LOpErr *)
      + simpl. rewrite IHHMEv. reflexivity.
      (* EVal_LLam *)
      + destruct n. inversion l. eauto.
      (* EVal_LApp *)
      + simpl. rewrite IHHMEv1, IHHMEv2.
        destruct (is_verror v) eqn: eqerr.
        (* v := VError _ *)
        * destruct_elim v. 
          apply is_verror_false_not_typeof_terr in Hnoterr.
          rewrite eqerr in Hnoterr; discriminate.
        (* v <> VError _ *)
        * assert (H: MatchEnv arg v cls_env 
                     (match_env arg v cls_env)) by 
          (apply match_env_safe; eauto).
          assert (cls_env' = match_env arg v cls_env) by 
          (eapply MatchEnv_deterministic; eauto); subst.
          rewrite IHHMEv3. apply has_match_complete in Hmatch.
          rewrite Hmatch; destruct_elim v; reflexivity.
      (* EVal_LAppRec *)
      + simpl. rewrite IHHMEv1, IHHMEv2.
        destruct (is_verror v) eqn: eqerr.
        (* v := VError _ *)
        * destruct_elim v. 
          apply is_verror_false_not_typeof_terr in Hnoterr.
          rewrite eqerr in Hnoterr; discriminate.
        (* v <> VError _ *)
        * assert (H: MatchEnv arg v cls_env 
                     (match_env arg v cls_env)) by 
          (apply match_env_safe; eauto).
          assert (cls_env' = match_env arg v cls_env) by 
          (eapply MatchEnv_deterministic; eauto); subst.
          rewrite IHHMEv3. apply has_match_complete in Hmatch.
          rewrite Hmatch; destruct_elim v; reflexivity.
      (* EVal_LAppErr_fun *)
      + simpl. rewrite IHHMEv. reflexivity. 
      (* EVal_LAppErr_arg *)
      + simpl. rewrite IHHMEv1. 
        destruct v; try inversion_subst Htype.
        rewrite IHHMEv2. reflexivity.
      (* EVal_LUnit *)
      + destruct n. inversion l. simpl. reflexivity.
      (* EVal_LNil *)
      + destruct n. inversion l. simpl. reflexivity.
      (* EVal_LPair *)
      + simpl. rewrite IHHMEv1, IHHMEv2.
        destruct (is_verror v1) eqn: eqerr.
        (* v1 := VError _ *)
        * destruct_elim v1. inversion_subst Htype1; 
          contradiction.
        (* v1 <> VError _ *)
        * destruct_elim v1;  
          eapply typeof_complete in Htype1, Htype2; 
          subst; simpl; destruct_elim v2; try reflexivity; 
          contradiction.
      (* EVal_LPairErr_fst *)
      + simpl. rewrite IHHMEv. reflexivity. 
      (* EVal_LPairErr_snd *)
      + simpl. rewrite IHHMEv1, IHHMEv2. 
        destruct_elim v; try reflexivity.
        rewrite <- Typeof_neq_terr in Hnoterr.
        specialize Hnoterr with m; contradiction.
      (* EVal_LCons *)
      + simpl. rewrite IHHMEv1, IHHMEv2.
        destruct (is_verror v1) eqn: eqerr1. 
        (* v1 := VError _ *)
        * destruct_elim v1. inversion_subst Htype.
          contradiction.
        (* v1 <> VError _ *)
        * apply typeof_complete in Htype; subst.
          destruct_elim v1; reflexivity.
      (* EVal_LCons_nestt *)
      + simpl. rewrite IHHMEv1, IHHMEv2.
        destruct (is_verror v1) eqn: eqerr1.
        (* v1 := VError _ *)
        * destruct_elim v1. inversion_subst Htype1.
          inversion_subst Hconsistent. discriminate.
        (* v1 <> VError _ *)
        * destruct_elim v1; destruct (is_verror v2) eqn:eqerr2;
          (* v2 := VError _ *)
          try (destruct_elim v2; inversion_subst Htype2); 
          (* v2 := VNil *)
          try discriminate; 
          (* v2 := VCons *)
          apply typeof_complete in Htype1; subst;
          apply is_consistent_complete in Hconsistent; 
          rewrite Hconsistent, Hnested; reflexivity.
      (* EVal_LCons_nestf *)
      + simpl. rewrite IHHMEv1, IHHMEv2.
        destruct (is_verror v1) eqn: eqerr1.
        (* v1 := VError _ *)
        * destruct_elim v1. inversion_subst Htype1.
          inversion_subst Hconsistent. contradiction. 
        (* v1 <> VError _ *)
        * destruct_elim v1; destruct (is_verror v2) eqn:eqerr2;
          (* v2 := VError _ *)
          try (destruct_elim v2; inversion_subst Htype2); 
          (* v2 := VNil *)
          pose proof Htype1 as Htype1';
          pose proof Hconsistent as Hconsistent';
          try (inversion_subst Htype1; inversion_subst Hconsistent); 
          (* v2 := VCons *)
          apply typeof_complete in Htype1'; subst;
          apply is_consistent_complete in Hconsistent'; 
          eauto; simpl in *; rewrite Hconsistent'; eauto; 
          try discriminate; rewrite Hnested; eauto.
      (* EVal_LConsErr_head *)
      + simpl. rewrite IHHMEv. reflexivity.
      (* EVal_LConsErr_tail *)
      + simpl. rewrite IHHMEv1, IHHMEv2. 
        destruct_elim v1; eauto. 
        rewrite <- Typeof_neq_terr in Hnoterr.
        specialize Hnoterr with m. contradiction.
      (* EVal_LVariant *)
      + simpl. rewrite IHHMEv. destruct (is_verror v) eqn: eqerr.
        (* v := VError _ *)
        * destruct_elim v. inversion_subst Htype.
          contradiction.
        (* v <> VError _ *)
        * apply is_consistent_complete in Hconsistent. 
          apply typeof_complete in Htype; subst.
          rewrite Hconsistent. 
          destruct_elim v; reflexivity.
      (* EVal_LVariantErr *)
      + simpl. destruct inf. rewrite IHHMEv. reflexivity.
      (* EVal_LFix *)
      + simpl. rewrite IHHMEv. reflexivity.
      (* EVal_LFixErr *)
      + simpl. rewrite IHHMEv. reflexivity.
      (* EVal_LMatch *)
      + simpl. rewrite IHHMEv1. pose proof Hfirst as Hfirst'. 
        apply FirstMatch_eq_find_match in Hfirst. 
        rewrite Hfirst. apply FirstMatch_Match in Hfirst'. 
        rewrite <- match_env_safe in Henv; eauto; subst.
        rewrite IHHMEv2; destruct_elim v; try reflexivity.
        (* v := VError _ *)
        rewrite <- Typeof_neq_terr in Hnoterr.
        specialize Hnoterr with m. contradiction.
      (* EVal_LMatchErr *)
      + simpl. rewrite IHHMEv. reflexivity. 
      (* EVal_LError *)
      + destruct n. inversion l. eauto.
      (* EValOp_Nil *)
      + destruct n. inversion l. eauto.
      (* EValOp_cons *)
      + simpl. rewrite IHHMEv0, IHHMEv.
        destruct tail' as [| h t]; eauto.
        destruct (is_verror h) eqn: eqerr.
        (* h := VError _ *)
        destruct_elim h. destruct t; eauto.
        apply one_error_contra in Hnoterr. 
        contradiction.
        (* h <> VError *)
        * destruct_elim h; reflexivity.
      (* EValOpErr_tail *)
      + simpl. rewrite IHHMEv, IHHMEv0.
        reflexivity.
      (* EValOpErr_head *)
      + simpl. rewrite IHHMEv. reflexivity.
  Qed.


    

  Theorem eval_evalop_fuel_monotonic: 
    forall n, 
      (forall e s v, 
        eval n e s = Ok v -> 
        forall m, m > n -> eval m e s = Ok v) /\ 
      (forall l s lv, 
        evalop n l s = Ok lv -> 
        forall m, m > n -> evalop m l s = Ok lv).
  Proof.
    induction n; intros ; split; discard_case; 
    destruct IHn as [IHnev IHnevop].
    (* eval *)
    + intros * Hev * Hlt. destruct e; simpl.
      (* e := LVar x *)
      * destruct (lookup _) eqn: eqlkp; discard_case.
        inversion_subst Hev. destruct m; 
        discard_case_m_using Hlt.
        simpl. rewrite eqlkp. reflexivity.
      (* e := LLit x *)
      * inversion_subst Hev. destruct m; 
        discard_case_m_using Hlt; eauto. 
      (* e := LOp op args *)
      * destruct (evalop n _) eqn: eqevop; discard_case.
        destruct m; discard_case_m_using Hlt. simpl.
        eapply IHnevop in eqevop. rewrite eqevop. eauto.
        solve_n_lt_m.
      (* e := LLam p e *)
      * inversion_subst Hev. destruct m; 
        discard_case_m_using Hlt; simpl; eauto.
      (* e := LApp e1 e2 *)
      * destruct m; discard_case_m_using Hlt.
        simpl. destruct (eval n _) as [v1 |] eqn: eqev1; 
        discard_case. destruct (is_verror v1) eqn: eqerr.
        (* v1 := VError _ *)
        - destruct_elim v1. eapply IHnev in eqev1; 
          try solve_n_lt_m. rewrite eqev1. eauto.
        (* v1 <> VError _ *)
        - destruct_elim v1. eapply IHnev in eqev1; 
          try solve_n_lt_m. rewrite eqev1. 
          destruct (eval n e2 _) as [v2|] eqn: eqev2; 
          discard_case. destruct (is_verror v2) eqn: eqerr2.
          (* v2 := VError _ *)
          -- destruct_elim v2. eapply IHnev in eqev2; 
             try solve_n_lt_m. rewrite eqev2. eauto.
          (* v2 <> VError _ *)
          -- eapply IHnev in eqev2; try solve_n_lt_m.
             rewrite eqev2; eauto. 
             destruct (has_match _) eqn: eqm.
             (* has_match = true *)
             ** destruct typ; destruct_elim v2; 
                eapply IHnev in Hev; try solve_n_lt_m; eauto.
             (* has_match = false *)
             ** destruct_elim v2.
      (* e := LUnit *)
      * destruct m; discard_case_m_using Hlt. eauto.
      (* e := LNil *)
      * destruct m; discard_case_m_using Hlt. eauto.
      (* e := LPair e1 e2 *)
      * destruct m; discard_case_m_using Hlt; simpl.
        destruct (eval n _) as [v1|] eqn: eqev1; 
        discard_case. eapply IHnev in eqev1; 
        try solve_n_lt_m; rewrite eqev1.
        destruct (is_verror v1) eqn: eqerr. 
        (* v1 := VError _ *)
        - destruct_elim v1. eauto.
        (* v1 <> VError _ *)
        -  destruct_elim v1; 
           destruct (eval n e2 _) eqn: eqev2; discard_case; 
           eapply IHnev in eqev2; try solve_n_lt_m; 
           rewrite eqev2; eauto.
      * destruct m; discard_case_m_using Hlt; simpl.
        destruct (eval n _) as [v1|] eqn: eqev1; 
        discard_case. eapply IHnev in eqev1; 
        try solve_n_lt_m; rewrite eqev1.
        destruct (is_verror v1) eqn: eqerr. 
        (* v1 := VError _ *)
        - destruct_elim v1; eauto.
        (* v1 <> VError _ *)
        - destruct (eval n e2 _) as [v2|] eqn: eqev2; 
          destruct_elim v1; eauto; 
          eapply IHnev in eqev2; try solve_n_lt_m;
          rewrite eqev2; eauto.
      (* e := LVariant _ *)
      * destruct m; discard_case_m_using Hlt. 
        simpl. destruct inf. 
        destruct (eval n _) eqn: eqev; discard_case. 
        eapply IHnev in eqev; try solve_n_lt_m. 
        rewrite eqev; eauto.
      (* e := LFix _  *)
      * destruct m; discard_case_m_using Hlt. 
        simpl. destruct (eval n _) eqn: eqev; 
        discard_case. eapply IHnev in eqev; 
        try solve_n_lt_m; rewrite eqev; eauto.
      (* e := LMatch e cases *)
      * destruct m; discard_case_m_using Hlt. 
        simpl. destruct (eval n _) as [v1|] eqn: eqev; 
        discard_case. eapply IHnev in eqev; 
        try solve_n_lt_m; rewrite eqev.
        destruct (is_verror v1) eqn: eqerr. 
       (* v1 := VError _ *)
        - destruct_elim v1; eauto. 
       (* v1 <> VError _ *)
        - destruct_elim v1; 
          destruct (find _) as [(p, e')|] eqn: eqf; 
          discard_case; eapply IHnev in Hev; try solve_n_lt_m;
          rewrite Hev; eauto.
      * destruct m; discard_case_m_using Hlt; eauto.
   (* evalop *)
   + intros * Hev * Hlt. destruct m; 
      discard_case_m_using Hlt. simpl; 
      destruct l; eauto.  
      destruct (eval n _) eqn: eqev; discard_case. 
      eapply IHnev in eqev; try solve_n_lt_m. 
      rewrite eqev. destruct (evalop n _) eqn: eqevop.
      - eapply IHnevop in eqevop; try solve_n_lt_m; 
        rewrite eqevop; eauto.
      - destruct_elim v. eauto. 
  Qed.


   Corollary eval_fuel_monotonic: 
    forall n e s v, 
        eval n e s = Ok v -> 
        forall m, m > n -> eval m e s = Ok v. 
   Proof.
    intros. 
    eapply eval_evalop_fuel_monotonic; eauto.
   Qed.  


   (* the evaluation semantic is deterministic *)
    Corollary EVal_deterministic : 
      forall e s v v' 
            (H: EVal e s v) (H': EVal e s v') n n',
      WFEV s ->  
      MeasureEVal H n -> 
      MeasureEVal H' n' ->
      v = v'. 
    Proof. 
      intros * Hwfev HMe1 HMe2.
      eapply eval_complete in HMe1.
      eapply eval_complete in HMe2.
      assert (HCases: n <= n' \/ n' < n) by 
      (apply Nat.le_gt_cases).
      rewrite Nat.le_lteq in HCases. 
      destruct HCases as [[Hnltn' | Heq] | Hn'ltn]. 
      (* n < n' *)
      + assert (Hp: eval n' e s = Ok v). 
        {eapply eval_evalop_fuel_monotonic; 
          eauto. }
        rewrite Hp in HMe2; inversion_subst HMe2; eauto.
      (* n = n' *)
      + subst; rewrite HMe2 in HMe1; 
        inversion_subst HMe1; eauto.
      (* n' > n *)
      + assert (Hp: eval n e s = Ok v'). 
        {eapply eval_evalop_fuel_monotonic; 
          eauto. }
        rewrite Hp in HMe1; inversion_subst HMe1; eauto.   
         
    Qed.


End EVALUATION.