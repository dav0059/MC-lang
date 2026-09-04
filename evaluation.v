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
    Local Notation " 'v_env' " := (v_env I P). 
    Local Notation " 'WFEV' " := (@WFEV I P).
    Local Notation " 'interp_op' " := (interp_op P).
    Local Notation " 'BaseVl' " := (BaseVl P).
    Local Notation " 'id_eqb' " := (id_eqb I). 
    Local Notation " 'bind' s i v " := (bind s i v id_eqb) (at level 90).
    
    Fixpoint getBaseVl (l: list Val) : list BaseVl :=
      match l with 
      |(VLit x)::t => x::getBaseVl t 
      |_           => []
      end. 


    
    Inductive EValOp : list LExpr -> v_env -> list Val -> Prop := 
     |EValOp_nil   : forall s, 
                     WFEV s ->
                     EValOp [] s []
     |EValOp_cons : forall s tail tail' mssg head x,
                      WFEV s -> 
                      EValOp tail s tail' -> 
                      tail' <> [VError mssg] -> 
                      EVal head s (VLit x) -> 
                      EValOp (head::tail) s (VLit x::tail') 
     |EValOp_err1  : forall s tail tail' mssg' head mssg, 
                      WFEV s ->   
                      EValOp tail s tail' -> 
                      tail' <> [VError mssg'] -> 
                      EVal head s (VError mssg) -> 
                      EValOp (head::tail) s [VError mssg] 
     |EValOp_err2  : forall s head s v tail mssg,
                      WFEV s ->  
                      EValOp tail s [VError mssg] ->
                      EValOp (head::tail) s [VError mssg]        

    with EVal : LExpr -> v_env -> Val -> Prop := 
    |EV_Var      : forall i s v, 
                     WFEV s -> 
                     lookup s i = Some v -> 
                     EVal (LVar i) s v 
    |EV_Lit      : forall x s , 
                     WFEV s -> 
                     EVal (LLit x) s (VLit x)  
    |EV_LOp      : forall s le lv mssg hv lbv op v,       
                     WFEV s -> 
                     EValOp (rev le) s lv ->
                     lv <> [VError mssg] -> 
                     getBaseVl (rev lv) = lbv -> 
                     interp_op op lbv = Some v ->
                     EVal (LOp op le) s (VLit v) 
    |EV_LOpErr   : forall s le lv op mssg, 
                     WFEV s -> 
                     EValOp (rev le) s [VError mssg] ->
                     EVal (LOp op le) s (VError mssg)
    |EV_LLam     : forall s arg body, 
                     WFEV s -> 
                     EVal (LLam arg body) s (VCls arg body s)
    |EV_LApp     : forall s e1 arg body cls_env e2 v mssg 
                          cls_env' v', 
                     WFEV s -> 
                     EVal e1 s (VCls arg body cls_env) -> 
                     EVal e2 s v -> 
                     v <> (VError mssg) ->     
                     Match arg v -> 
                     MatchEnv arg v cls_env cls_env' -> 
                     EVal body cls_env' v' ->
                     EVal (LApp e1 e2) s v'  
    |EV_LAppRec  : forall s e1 name arg body cls_env e2 v mssg 
                          cls_env' cls_env_rec v', 
                     WFEV s ->  
                     EVal e1 s (VRecCls name arg body cls_env) ->
                     EVal e2 s v -> 
                     v <> VError mssg ->
                     Match arg v -> 
                     MatchEnv arg v cls_env cls_env' -> 
                     cls_env_rec = 
                       bind cls_env' name 
                        (VRecCls name arg body cls_env) ->
                     EVal body cls_env_rec v' -> 
                     EVal (LApp e1 e2) s v'
    |EV_LAppErr1  : forall s e1 e2 mssg, 
                     WFEV s -> 
                     EVal e1 s (VError mssg) -> 
                     EVal (LApp e1 e2) s (VError mssg) 
    |EV_LAppErr2  : forall s e1 v e2 mssg, 
                     WFEV s -> 
                     EVal e1 s v -> 
                     Typeof v KTFunction ->  
                     EVal e2 s (VError mssg) -> 
                     EVal (LApp e1 e2) s (VError mssg) 
    |EV_LUnit     : forall s, 
                     WFEV s -> 
                     EVal LUnit s VUnit 
    |EV_LNil      : forall s, 
                     WFEV s -> 
                     EVal LNil s VNil
    |EV_LPair     : forall s e1 e2 v1 t1 v2 t2,
                     WFEV s -> 
                     EVal e1 s v1 -> 
                     v1 <> VError mssg -> 
                     Typeof v1 t1 ->
                     EVal e2 s v2 -> 
                     v2 <> VError mssg ->
                     Typeof v2 t2 ->
                     EVal (LPair e1 e2) s 
                      (VPair (v1, t1) (v2, t2))
    |EV_LPairErr1 : forall e1 s mssg e2, 
                     WFEV s -> 
                     EVal e1 s (VError mssg) ->
                     EVal (LPair e1 e2) s (VError m)
    |EV_LPairErr2 : forall s e1 v1 mssg' e2 mssg, 
                     WFEV s -> 
                     EVal e1 s v1 ->
                     v1 <> VError mssg' ->
                     EVal e2 s (VError mssg) ->
                     EVal (LPair e1 e2) s (VError mssg)
    |EV_LCons1      : forall s e1 v1 t1 e2,  
                       WFEV s -> 
                       EVal e1 s v1 -> 
                       Typeof v1 t1 -> 
                       t1 <> KTError -> 
                       EVal e2 s VNil -> 
                       EVal (LCons e1 e2) s (VCons v1 VNil t1)
    |EV_LCons2      : forall s e1 v1 t1 e2 v2 t, 
                       WFEV s -> 
                       EVal e1 s v1 ->
                       Typeof v1 t1 ->
                       EVal e2 s v2 ->
                       Typeof v2 (KTList t) -> 
                       Consistent t1 t ->
                       nested_empty t = true ->  
                       EVal (LCons e1 e2) s (VCons v1 v2 t1)
    |EV_LCons3      : forall s e1 v1 t1 e2 v2 t, 
                       WFEV s -> 
                       EVal e1 s v1 -> 
                       Typeof v1 t1 -> 
                       t1 <> KTError -> 
                       EVal e2 s v2 -> 
                       Typeof v2 (KTList t) -> 
                       Consistent t1 t -> 
                       nested_empty t = false -> 
                       EVal (LCons e1 e2) s (VCons v1 v2 t)
    |EV_LConsErr1   : forall s e1 mssg e2, 
                       WFEV s -> 
                       EVal e1 s (VError m) ->
                       EVal (LCons e1 e2) s (VError m)
    |EV_LConsErr2   : forall e1 s v1 mssg' mssg , 
                       WFEV s -> 
                       EVal e1 s v1 -> 
                       v1 <> (Error mssg') -> 
                       EVal e2 s (VError mssg) -> 
                       EVal (LCons e1 e2) s (VError mssg)
    |EV_LVariant    : forall s e v t' t c i, 
                       WFEV s -> 
                       EVal e s v -> 
                       Typeof v t' -> 
                       t' <> KTError -> 
                       Consistent t t' -> 
                       EVal (LVariant c (i, t) e) s 
                             (VVariant c (i, t) v)
    |EV_LVariantErr : forall e s mssg c inf, 
                       WFEV s -> 
                       EVal e s (VError mssg) -> 
                       EVal (LVariant c inf e) s (VError mssg)
    |EV_LFix        : forall s e arg body cls_env name,
                       WFEV s -> 
                       EVal e s (VCls arg body cls_env) ->  
                       EVal (LFix name e) s 
                            (VRecCls name arg body cls_env)
    |EV_LFixErr     : forall e s mssg name, 
                       WFEV s -> 
                       EVal e s (VError mssg) -> 
                       EVal (LFix name e) s (VError mssg)
    |EV_LMatch      : forall s e v mssg p' e' s' v' l, 
                       WFEV s -> 
                       EVal e s v -> 
                       v <> (VError mssg) -> 
                       (fun '(p, _) => has_match p v) l = Some (p', e') ->
                       match_env p' v s = Some s' -> 
                       EVal e' s' v' -> 
                       EVal (LMatch e l) s v' 
    |EV_LMatchErr   : forall e s m l, 
                       WFEV s -> 
                       EVal e s (VError m) -> 
                       EVal (LMatch e l) s (VError m) 
    |EV_LError      : forall s m, 
                       WFEV s -> 
                       EVal (LError m) s (VError m).


    (* we need a powerful induction principle for mutually recursive types *)
    Scheme EVal_mut := Induction for EVal Sort Prop
    with EValOp_mut := Induction for EValOp Sort Prop.

    
    (* the possible VError value gotten from the operands evaluation of a 
       primitive operation is ever at the head position of the result list.*)
    Theorem EValOp_VError_Hd: forall l s l' v, 
      EValOp l s l' ->
      typeof v = Some KTError ->
      In v l' -> 
      hd_error l' = Some v.
    Proof. 
      intros * HEOp Htof HIn .
      generalize dependent l'. 
      induction l; intros. 
      + inversion HEOp; subst. contradiction.
      + inversion HEOp; subst; eauto. 
        destruct v; try destruct el_type; try discriminate. 
        destruct H7 as [Htbase | Hterr];
        destruct HIn; subst; eauto; 
        assert (contra: hd_error t' = Some (VError m)) by  
        (apply IHl; eauto); try rewrite contra in H2;  
        inversion H2; subst; contradiction. 
    Qed.

    (* spec uses getBaseVl in a safe way, i.e. as a map function 
       extracting BaseVl from the corresponding VLit.*)
    Theorem getBaseVl_safe: forall l s l' v, 
     EValOp l s l' -> 
     hd_error l' = Some v ->
     typeof v <> Some (KTError) ->
     Forall (fun x => exists t, typeof x = Some (KTBase t)) l' /\
     length (getBaseVl l') = length l'.
    Proof.
      intros * HEV Hhd Htof. 
      split. 
      + generalize dependent l. 
        generalize dependent v.
        induction l'; intros; try discriminate.   
        inversion HEV; subst; apply Forall_cons; eauto; 
        simpl in *; inversion Hhd; subst. 
        - destruct H7 as [Hl | *]. destruct Hl as [t' *].
          exists t' ; eauto. 
          contradiction.
        - inversion H1; subst; contradiction. 
        - inversion H1; subst; contradiction.
      + generalize dependent l.  
        generalize dependent v. 
        induction l'; intros; eauto. 
        inversion HEV; subst; simpl in *; inversion Hhd; subst; 
        try (inversion H0; subst; contradiction). 
        destruct H7; destruct H. 
        - destruct v; simpl; eauto;
          simpl in *; try destruct el_type; discriminate.
        - contradiction.
        - inversion H1; subst; contradiction.
    Qed.


    (* The following lemmas establish that each rule has a short-circuited
       propagation behaviour determined by the left-to-right 
       evaluation order for VError values. *)
    Lemma lop_propagates_leftmost_verror: forall l s l' m op, 
      EValOp (rev l) s l' -> 
      hd_error l' = Some (VError m) -> 
      EVal (LOp op l) s (VError m).
    Proof. 
      intros * HEvOp Hhd. 
      destruct l. 
      + inversion HEvOp; subst; simpl in Hhd; discriminate.
      + apply EV_LOpErr with (lv := l'); eauto. 
        inversion HEvOp; eauto; inversion H3; eauto.
    Qed. 
      

    Lemma lapp_propagates_left_verror: forall e1 s m e2, 
      EVal e1 s (VError m) -> 
      EVal (LApp e1 e2) s (VError m).
    Proof. 
      intros * HEv. 
      apply EV_LAppErr1; eauto.
      inversion HEv; eauto.
    Qed. 

    Lemma lapp_propagates_right_verror: forall e1 s name p e s_cls e2 m, 
      EVal e1 s (VCls name p e s_cls) -> 
      EVal e2 s (VError m) -> 
      EVal (LApp e1 e2) s (VError m).
    Proof. 
      intros * HEv1 HEv2. 
      apply EV_LAppErr2 with (name := name) (p := p) (e := e)
      (s_cls := s_cls); eauto.
      inversion HEv1; eauto.
    Qed. 


    Lemma lpair_propagates_left_verror: forall e1 s m e2, 
      EVal e1 s (VError m) -> 
      EVal (LPair e1 e2) s (VError m). 
    Proof. 
      intros * HEv. 
      apply EV_LPairErr1; eauto. 
      inversion HEv; eauto. 
    Qed. 


    Lemma lpair_propagates_right_verror: forall e1 s v e2 m, 
      EVal e1 s v -> 
      typeof v <> Some KTError -> 
      EVal e2 s (VError m) ->
      EVal (LPair e1 e2) s (VError m). 
    Proof. 
      intros * HEv1 Htof HEv2. 
      apply EV_LPairErr2 with (v1 := v); eauto. 
      inversion HEv2; eauto. 
    Qed. 
    
    
    Lemma lcons_propagates_left_verror: forall e1 s m e2, 
      EVal e1 s (VError m) -> 
      EVal (LCons e1 e2) s (VError m).
    Proof. 
      intros * HEv. 
      apply EV_LConsErr1; eauto. 
      inversion HEv; eauto. 
    Qed. 


    Lemma lcons_propagates_right_verror: forall e1 s v e2 m,
      EVal e1 s v -> 
      typeof v <> Some KTError -> 
      EVal e2 s (VError m) -> 
      EVal (LCons e1 e2) s (VError m).
    Proof. 
      intros * HEv1 Htof HEv2. 
      apply EV_LConsErr2 with (v1 := v); eauto.
      inversion HEv1; eauto.
    Qed. 
    
    
    Lemma lvariant_propagates_verror: forall e s m c inf, 
      EVal e s (VError m) -> 
      EVal (LVariant c inf e) s (VError m).
    Proof. 
      intros * HEv. 
      apply EV_LVariantErr; eauto. 
      inversion HEv; eauto. 
    Qed. 
    
    
    Lemma lfix_propagates_verror: forall e s m i, 
      EVal e s (VError m) -> 
      EVal (LFix i e) s (VError m). 
    Proof. 
      intros * HEnv. 
      apply EV_LFixErr; eauto. 
      inversion HEnv; eauto. 
    Qed. 


    Lemma lmatch_propagates_verror: forall e s m l, 
      EVal e s (VError m) -> 
      EVal (LMatch e l) s (VError m). 
    Proof. 
      intros * HEv. 
      apply EV_LMatchErr; eauto. 
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
      try apply WFV_VLit; eauto. 
      + induction w; subst; unfold lookup, empty_env in e. 
        discriminate. unfold bind in e.
        destruct (id_eqb i i0) eqn: eqid; 
        inversion e; subst; eauto. 
      + destruct lv; inversion e0; subst.
        apply IHHEv in e. inversion e; eauto.
      + apply WFV_Cls. eauto.
      + apply WFV_VUnit.  
      + apply WFV_VNil.
      + apply WFV_VPair; eauto; 
        apply typeof_correct; eauto.
      + apply WFV_VCons with (t := t1) (t1 := t1) (t2 := KTList KTEmpty); 
        try apply typeof_correct; eauto.
        * assert (H: is_FOT t1 = true) by 
          (apply typeof_is_FOT with (v := v1), typeof_correct; eauto).
          apply consistent_refl; eauto.
        * apply c_TListNil1, typeof_is_FOT with (v := v1),
          typeof_correct; eauto.
      + apply WFV_VCons with (t := t1) (t1 := t1) (t2 := KTList t2);
        apply typeof_correct in e; apply typeof_correct in e0; eauto.
        * apply consistent_refl, typeof_is_FOT with (v := v1); eauto.
        * apply c_TList, consistent_sym, is_consistent_correct; eauto.
      + apply WFV_VCons with (t := t2) (t1 := t1) (t2 := KTList t2);
        apply typeof_correct in e; apply typeof_correct in e0; eauto.
        * apply is_consistent_correct; eauto.
        * apply c_TList, consistent_refl. 
          apply is_consistent_correct in e4.
          apply consistent_is_FOT in e4; destruct e4; eauto.
      + apply WFV_VVariant with (t := t'); eauto.
        * apply typeof_correct; eauto.
        * apply consistent_sym, is_consistent_correct; simpl; eauto.
      + apply WFV_Cls. subst. apply WFEV_some; 
        inversion IHHEv; subst; try apply WFV_Cls; eauto.
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
      generalize dependent HEv2. 
      generalize dependent Hwfev.
      generalize dependent v'.
      induction HEv1 using EVal_mut with 
        (P0 := fun l s l' _ => forall l'', 
          WFEV s -> EValOp l s l' -> EValOp l s l'' -> l' = l'' );
       intros.
      + inversion HEv2; subst; rewrite H1 in e; 
        inversion e; eauto.
      + inversion HEv2; subst; eauto. 
      + inversion HEv2; subst; try rewrite H5 in e0;
        inversion e0; eauto;
        inversion H2; subst; simpl in *; discriminate.
      + inversion e; inversion HEv2; subst; try discriminate.
        * assert (Hind: v0::t' = lv0) by (apply IHHEv1; eauto).
          subst. rewrite H16 in e2; inversion e2; eauto.
        * assert (Hind: v0::t' = lv0) by (apply IHHEv1; eauto). 
          subst. simpl in *; inversion H13; subst; 
          destruct H4 as [ [x Hcontra] | Herr]; 
          try (rewrite H14 in Hcontra; discriminate);
          inversion e0; subst; contradiction.
        * assert (Hind: lv = lv0) by (apply IHHEv1; eauto).
          subst; rewrite H15 in e2; inversion e2; eauto.
        * rewrite H2 in e0; inversion e0; subst. contradiction.
      + inversion e; inversion HEv2; subst; try discriminate.
        * simpl in *; inversion e0; subst. 
          assert (VError m::t' = lv0) by (apply IHHEv1; eauto).
          subst. simpl in *; inversion H11; subst; contradiction.
        * simpl in *; inversion e0; subst. 
          assert (VError m::t' = lv0) by (apply IHHEv1; eauto).
          subst. simpl in *; inversion H13; eauto.
        * assert (lv = lv0) by (apply IHHEv1; eauto); subst.
          rewrite H10 in e0; inversion e0; subst. contradiction.
        * assert (lv = lv0) by (apply IHHEv1; eauto); subst.   
          rewrite H12 in e0; inversion e0; eauto. 
      + inversion HEv2; subst. eauto. 
      + inversion HEv2; subst. 
        * assert (Hp1: VCls None p e s_cls = VCls None p0 e5 s_cls0) 
          by (apply IHHEv1_1; eauto).
          assert (Hp2: v = v0) by (apply IHHEv1_2; eauto). 
          inversion Hp1; subst. rewrite H6 in e3. inversion e3; subst.  
          apply IHHEv1_3; eauto.
          apply EVal_wfv in HEv1_1, HEv1_2. 
          inversion HEv1_1; subst; 
          apply match_env_preservers_wfev with (s := s_cls0)
          (p := p0) (v := v0);
          apply match_env_correct in H6; eauto. 
        * assert (Hp1: VCls None p e s_cls = VCls (Some i) p0 e5 s_rcls) 
          by (apply IHHEv1_1; eauto). 
          inversion Hp1. 
        * assert (Hp1: VCls None p e s_cls = VError m) 
          by (apply IHHEv1_1; eauto). 
          inversion Hp1.
        * assert (Hp2: v = VError m) by (apply IHHEv1_2; eauto). 
          rewrite Hp2 in n; contradiction.
      + inversion HEv2; subst. 
        * assert (Hp1: VCls (Some i) p e s_rcls = VCls None p0 e6 s_cls) 
          by (apply IHHEv1_1; eauto). 
          inversion Hp1.
        * assert (Hp1: VCls (Some i) p e s_rcls = VCls (Some i0) p0 e6 s_rcls0) 
          by (apply IHHEv1_1; eauto).
          assert (Hp2: v = v0) by (apply IHHEv1_2; eauto). 
          inversion Hp1; subst. rewrite H6 in e3. inversion e3; subst.  
          apply IHHEv1_3; eauto.
          apply EVal_wfv in H2, H3. apply match_env_correct, 
          match_env_preservers_wfev in H6;  
          inversion H2; subst; try apply WFEV_some; eauto.
        * assert (Hp1: VCls (Some i) p e s_rcls = VError m) 
          by (apply IHHEv1_1; eauto). 
          inversion Hp1.
        * assert (Hp2: v = VError m) by (apply IHHEv1_2; eauto). 
          rewrite Hp2 in n; contradiction.
      + inversion HEv2; subst; eauto.
        * apply IHHEv1 with (v' := VCls None p e s_cls) in H2. 
          inversion H2. eauto.
        * apply IHHEv1 with (v' := VCls (Some i) p e s_rcls) in H2. 
          inversion H2. eauto.
        * apply IHHEv1 with (v' := VCls name p e s_cls) in H2. 
          inversion H2. eauto.
      + inversion HEv2; subst; eauto; 
        try (apply IHHEv1_2 with (v' := v) in H3; subst; eauto; 
          contradiction).
        apply IHHEv1_1 in H4; eauto; inversion H4.
      + inversion HEv2; eauto.
      + inversion HEv2; eauto.
      + inversion HEv2; subst. 
        * assert (Hp1: v1 = v0) by (apply IHHEv1_1; eauto).
          assert (Hp2: v2 = v3) by (apply IHHEv1_2; eauto); 
          subst; rewrite H3 in e; rewrite H6 in e0; inversion e; 
          inversion e0; subst; eauto.
        * assert (Hp1: v1 = VError m) by (apply IHHEv1_1 ; eauto); 
          subst. simpl in e. inversion e; subst. contradiction.
        * assert (Hp1: v2 = VError m) by (apply IHHEv1_2 ; eauto); 
          subst. simpl in e0. inversion e0; subst. contradiction.
      + inversion HEv2; subst. 
        * assert (Hp1: VError m = v1) by (apply IHHEv1; eauto); 
          subst. simpl in H3. inversion H3; subst. contradiction.
        * apply IHHEv1; eauto.
        * assert (Hp1: VError m = v1) by (apply IHHEv1; eauto). 
          subst. simpl in H3. contradiction.
      + inversion HEv2; subst.  
        * assert (Hp1: VError m = v2) by (apply IHHEv1_2; eauto); 
          subst. simpl in H6. inversion H6; subst. contradiction.
        * assert (Hp1: v1 = VError m0) by 
          (apply IHHEv1_1 in H4; eauto); 
          subst. simpl in *. contradiction.
        * apply IHHEv1_2; eauto.
      + inversion HEv2; subst. 
        * apply IHHEv1_1 in H2; eauto; subst. rewrite H3 in e;  
          inversion e; eauto.
        * apply IHHEv1_1 in H2; eauto; subst. 
          apply IHHEv1_2 in H4; eauto; subst. 
          rewrite H3 in e; inversion e; eauto.
        * apply IHHEv1_1 in H2; eauto; subst. 
          apply IHHEv1_2 in H5; eauto; subst. 
          rewrite H3 in e; inversion e; inversion H6; subst.
          apply is_consistent_correct, consistent_eq_tempty in H10; 
          subst; eauto. 
        * apply IHHEv1_1 in H4; eauto; subst.
          simpl in *. inversion e; subst; contradiction.
        * apply IHHEv1_2 in H6; eauto; subst. discriminate.
      + inversion HEv2; subst.
        * apply IHHEv1_1 in H2; eauto; subst. 
          apply IHHEv1_2 in H7; eauto; subst. 
          rewrite H3 in e; inversion e; eauto.
        * apply IHHEv1_1 in H2; eauto; subst. 
          apply IHHEv1_2 in H4; eauto; subst. 
          rewrite H3 in e; inversion e; subst; eauto.
        * apply IHHEv1_1 in H2; eauto; subst. 
          apply IHHEv1_2 in H5; eauto; subst. 
          rewrite H3 in e; inversion e; subst;
          rewrite H6 in e0; inversion e0; subst.
          rewrite H7 in e3; discriminate.
        * apply IHHEv1_1 in H4; eauto; subst.
          simpl in *; inversion e; subst. 
          apply is_consistent_correct in e4.
          inversion e4; subst. discriminate.
        * apply IHHEv1_2 in H6; eauto; subst.
          simpl in *; inversion e0.
      + inversion HEv2; subst. 
        * apply IHHEv1_1 in H2; eauto; subst. 
          apply IHHEv1_2 in H7; eauto; subst.
          rewrite H3 in e; inversion e; inversion e0; subst.
          apply is_consistent_correct, consistent_eq_tempty in 
          e4; subst; eauto.
        * apply IHHEv1_1 in H2; eauto; subst. 
          apply IHHEv1_2 in H4; eauto; subst. 
          rewrite H3 in e; inversion e; subst;
          rewrite H5 in e0; inversion e0; subst.
          rewrite H6 in e3; discriminate.
        * apply IHHEv1_1 in H2; eauto; subst. 
          apply IHHEv1_2 in H5; eauto; subst. 
          rewrite H6 in e0; inversion e0; subst. eauto.
        * apply IHHEv1_1 in H4; eauto; subst.
          simpl in *; inversion e; subst. 
          apply is_consistent_correct in e4.
          inversion e4; subst. contradiction. 
        * apply IHHEv1_2 in H6; eauto; subst.
          simpl in *; inversion e0.  
      + inversion HEv2; subst; eauto;
        try(assert (Hp1: VError m = v1) by 
          (apply IHHEv1 in HEv1; eauto);
          subst; simpl in H3; try inversion H3; subst); 
        try contradiction;
        try (apply is_consistent_correct in H9;
          inversion H9; try discriminate; subst; simpl in *; 
          discriminate).
      + inversion HEv2; subst; eauto; 
        try (assert (Hp1: VError m = v2) by (apply IHHEv1_2; eauto); 
          subst; simpl in *; discriminate) .
        apply IHHEv1_2 in H7; eauto; discriminate.
        apply IHHEv1_1 in H4; eauto; subst; simpl; contradiction.
      + inversion HEv2; subst. 
        * apply IHHEv1 in H4; subst; eauto.
        * apply IHHEv1 in H5; subst; simpl in e0; inversion e0; 
          subst; eauto; contradiction. 
      + inversion HEv2; subst; eauto. 
        apply IHHEv1 in H3; subst; simpl in H4; inversion H4; 
        subst; eauto; contradiction. 
      + inversion HEv2; subst. 
        * apply IHHEv1 in H2; inversion H2; subst; eauto.
        * apply IHHEv1 in H4; eauto; discriminate.
      + inversion HEv2; subst; eauto.
        apply IHHEv1 in H2; eauto; discriminate.
      + inversion HEv2; subst. 
        * apply IHHEv1_1 in H2; subst; eauto.
          rewrite H4 in e0; inversion e0; subst. 
          rewrite H5 in e1; inversion e1; subst.
          apply IHHEv1_2 in H8; eauto.
          apply match_env_correct, match_env_preservers_wfev in H5; 
          eauto; apply EVal_wfv in HEv1_1; eauto.
        * apply IHHEv1_1 in H4; subst; simpl in *; eauto; 
          contradiction.
      + inversion HEv2; subst; eauto.
        apply IHHEv1 in H2; subst; simpl in *; eauto; 
        contradiction.
      + inversion HEv2; subst; eauto.
      + inversion H1; eauto.
      + inversion H1; subst; eauto. 
        * apply IHHEv0 in H7; subst; 
          apply IHHEv1 in H4; subst; eauto.
        * apply IHHEv1 in H5; eauto; subst. 
          rewrite H6 in e0; inversion e0; subst.
          contradiction.
      + inversion H1; subst. 
        * apply IHHEv1 in H4; eauto; subst. 
          rewrite H5 in e0; inversion e0; subst.
          contradiction.
        * eauto.
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