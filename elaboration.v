Require Import result_type.
Require Import ids.
Require Import primitives. 
Require Import kernel_syntax.
Require Import type_env.
Require Import env. 
Require Import type_theory.
Require Import pattern_theory. 
Require Import Strings.String. 
Require Import Lists.List. 
Import ListNotations.


Set Implicit Arguments. 
Set Contextual Implicit. 

Section ELABORATION.

    Context (I: IDS).
    Context (P: PRIM_DATA). 

    Local Notation " 'Ide' " := (@Ide I).
    Local Notation " 'Constr' " := (@Constr I).
    Local Notation " 'Message' " := (@Message I).
    Local Notation " 'KTp' " := (@KTp I P).
    Local Notation " 'KPat' " := (@KPat I P).    
    Local Notation " 'KExpr' " := (@KExpr I P). 
    Local Notation " 'BaseVl' " := (@BaseVl P).
    Local Notation " 'OP' " := (@OP P).
    Local Notation " 'tenv' " := (@tenv I P). 
    Local Notation " 'register' " := (@register I ).
    Local Notation " 'constr_env' " := (@constr_env I P).


    Ltac inversion_subst H := inversion H; subst; clear H.
    Ltac solve_base := try constructor; eauto.
    Ltac discard_case := 
      try contradiction; 
      try (simpl in *; discriminate).

    (* the AST resulting from the static elaboration is a labelled AST (LExpr). 
      The node `EVariant c e` carries the pair (i: Id, t: Tp), where `i` is 
      the name of the last defined variant type having `c` among its 
      constructors with `t` as constructor argument. This allows to do 
      efficient nominal typechecking at runtime. 
      Moreover, in the new AST every node of the form `DefType` has been 
      erased because of the type declarations processing.  *)
    Inductive LExpr: Type := 
    |LVar (i: Ide) 
    |LLit (x: BaseVl) 
    |LOp (op: OP) (args: list LExpr)   
    |LLam (p: KPat) (e: LExpr) 
    |LApp (e1: LExpr) (e2: LExpr)
    |LUnit 
    |LNil  
    |LPair (e1 : LExpr) (e2: LExpr) 
    |LCons (e1: LExpr) (e2: LExpr) 
    |LVariant (c: Constr) (inf: Ide * KTp) (e: LExpr) 
    |LFix (name: Ide) (cls: LExpr)  
    |LMatch (e: LExpr) (cases: list (KPat * LExpr)) 
    |LError (m: Message) . 


    (* block of type declarations. *)
    Definition tdblock :=  list (Ide * KTp).
    (* state of block elaboration consists of a type env, 
      a register, both to be extended during the elaboration, 
      and a block of type declarations. *)
    Definition tbe_state : Type := tenv * register * tdblock. 
    (* the successful result of block elaboration is 
       the type env and the register extended. 
       The failure result is an error message. *)
    Definition tdblock_ext_result := result (tenv * register) string .


    (* given a register `R` and a tdblock `B` 
       extends temporarily `R` with names in `B`.  *)
    Definition early_binding (R: register) (B: tdblock) := 
      fold_right (fun '(i, _) e => bind e i tt (id_eqb I)) R B.

    (* given a type_env `r` extends it with types in `B`, 
       assuming they are already be validated. *)
    Definition type_env_ext (r: tenv) (B: tdblock) :=  
      fold_right (fun '(i, t) e => tbind e i t) r B.
    
    
    (* Note that the extension of the type env and register 
       is right to left! 
       The order in which names are installed is irrelevant because 
       within a block we require uniqueness of declared names 
       and constructors. So, there's no problem of shadowing 
       (WITHIN A BLOCK, not in general). *)


    (* given a tdblock of validated types collects all declared 
       constructors in a list.  *)    
    Definition dblock_constr (B: tdblock) : option (list Constr) := 
      fold_right (fun '(_, t) acc => 
                   match t, acc with 
                   |KTVariant l', Some l => Some (fst (split l') ++ l) 
                   |_, _                 => None end) (Some []) B.  
    



    Lemma dblock_constr_correct : forall i l B c l', 
      In (i, KTVariant l) B -> 
      In c (fst (split l)) -> 
      Some l' = (dblock_constr B) -> 
      In c l'. 
    Proof. 
      intros * HInB HInl Hl'.
      generalize dependent l'.
      induction B as [| (i', t) B']; intros; discard_case.
      simpl in HInB. destruct t; discard_case.
      (* t := KTVariant tags *)
      destruct (dblock_constr B') as [lB |] eqn: HDB'.
      (* HDB' := Some lB *)
      * destruct HInB as [HEq | HInB] .
        (* (i, KTVariant l) = (i', t) *)
        ** inversion_subst HEq. inversion_subst Hl'.
           rewrite HDB' in *. inversion_subst H0.  
           rewrite in_app_iff. left; eauto.
        (* In (i, KTVariant l) B' *)
        ** pose proof HInB as HInB2. 
           apply IHB' with (l' := lB) in HInB; eauto. 
           simpl in Hl'. rewrite HDB' in Hl'. 
           inversion_subst Hl'. rewrite in_app_iff; 
           right; eauto.
      (* HDB' := None *)
      * simpl in Hl'. rewrite HDB' in Hl'. discriminate.   
    Qed.
 

    (* TBlockElab formalizes the elaboration 
       of a type declaration block . *)
    Inductive TBlockElab: tbe_state -> tbe_state -> Prop := 
    |TBElab : forall r R B l, 
                WFET r R -> 
                nodupb (id_eqb I) (fst (split B)) = true -> 
                Forall (DT (early_binding R B)) (snd (split B)) ->  
                dblock_constr B = Some l -> 
                nodupb (constr_eqb I) l = true ->  
                TBlockElab 
                (r, R, B) 
                (type_env_ext r B, early_binding R B, B) . 


    Lemma extension_preserves_eq_dom : forall r R B, 
     (forall i , tdom r i <-> dom R i) -> 
     (forall i, tdom (type_env_ext r B) i <-> dom (early_binding R B) i). 
    Proof. 
      intros * Hdom; split.
      (* -> *)
      + intros Htdom; induction B; intros. 
        - simpl in *; apply Hdom; eauto.
        - simpl in Htdom. destruct a as (i', t).
          unfold tdom, tlookup, tbind in Htdom.
          destruct Htdom as [x Htdom]. simpl in Htdom. 
          destruct (id_eqb I i i') eqn: eqid. 
          (* id_eqb I i i' = true *)
          * unfold dom, lookup. exists tt. simpl.
            unfold bind. rewrite eqid; eauto.
          (* id_eqb I i i' = false *)
          * unfold tdom, tlookup, tbind in IHB. 
            assert (Hp: exists y, 
             assoc_opt (type_env_ext r B) i (id_eqb I) = Some y) by 
            (exists x; eauto).  
            apply IHB in Hp. simpl. unfold dom, lookup, bind in *.
            destruct Hp. exists x0. rewrite eqid. eauto.
      (* <- *)
      + intros HDom; induction B; intros. 
        - simpl in *; apply Hdom; eauto.
        - simpl in HDom. destruct a as (i', t);
          unfold dom, lookup, bind in HDom;
          destruct HDom as [x HDom];  
          destruct (id_eqb I i i') eqn: eqid.
           (*id_eqb I i i'  = true *)
          * unfold tdom, tlookup. exists t. simpl.
            rewrite eqid; eauto.
          (* id_eqb I i i' = false *)
          * unfold lookup in HDom. 
            unfold dom, lookup, bind in IHB. 
            assert (Hp: exists y, 
             early_binding R B i = Some y) by 
            (exists x; eauto).  
            apply IHB in Hp. simpl. 
            unfold tdom, tlookup, tbind in *.
            destruct Hp. exists x0. simpl. 
            rewrite eqid. eauto.
    Qed.            
      

    Lemma early_bind_preserves_AF : 
      forall (R: register) (B: tdblock) (t: KTp),
         AF R t -> AF (early_binding R B) t.
    Proof. 
      intros * HAF.
      induction HAF using AF_ind'; solve_base.  
      generalize dependent R. 
      induction B; intros; solve_base.
      simpl. destruct a as (i', _). 
      unfold includes, lookup, bind.
      destruct (id_eqb I i i') eqn: eqid; eauto.
    Qed. 
    
    
    Corollary early_bind_preserves_DT : 
      forall (R: register) (B: tdblock) (t: KTp), 
        DT R t -> DT (early_binding R B) t.
    Proof. 
      intros * HDT; inversion_subst HDT. 
      constructor. eapply early_bind_preserves_AF.
      eauto.
    Qed.      

   
    Lemma timm_type_env_ext_cases : 
      forall (r: tenv) (B: tdblock) t, 
        timm (type_env_ext r B) t -> 
        timm r t \/ In t (snd (split B)).
    Proof. 
      intros * Htext. induction B; intros. 
      + simpl in *. left. eauto. 
      + simpl in *. destruct a as (i, t').
        unfold timm, tlookup, tbind in *.
        destruct Htext as [i' Htext]; simpl in *.
        destruct (id_eqb I i' i) eqn: eqid.
        (* id_eqb I i' i = true *)
        * right. destruct (split B). simpl.
          left. inversion_subst Htext; eauto.
        (* id_eqb I i' i = false *)
        * assert (Hp: exists i,  
           assoc_opt (type_env_ext r B) i (id_eqb I) = Some t) by 
           (exists i'; eauto). apply IHB in Hp. 
          destruct Hp as [[i'' Hp] | HIn ].
          - left; eauto. 
          - destruct (split B). simpl; right; eauto.
    Qed.        



    (* TBlockElab extends (r, R) preserving well-formedness *)
    Theorem TBlockElab_correct : forall r R r' R' B, 
     TBlockElab (r, R, B) (r', R', B) -> WFET r' R'.
    Proof. 
      intros * HBext. 
      inversion HBext as [r0 R0 B' l HWfet Hnodup1
                          HForall Hconstr Hnodup2]; 
      subst; clear HBext.
      inversion_subst HWfet.                    
      unfold WFET. split. 
      + intro. apply extension_preserves_eq_dom; eauto.  
      + intros * Himm. 
        apply timm_type_env_ext_cases in Himm.
        destruct Himm as [Htimm | HIn]. 
        * apply H0 in Htimm. 
          apply early_bind_preserves_DT; eauto.
        * rewrite Forall_forall in HForall.
          specialize HForall with t. eauto.
    Qed.     


    (* computational version of BlockExtends predicate *)
    Definition tblock_extends r R B : tdblock_ext_result := 
      if nodupb (id_eqb I) (fst (split B)) then 
        let R' := early_binding R B in 
        if forallb (fun p => is_DT R' (snd p)) B then 
          let r' := type_env_ext r B in 
          match dblock_constr B with 
          |Some l  => if nodupb (constr_eqb I) l then Ok (r', R') 
                      else Error ("duplicated constructor is declared in the same block"%string)
          |None    => Error ("implementation error: invalid type has been declared"%string)
          end 
        else Error ("declaration of invalid type"%string)
      else Error ("duplicated name is declared in the same block"%string). 
      
    
    Theorem Forall_split_conv : forall {X Y} P (l: list (X * Y)), 
     Forall P (snd (split l)) <-> Forall (fun p => P (snd p)) l.
    Proof. 
      split; intros; induction l; 
      try apply Forall_nil; simpl in *;
      destruct a; destruct (split l); simpl;  
      apply Forall_cons; inversion H; subst;  
      try discriminate; eauto. 
    Qed.        
    
    Theorem tbl_ext_correct: forall r r' R R' B,
      WFET r R ->  
      tblock_extends r R B = Ok (r', R') -> 
      TBlockExtends (r, R, B) (r', R', B).
    Proof. 
      intros * HWfet Hb_ext. 
      unfold tblock_extends in Hb_ext. 
      destruct (nodupb _) eqn: eqnodup. 
      + destruct (forallb _) eqn: eqforall. 
        * destruct (dblock_constr _) eqn: eqconstr. 
          - destruct (nodupb (constr_eqb I) l) eqn: eqnodupb; 
            inversion Hb_ext; subst. 
            apply TBext with l; eauto.
            apply Forall_split_conv.
            apply Forall_impl_forallb_DT; eauto.
            intros; symmetry; apply is_DT_eq_DT .        
          - discriminate.
        * discriminate. 
      + discriminate. 
    Qed.
    
    Theorem tbl_ext_complete: forall r r' R R' B,   
      TBlockExtends (r, R, B) (r', R', B) -> 
      tblock_extends r R B = Ok (r', R'). 
    Proof. 
      intros * HBext. 
      inversion HBext as [r0 R0 B' l HWfet Hnodup1
                          HForall Hconstr Hnodup2]; subst. 
      unfold tblock_extends. 
      rewrite Hnodup1.
      apply Forall_split_conv in HForall.
      rewrite Forall_impl_forallb_DT in HForall.
      rewrite HForall.
      rewrite <- Hconstr.
      rewrite Hnodup2.
      reflexivity.
      symmetry; apply is_DT_eq_DT. 
    Qed.
    

    Theorem tbl_ext_correct_Err: forall r R B mssg, 
      tblock_extends r R B = Error mssg ->
      (forall r' R', ~TBlockExtends (r, R, B) (r', R', B)).
    Proof. 
      intros * Hbe. unfold not. 
      intros * HBext. 
      inversion HBext as [r0 R0 B' l HWfet Hnodup1
                          HForall Hconstr Hnodup2]; subst. 
      unfold tblock_extends in Hbe.
      rewrite Hnodup1 in Hbe. 
      apply Forall_split_conv in HForall.
      rewrite Forall_impl_forallb_DT in HForall.
      rewrite HForall in Hbe. 
      rewrite <- Hconstr in Hbe.
      rewrite Hnodup2 in Hbe.
      discriminate.
      symmetry. apply is_DT_eq_DT.
    Qed.   


    Theorem tbl_ext_complete_Err: forall r R B, 
       WFET r R -> 
       (forall r' R', ~TBlockExtends (r, R, B) (r', R', B)) -> 
       (exists mssg, tblock_extends r R B = Error mssg).
    Proof. 
      intros * HWfet HBext. 
      unfold tblock_extends.   
      destruct (nodupb _) eqn: eqnodup1.
      + destruct (forallb _) eqn: eqforall. 
        * destruct (dblock_constr _) eqn: eqconstr. 
          - destruct (nodupb (constr_eqb I) l) eqn: eqnodupb. 
            -- exists ""%string. 
               assert (contra: 
                TBlockExtends (r, R, B) (type_env_ext r B, early_binding R B, B)). 
               {apply TBext with l; eauto. 
                apply Forall_split_conv; 
                apply Forall_impl_forallb_DT; eauto.
                symmetry. apply is_DT_eq_DT. } 
              unfold not in HBext; apply HBext in contra.
              contradiction. 
            -- exists "duplicated constructor is declared in the same block"%string.
               reflexivity.
          - exists "implementation error: invalid type has been declared"%string.
            reflexivity.
        * exists "declaration of invalid type"%string. 
          reflexivity. 
      + exists "duplicated name is declared in the same block"%string.
        reflexivity.
    Qed.                   
                
    


    Definition cdblock := list (Constr * KTp). 

    (* given a well-formed constr_env `d`, a name `i` of a declarable type 
       and its block of declared constructors `l`, it extends `d` binding 
       each constructor `c` declared in `l` carrying type `t` with `(i, t)`. *)
    Fixpoint cblock_extends (d: constr_env) (i: Ide) (l: cdblock) : constr_env :=
      match l with 
      |[]        => d 
      |(c, t)::l => bind (cblock_extends d i l) c (i, t) (constr_eqb I)  
      end. 
      
           
       
    Lemma bind_old_or_new : forall d c i j l t,
      lookup (cblock_extends d i l) c = Some (j, t) -> 
      lookup d c = Some (j, t) \/ (j = i /\ In (c, t) l).
    Proof. 
      intros * Hlkp.
      generalize dependent d. 
      induction l; intros. 
      + simpl in *. left. eauto.
      + simpl in Hlkp. destruct a.
        pose proof Hlkp as Hlkp'.  
        unfold lookup, bind in Hlkp.
        destruct (constr_eqb I c c0) eqn: eqc .
        - rewrite <- constr_eqb_eq in eqc; rewrite eqc in *.
          inversion Hlkp; subst.
          right. split; try (simpl; left); eauto.
        - apply IHl in Hlkp; eauto. 
          destruct Hlkp. 
          left; eauto. 
          right. split; destruct H; eauto.
          simpl. right; eauto.
    Qed.  


    Theorem cbl_ext_correct : forall d r R i l, 
      WFEC d r R ->
      In (i, KTVariant l) r -> 
      (forall c t, In (c, t) l -> last_type_def r c = Some (i, KTVariant l)) ->
      WFEC (cblock_extends d i l) r R. 
    Proof.
      intros * HWfec _.
      unfold WFEC; split; 
      inversion HWfec as [H0 H1]; eauto.
      intros * Hlkp. 
      apply bind_old_or_new in Hlkp.
      destruct Hlkp as [Hlkp | Heqin].
      + apply H1; eauto.
      + destruct Heqin as [Heq Hin]; subst. 
        pose proof Hin as Hin'. 
        apply H in Hin. exists l; eauto.
    Qed.
 
        
                
    (* given a well-formed constr_env `d` and a tblock `l` 
       it extends `d` binding every variant constructor in `l` to 
       `(i, t)`, where `i` is the name of the declared type and 
       `t` is the type carried by the current constructor. 
       If 'l' contains a non declarable type, it returns None. *)
    Fixpoint bind_constr_tblock (d: constr_env) (B: tdblock) := 
      match B with 
      |[]                    => Some d 
      |(i, KTVariant l)::B'  => bind_constr_tblock (cblock_extends d i l) B' 
      |_                     => None 
      end.
  
          
    Lemma bind_old_or_new_ex : forall d d' B c j t,
      Some d' = bind_constr_tblock d B -> 
      lookup d' c = Some (j, t) -> 
      lookup d c = Some (j, t) \/ 
      (exists i l, j = i /\ In (i, KTVariant l) B /\ In (c, t) l).
    Proof.
      intros.  
      generalize dependent d.
      induction B; intros. 
      + simpl in H; inversion H; subst; left; eauto.
      + pose proof H as H'. 
        simpl in H; destruct a; destruct k; try discriminate.
        apply IHB in H. destruct H. 
        * apply bind_old_or_new in H. 
          destruct H. 
          ** left; eauto.
          ** right. exists i. exists tags.
             destruct H; repeat split; simpl; eauto.
        * right. destruct H as [i0 [l [H1 [H2 H3]]]].
          exists i0. exists l. repeat split; eauto. 
          simpl. right . eauto.
    Qed.     
             

    
    Lemma exb_cblock : forall (cb : list (Constr * KTp)) c, 
      existsb (fun p => constr_eqb I (fst p) c) cb = true -> 
      exists t, In (c, t) cb.
    Proof.
      intros * Hexb. 
      induction cb. 
      + simpl in *. discriminate. 
      + simpl in Hexb. destruct (constr_eqb I (fst a) c) eqn: eqid. 
        - destruct a. 
          exists k. simpl. left. rewrite <- constr_eqb_eq in eqid; 
          simpl in *; subst; eauto. 
        - rewrite Bool.orb_false_l in Hexb. 
          apply IHcb in Hexb. 
          destruct Hexb as [t Hin]. 
          exists t. simpl. right. eauto.
    Qed. 



    Lemma nexb_cblock : forall (cb: list (Constr * KTp)) c , 
      existsb (fun p => constr_eqb I (fst p) c) cb = false -> 
      forall t, ~In (c, t) cb.
    Proof. 
      intros. 
      induction cb. 
      + unfold not; intros; contradiction.
      + simpl in H. destruct (constr_eqb I (fst a) c) eqn: eqid.
        - rewrite <- constr_eqb_eq in eqid;
          destruct a; simpl in *; subst; discriminate.
        - rewrite Bool.orb_false_l in H. 
          apply IHcb in H. unfold not;
          intros contra. simpl in contra; 
          destruct contra; subst; simpl in *; 
          rewrite <- constr_eqb_neq in eqid; 
          contradiction.
    Qed.       
            

    Lemma In_split_cblock : forall c t (cb: list (Constr * KTp)), 
      In (c, t) cb -> In c (fst (split cb)).
    Proof. 
      intros. induction cb; try contradiction .
      simpl in *. 
      destruct a. destruct (split cb).
      simpl. destruct H. inversion H; subst. 
      left; reflexivity. 
      right; eauto.
    Qed.
    
    Lemma split_In_cblock : forall c (cb : list (Constr * KTp)), 
      In c (fst (split cb)) -> exists t, In (c, t) cb.
    Proof. 
      intros. induction cb; try contradiction. 
      simpl in *. destruct a. destruct (split cb). 
      simpl in *. destruct H; subst.
      exists k. left. eauto.
      apply IHcb in H. destruct H. 
      exists x.  right. eauto. 
    Qed. 

  

    Lemma ltd_correct: forall i cb B c t l r,  
      In (i, KTVariant cb) B -> 
      In (c, t) cb -> 
      nodupb (id_eqb I) (fst (split B)) = true -> 
      Some l = dblock_constr B -> 
      nodupb (constr_eqb I) l = true ->
      last_type_def (type_env_ext r B) c = Some (i, KTVariant cb).
    Proof. 
      intros * HInB HInCB HnodupId Hsome HnodupC .
      generalize dependent r.
      generalize dependent l.
      induction B; try contradiction; intros.
      simpl. simpl in HnodupId. destruct a. 
      destruct (split B). simpl in HnodupId. 
      destruct (find _) eqn: eqfind; try discriminate.
      unfold tbind; simpl;
      simpl in HInB; destruct HInB.
      + inversion H; subst. destruct (existsb _) eqn: eqex.
        eauto. 
        apply nexb_cblock with (t := t) in eqex . contradiction.
      + destruct k; simpl in Hsome; try discriminate;
        destruct (existsb _) eqn: eqex.
        * rewrite existsb_exists in eqex.
           destruct (dblock_constr B) eqn: eqB; try discriminate. 
           inversion Hsome; subst.
           destruct eqex as [(c0, k) [HIn Heqc]].
           rewrite <- constr_eqb_eq in Heqc; simpl in Heqc; subst. 
            (* devo giungere ad una contraddizione dall'avere 
               c in fst (split tags) e in fst (split cb). 
               Sfruttiamo il lemma di correttezza per dblock_constr. *)
            assert (Hp: In c l2). {
              apply (dblock_constr_correct i cb B c); eauto. 
              apply In_split_cblock with (t := t); eauto. 
              } 
            assert (Hp': In c (fst (split tags))) by 
              (apply In_split_cblock with (t := k); eauto).
            assert (Hnodupbf: nodupb (constr_eqb I) (fst (split tags) ++ l2) = false). 
            {apply In_false_nodupb with (x := c); eauto. 
             intros. apply Bool.iff_reflect. apply constr_eqb_eq.  }
            rewrite HnodupC in Hnodupbf. discriminate.
        * destruct (dblock_constr B) eqn: eqB; try discriminate. 
          apply IHB with (l := l2); eauto. 
          inversion Hsome. subst. 
          rewrite <- nodupb_eq_NoDup in HnodupC |- *; 
          try (intros; apply Bool.iff_reflect; apply constr_eqb_eq) .
          apply NoDup_app_remove_l with (l := fst (split tags)); 
          eauto.

    Qed.
                  
      

    Theorem tbl_ext_with_constr_correct: forall r r' R R' B d d', 
      TBlockExtends (r, R, B) (r', R', B) -> 
      WFEC d r' R' ->
      Some d' = bind_constr_tblock d B -> 
      WFEC d' r' R'. 
    Proof. 
      intros * HBext HWfec Hsome. 
      unfold WFEC; split; 
      inversion HBext as [r0 R0 B' l HWfet Hnodup1
                          HForall Hconstr Hnodup2]; subst; eauto;
      inversion HWfec as [HWfet' Hlkp]; eauto.
      intros * Hlkp'. 
      apply bind_old_or_new_ex with (d := d) (B := B) in Hlkp'; eauto.
      destruct Hlkp'. 
      + apply Hlkp in H; eauto.
      + repeat destruct H.
        destruct H0.
        exists x0; split; eauto. 
        apply ltd_correct with (t := t) (l := l); 
        eauto.
    Qed.    


    Lemma aux1: forall c t l d i, 
      In (c, t) l -> 
      nodupb (constr_eqb I) (fst (split l)) = true  ->
      lookup (cblock_extends d i l) c = Some (i, t).
    Proof. 
      intros * HIn Hnodupb. 
      induction l; try contradiction. 
      simpl. destruct a. unfold lookup, bind. 
      destruct (constr_eqb I c c0) eqn: eqc. 
      + simpl in HIn. destruct HIn as [Heq | HIn].
        inversion Heq; eauto.  
        simpl in Hnodupb. destruct (split l) eqn: eqsplit.
        simpl in *.
        destruct (find _) eqn: eqfind. discriminate. 
        apply find_none with (x := c) in eqfind. 
        rewrite eqc in eqfind. discriminate. 
        apply In_split_cblock in HIn. 
        rewrite eqsplit in HIn. simpl in *. eauto.
      + simpl in HIn. destruct HIn as [Heq | HIn].  
        inversion Heq; subst. rewrite <- constr_eqb_neq in eqc.
        contradiction. 
        simpl in Hnodupb. destruct (split l) eqn: eqsplit.
        simpl in *.
        destruct (find _) eqn: eqfind. discriminate. 
        eauto.
    Qed.

         
    Lemma not_In_app : forall {X: Type} (x: X) l l', 
      ~In x (l ++ l') -> 
      ~In x l /\ ~In x l'.
    Proof. 
      intros * HInapp. 
      generalize dependent l'. 
      induction l; intros. 
      + simpl in *; unfold not; split; 
        eauto.
      + simpl in *;  
        apply Decidable.not_or in HInapp; 
        unfold not; split; 
        intros; destruct HInapp. 
        * destruct H. contradiction.
          apply IHl in H1. destruct H1. 
          contradiction.
        * apply IHl in H1. destruct H1.  
          contradiction. 
    Qed.      


    Lemma aux3: forall d c i t l i' , 
      lookup d c  = Some (i, t) -> 
      ~In c (fst (split l)) -> 
      lookup (cblock_extends d i' l) c = Some (i, t).
    Proof. 
      intros * Hlkp HIn. 
      induction l. 
      + eauto. 
      + simpl. destruct a. unfold lookup, bind. 
        simpl in HIn. destruct (split l) eqn: eqsplit. 
        simpl in HIn. apply Decidable.not_or in HIn. 
        destruct HIn. 
        destruct (constr_eqb I c c0) eqn: eqc.
        * rewrite <- constr_eqb_eq in eqc. 
          symmetry in eqc. contradiction.
        * eauto.
    Qed.    

    Lemma aux2: forall d d' i l c t B, 
      lookup d c = Some (i, t) ->
      dblock_constr B = Some l ->
      ~In c l -> 
      bind_constr_tblock d B = Some d' ->
      lookup d' c = Some (i, t). 
    Proof.   
      intros * Hlkp Hdb HnIn Hbct.
      generalize dependent l. 
      generalize dependent d'.
      generalize dependent d.
      induction B; intros. 
      + inversion Hbct; subst; eauto.
      + simpl in Hdb. destruct a. 
        destruct k; try discriminate. 
        destruct (dblock_constr B) eqn: eqdb.
        * inversion Hdb; subst. apply not_In_app in HnIn.
          simpl in Hbct. apply IHB with (d := cblock_extends d i0 tags)
          (l := l0); 
          destruct HnIn; eauto. 
          apply aux3; eauto.
        * discriminate.
    Qed.  
        

    Lemma aux4 : forall B l c, 
      dblock_constr B = Some l -> 
      In c l -> 
      exists i cb t, In (i, KTVariant cb) B /\ In (c, t) cb.
    Proof. 
      intros * Hdb HIn. 
      generalize dependent l.
      induction B; intros. 
      + simpl in *; inversion Hdb; subst; contradiction.
      + simpl in *. destruct a. destruct k; try discriminate. 
        destruct (dblock_constr B) eqn: eqdb; try discriminate.
        inversion Hdb; subst.
        apply in_app_or in HIn.
        destruct HIn as [HInl | HInr]. 
        - apply split_In_cblock in HInl. destruct HInl as [t Hinl].
          exists i, tags, t. split; try left; eauto. 
        - assert (Hp: exists i cb t, In (i, KTVariant cb) B /\ In (c, t) cb). 
          {apply IHB with (l := l0); eauto. }
          destruct Hp as [i' [cb [t [HIn1 HIn2 ]]]]. 
          exists i', cb, t. split; try right; eauto.
    Qed.


    Lemma aux5 : forall d' d B l c i t, 
      bind_constr_tblock d B = Some d' ->
      dblock_constr B = Some l -> 
      nodupb (constr_eqb I) l = true -> 
      In c l -> 
      lookup d' c = Some (i, t) -> 
      exists l', In (i, KTVariant l') B /\ In (c, t) l'.
    Proof. 
      intros * Hbtb Hdb Hndpb HIn Hlkp. 
      generalize dependent l. 
      generalize dependent d.
      induction B; intros. 
      + simpl in *; inversion Hdb; subst; contradiction.
      + simpl in *. destruct a. destruct k; try discriminate. 
        destruct (dblock_constr B) eqn: eqdb; try discriminate.
        inversion Hdb; subst.
        apply in_app_or in HIn. 
        destruct HIn as [HIn1 | HIn2].
        * apply split_In_cblock in HIn1. destruct HIn1 as [t' HIn1].  
          pose proof HIn1 as HIn1'.
          apply In_split_cblock in HIn1;
          assert (Haux1: lookup (cblock_extends d i0 tags) c = Some (i0, t')). 
          {   
              rewrite <- nodupb_eq_NoDup in Hndpb.
              apply NoDup_app_remove_r in Hndpb. 
              apply nodupb_eq_NoDup with (eqb := constr_eqb I) in Hndpb.
              apply aux1; eauto. apply constr_refl. apply constr_refl. 
          }
          assert (HnIn : ~In c l0) by (
            apply nodupb_In_false with 
            (eqb := constr_eqb I) (l := (fst (split tags))); 
            eauto; apply constr_refl
          ).
          assert (Hlkpc: lookup d' c = Some (i0, t')) by (
              apply aux2 with (d := cblock_extends d i0 tags)
              (l:= l0) (B := B); eauto
          ).  
          rewrite Hlkpc in Hlkp.
          inversion Hlkp ;subst. exists tags; split; eauto.
        * assert (H: exists l', In (i, KTVariant l') B /\ In (c, t) l'). 
          {apply IHB with (d := cblock_extends d i0 tags) (l := l0); eauto. 
           rewrite <- nodupb_eq_NoDup in Hndpb. 
           apply NoDup_app_remove_l in Hndpb.
           rewrite <- nodupb_eq_NoDup; eauto; apply constr_refl.
           apply constr_refl. } 
           repeat destruct H. exists x. split; try right; eauto.
    Qed.


    Lemma aux6 : forall d i' l c i t, 
      lookup (cblock_extends d i' l) c = Some (i, t) -> 
      ~In c (fst (split l)) -> 
      lookup d c = Some (i, t).
    Proof. 
      intros * Hlkp HnIn. 
      generalize dependent d. 
      induction l; intros. 
      + simpl in *. eauto.
      + simpl in *. destruct a. destruct (split l). 
        unfold lookup, bind in Hlkp.
        simpl in HnIn. apply Decidable.not_or in HnIn.
        destruct HnIn as [HnInl HnInr].
        destruct (constr_eqb I c c0) eqn: eqc. 
        * rewrite <- constr_eqb_eq in eqc; subst.  
          contradiction.
        * apply IHl; simpl; eauto.
    Qed. 


    Lemma aux7 : forall d' d c i t B l, 
      lookup d' c = Some (i, t) -> 
      bind_constr_tblock d B = Some d' -> 
      dblock_constr B = Some l -> 
      ~In c l -> 
      lookup d c = Some (i, t).
    Proof.
      intros * Hlkp Hbd Hdb HnIn. 
      generalize dependent l. 
      generalize dependent d. 
      induction B; intros. 
      + simpl in *. inversion Hbd; subst; eauto. 
      + simpl in *. destruct a. destruct k; try discriminate. 
        destruct (dblock_constr _) eqn: eqdb; try discriminate. 
        inversion Hdb; subst.
        apply not_In_app in HnIn. destruct HnIn as [HnIn1 HnIn2]. 
        assert (H: lookup (cblock_extends d i0 tags) c = Some (i, t)).
        {apply IHB with (d := cblock_extends d i0 tags) (l := l0); eauto. }
        apply aux6 in H; eauto.
    Qed. 
    
    
    Lemma aux8 : forall r c i l B l', 
      dblock_constr B = Some l -> 
      ~In c l -> 
      last_type_def r c = Some (i, KTVariant l') ->
      last_type_def (type_env_ext r B) c = Some (i, KTVariant l').
    Proof.
      intros * Hdb HnIn Hltd. 
      generalize dependent l.
      generalize dependent r. 
      induction B; intros. 
      + eauto. 
      + simpl in *. destruct a. destruct k; try discriminate.
        destruct (dblock_constr _) eqn: eqdb; try discriminate.
        inversion Hdb; subst. 
        apply not_In_app in HnIn. destruct HnIn as [HnIn1 HnIn2]. 
        unfold tbind. simpl. destruct (existsb _) eqn: eqx.
        * apply existsb_exists in eqx. 
          destruct eqx as [(c', t) [HIn Heq]]. 
          rewrite <- constr_eqb_eq in Heq. simpl in *. 
          subst. apply In_split_cblock in HIn. contradiction.
        * apply IHB with (l := l0); eauto.
    Qed.   

             
    
    Theorem tbl_ext_with_constr_correct2: forall r r' R R' B d d', 
      TBlockExtends (r, R, B) (r', R', B) -> 
      WFEC d r R ->
      Some d' = bind_constr_tblock d B -> 
      WFEC d' r' R'. 
    Proof. 
      intros * HBext HWfec Hsome. 
      unfold WFEC; split; 
      inversion HBext as [r0 R0 B' l HWfet Hnodup1
                          HForall Hconstr Hnodup2]; subst; eauto;
      inversion HWfec as [HWfet' Hlkp].
      + apply TBlockExtends_correct with (r := r) ( R:=R) (B := B).
        eauto. 
      + intros * Hlkp'.  
        destruct B. 
        * simpl in *; inversion Hsome; subst. eauto.
        * simpl in Hsome. simpl. destruct p. unfold tbind. simpl. 
          destruct k; try discriminate.
          simpl in Hconstr. destruct (dblock_constr _) eqn: Hdb; 
          try discriminate.
          destruct (existsb _) eqn: eqfind.
          - apply exb_cblock in eqfind. destruct eqfind as [t' HIn].  
            inversion Hconstr. subst.   
            pose proof HIn as HInt'.
            apply In_split_cblock in HIn;
            assert (Haux1: lookup (cblock_extends d i0 tags) c = Some (i0, t')). 
            {   
            rewrite <- nodupb_eq_NoDup in Hnodup2.
            apply NoDup_app_remove_r in Hnodup2. 
            apply nodupb_eq_NoDup with (eqb := constr_eqb I) in Hnodup2.
            apply aux1; eauto. apply constr_refl. apply constr_refl. 
            }
            assert (HnIn : ~In c l0) by (apply nodupb_In_false with 
              (eqb := constr_eqb I) (l := (fst (split tags))); 
              eauto; apply constr_refl).
            assert (Hlkpc: lookup d' c = Some (i0, t')). 
            {apply aux2 with (d := cblock_extends d i0 tags)
              (l:= l0) (B := B); eauto. } 
            rewrite Hlkpc in Hlkp'.
            inversion Hlkp' ;subst. exists tags; split; eauto.
          
          - simpl in Hnodup1. destruct (split B) eqn: eqsplitB.
            simpl in Hnodup1. destruct (find _) eqn: eqfnd. discriminate.
            inversion Hconstr; subst. 
            rewrite <- nodupb_eq_NoDup in Hnodup2;
            pose proof Hnodup2 as HNoDup2;
            try apply NoDup_app_remove_l in Hnodup2; 
            try rewrite nodupb_eq_NoDup with (eqb := constr_eqb I) in Hnodup2;  
            destruct (find (fun x => constr_eqb I x c) l0) eqn: eqfind'; 
            try apply constr_refl.
            -- apply find_some in eqfind'. destruct eqfind' as [HInl0 Heqc].
               rewrite <- constr_eqb_eq in Heqc; subst.
              assert (H: exists l', In (i, KTVariant l') B /\ In (c, t) l'). 
              {apply aux5 with (d' := d') (d := cblock_extends d i0 tags) (l := l0); 
              eauto. } 
              destruct H as [l' [HIn1 HIn2]]. exists l'. 
              split; try eauto. apply ltd_correct with (t := t) (l := l0); 
              try rewrite eqsplitB; eauto.
            -- apply find_none_not_In in eqfind'.  
               assert (Hp1: lookup (cblock_extends d i0 tags) c = Some (i, t)). 
               {apply aux7 with (d' := d') (B := B) (l := l0); 
                eauto. }
               assert (Hp2: lookup d c = Some (i, t)). 
               {apply aux6 with (i' := i0) (l := tags); eauto.
                unfold not. intro contra . 
                apply split_In_cblock in contra. 
                destruct contra as [t']. 
                apply nexb_cblock with (t := t') in eqfind.
                contradiction. }
               apply Hlkp in Hp2. destruct Hp2 as [l' [Hltd HIn]].
               exists l'. split; try apply aux8 with (l := l0); eauto.
               apply constr_refl.
    Qed.         
               

               
              
            
            (* assert (Hp: lookup (cblock_extends d i0 tags) c = Some (i, t) \/ 
                   exists j l, i = j /\ In (j, KTVariant l) B /\ In (c, t) l).
            {apply bind_old_or_new_ex with (d' := d'); eauto. }
            destruct (find (fun x => constr_eqb I x c) l0) eqn: eqfind'.
            -- apply find_some in eqfind'. destruct eqfind' as [HInl0 Heqc].
               rewrite <- constr_eqb_eq in Heqc; subst.
               assert (Hex: exists i cb t, 
                  In (i, KTVariant cb) B /\ In (c, t) cb). 
               {apply aux4 with (l:= l0); eauto. }
               destruct Hex as [i' [cb [t' [HInB HIncb]]]].
               exists cb. split. 
               apply ltd_correct with (t := t') (l := l0); 
               try rewrite eqsplitB; eauto. simpl.   *)



    Lemma fooo: forall c t t' (l: list (Constr * KTp)),  
      NoDup (fst (split l)) ->
      In (c, t) l -> 
      In (c, t') l -> 
      t = t'.
    Proof.
      intros * HNoDup HIn1 HIn2.
      induction l. try contradiction. intros. 
      simpl in HNoDup. destruct a . 
      destruct (split l) eqn: l'.
      simpl in HNoDup. inversion HNoDup; subst. 
      simpl in *. 
      destruct HIn2 as [Heq | HIn2]. 
      + destruct HIn1.   
        - inversion H. inversion Heq; subst. eauto.
        - inversion Heq; subst. 
          apply In_split_cblock in H. 
          rewrite l' in H; simpl in *. contradiction.
      + destruct HIn1. 
        - inversion H; subst. 
          apply In_split_cblock in HIn2. 
          rewrite l' in HIn2; simpl in *. contradiction.
        - apply IHl; eauto. 
    Qed.         
           
    
    

          
                



    
    (* spec of static elaboration *)
    Inductive Elab : KExpr -> tenv -> register -> constr_env -> LExpr -> Prop :=   
     |Elab_Var      : forall i r R d, 
                       WFET r R -> 
                       WFEC d r R -> 
                       Elab (KVar i) r R d (LVar i) 
     |Elab_Lit      : forall x r R d, 
                       WFET r R -> 
                       WFEC d r R -> 
                       Elab (KLit x) r R d (LLit x)
     |Elab_Op       : forall op l l' r R d,  
                       WFET r R -> 
                       WFEC d r R -> 
                       Forall2 (fun e le => Elab e r R d le) l l' -> 
                       Elab (KOp op l) r R d (LOp op l')
     |Elab_Lam      : forall p e e' r R d, 
                       WFET r R -> 
                       WFEC d r R -> 
                       is_WFP d p = true -> 
                       Elab e r R d e' -> 
                       Elab (KLam p e) r R d (LLam p e')  
     |Elab_App      : forall e1 e1' e2 e2' r R d, 
                       WFET r R -> 
                       WFEC d r R -> 
                       Elab e1 r R d e1' ->
                       Elab e2 r R d e2' -> 
                       Elab (KApp e1 e2) r R d (LApp e1' e2') 
     |Elab_Unit     : forall r R d, 
                       WFET r R -> 
                       WFEC d r R -> 
                       Elab KUnit r R d LUnit 
     |Elab_Nil      : forall r R d, 
                       WFET r R -> 
                       WFEC d r R ->
                       Elab KNil r R d LNil 
     |Elab_Pair     : forall e1 e1' e2 e2' r R d, 
                       WFET r R -> 
                       WFEC d r R -> 
                       Elab e1 r R d e1' -> 
                       Elab e2 r R d e2' -> 
                       Elab (KPair e1 e2) r R d (LPair e1' e2') 
     |Elab_Cons     : forall e1 e1' e2 e2' r R d, 
                       WFET r R -> 
                       WFEC d r R -> 
                       Elab e1 r R d e1' -> 
                       Elab e2 r R d e2' -> 
                       Elab (KCons e1 e2) r R d (LCons e1' e2')
     |Elab_Variant : forall c (inf: Ide * KTp) e e' r R d, 
                       WFET r R -> 
                       WFEC d r R -> 
                       lookup d c = Some inf -> 
                       Elab e r R d e' -> 
                       Elab (KVariant c e) r R d (LVariant c inf e')
     |Elab_Fix      : forall name cls cls' r R d, 
                       WFET r R -> 
                       WFEC d r R -> 
                       Elab cls r R d cls' ->  
                       Elab (KFix name cls) r R d (LFix name cls')  
     |Elab_DefType  : forall B e e' r r' R R' d d', 
                       WFET r R -> 
                       WFEC d r R -> 
                       tblock_extends r R B = Ok(r', R') ->
                       bind_constr_tblock d B = Some d' ->  
                       Elab e r' R' d' e'  ->
                       Elab (KDefType B e) r R d e'    
     |Elab_Match    : forall e e' l l' r R d, 
                        WFET r R -> 
                        WFEC d r R -> 
                        Elab e r R d e' -> 
                        Forall2 (fun p p' => 
                          is_WFP d (fst p) = true /\ 
                          fst p = fst p' /\ 
                          Elab (snd p) r R d (snd p')) l l' -> 
                        Elab (KMatch e l) r R d (LMatch e' l') 
     |Elab_Error    : forall m r R d, 
                        WFET r R ->   
                        WFEC d r R -> 
                        Elab (KError m) r R d (LError m) .

   

                        
    Definition elab_result := result LExpr string.  
    Definition ok_LLam p e : elab_result := Ok (LLam p e). 
    Definition ok_LApp e1 e2 : elab_result := Ok (LApp e1 e2).
    Definition ok_LPair e1 e2 : elab_result := Ok (LPair e1 e2). 
    Definition ok_LCons e1 e2 : elab_result := Ok (LCons e1 e2).
    Definition ok_LVariant c inf e : elab_result := Ok (LVariant c inf e). 
    Definition ok_LFix i e : elab_result := Ok (LFix i e).   
          

    Fixpoint elab (e: KExpr) (r: tenv) (R: register) (d: constr_env) : elab_result := 
      match e with 
      |KVar i       => Ok (LVar i)
      |KLit x       => Ok (LLit x) 
      |KOp op l     => 
          let lr' := map (fun e => elab e r R d) l in 
          (match find_error lr' with 
          |Some err => err 
          (* here we use LUnit as a dummy default expression for map_result. *)
          |None => Ok (LOp op (map_result lr' LUnit)) 
          end) 
      |KLam p e     => if is_WFP d p then elab e r R d >>= ok_LLam p  
                       else Error ("using an ill-formed pattern as a function parameter"%string)
      |KApp e1 e2   => elab e1 r R d >>= (fun x => elab e2 r R d >>= ok_LApp x)
      |KUnit        => Ok LUnit
      |KNil         => Ok LNil
      |KPair e1 e2  => elab e1 r R d >>= (fun x => elab e2 r R d >>= ok_LPair x)
      |KCons e1 e2  => elab e1 r R d >>= (fun x => elab e2 r R d >>= ok_LCons x)
      |KVariant c e => (match lookup d c with  
                        |Some inf  => elab e r R d >>= ok_LVariant c inf 
                        |None      => Error ("constructor '" ++ (constr_to_string I c) ++ "' doesn't exist")%string 
                        end)
      |KFix i e     => elab e r R d >>= ok_LFix i 
      |KDefType B e => match tblock_extends r R B with 
                       |Ok(r', R')  => match bind_constr_tblock d B with 
                                       |Some d' => elab e r' R' d' 
                                       |None    => Error ("only variant types can be declared"%string) 
                                       end 
                       |Error err   => Error err  
                       end 
      |KMatch e l   => elab e r R d >>= (fun e' => 
                          if forallb (fun '(p, _) => is_WFP d p) l then
                            let l' := map (fun '(p, e) => (p, elab e r R d)) l in 
                            (match find (fun '(_, e) => is_error e) l' with 
                             (* here we use LUnit as a dummy default expression for map_result function.*)
                              |None          => Ok (LMatch e' (map_snd_result l' LUnit)) 
                              |Some (_, err) => err
                              end) 
                          else Error ("using an ill-formed pattern as a match case"%string)) 
      |KError m => Ok (LError m) 
      end .

 
      Theorem elab_correct : forall e r R d e',
        WFET r R -> 
        WFEC d r R ->  
        elab e r R d = Ok e' ->
        Elab e r R d e'.
      Proof.
        intros * Hwfet Hwfec Helab. 
        generalize dependent e'. 
        generalize dependent d. 
        generalize dependent r.
        generalize dependent R. 
        induction e using KExpr_ind'; intros. 
        + simpl in Helab. inversion Helab. apply Elab_Var; eauto.
        + simpl in Helab. inversion Helab. apply Elab_Lit; eauto.
        + simpl in Helab. destruct (find_error _) eqn: eqfind. 
          ++ apply find_error_is_error in eqfind. 
             apply is_error_correct in eqfind.
             destruct eqfind; subst; discriminate.
          ++ inversion Helab. apply Elab_Op; eauto. 
              remember (map_result (map (fun e0 : KExpr => elab e0 r R d) l) LUnit)
                as l'. 
              generalize dependent e'. generalize dependent l'.
              induction l.
              ** intros. simpl in *; subst. apply Forall2_nil.
              ** intros. simpl in *. rewrite Heql'.
                apply Forall2_cons.
                {inversion H; subst; apply H3 with (e' := get_ok (elab a r R d) LUnit);
                  destruct (is_error (elab a r R d)) eqn: eqerr; eauto.
                  + discriminate.
                  + apply get_ok_correct with (def := LUnit) in eqerr; 
                    eauto. }
                {destruct l'; try discriminate. 
                  inversion Heql'. apply IHl with (e' := LOp op l') ;
                  inversion H; 
                  try f_equal; subst; 
                  eauto. 
                  destruct (is_error (elab a r R d)) ; try discriminate. eauto. }
        + simpl in Helab. destruct (is_WFP _) eqn: eqwfp;  
          destruct (elab e r R d) eqn: Hel; unfold ok_LLam in Helab;
          simpl in *; inversion Helab; apply Elab_Lam; 
          try apply is_WFP_correct; eauto.
        + intros. simpl in Helab.
          destruct (elab e1 r R d) eqn: Hel1; 
          simpl in Helab; try discriminate. 
          destruct (elab e2 r R d) eqn: Hel2; 
          unfold ok_LApp in Helab; simpl in *; 
          inversion Helab; apply Elab_App; eauto.
        + intros. simpl in Helab; inversion Helab; apply Elab_Unit; eauto.
        + intros. simpl in Helab; inversion Helab; apply Elab_Nil; eauto.
        + intros. simpl in Helab.
          destruct (elab e1 r R d) eqn: Hel1;
          simpl in Helab; try discriminate. 
          destruct (elab e2 r R d) eqn: Hel2; 
          unfold ok_LApp in Helab; simpl in *; 
          inversion Helab; apply Elab_Pair; eauto.
        + intros. simpl in Helab.
          destruct (elab e1 r R d) eqn: Hel1; 
          simpl in Helab; try discriminate. 
          destruct (elab e2 r R d) eqn: Hel2; 
          unfold ok_LApp in Helab; simpl in *; 
          inversion Helab; apply Elab_Cons; eauto.
        + intros. simpl in Helab.      
          destruct (lookup d c) eqn: eqlkp; try discriminate.
          unfold ok_LVariant in Helab. 
          destruct (elab e r R d) eqn: Hel; simpl in *; 
          inversion Helab; apply Elab_Variant; eauto.
        + intros. simpl in Helab.
          destruct (elab e r R d) eqn: Hel; 
          simpl in Helab; try discriminate.
          inversion Helab. apply Elab_Fix; eauto. 
        + simpl in Helab. destruct (tblock_extends _) eqn: Htbext. 
          * destruct p. destruct (bind_constr_tblock _) eqn: Hbctbl. 
            ** apply Elab_DefType with (r' := t) (d' := c) (R' := r0); 
                try apply IHe; eauto.
                - apply TBlockExtends_correct with (r := r) (R:= R) (B:= l).
                  apply tbl_ext_correct; eauto.
                - apply tbl_ext_with_constr_correct2 with 
                  (r := r) (R := R) (B:= l) (d := d); eauto.
                  apply tbl_ext_correct; eauto.
            ** discriminate.
          * discriminate. 
        + simpl in Helab. destruct (elab e r R d) eqn: Hel; try discriminate.
          simpl in Helab. destruct (forallb _) eqn: Hforall; try discriminate. 
          destruct (find _) eqn: eqfind. 
          destruct p; subst. apply find_some in eqfind.
          destruct eqfind as [_ contra]. simpl in contra. discriminate.
          inversion Helab; subst.
          apply Elab_Match; eauto. 
          remember (map_snd_result 
           (map (fun '(p, e0) => (p, elab e0 r R d)) l) LUnit) as l'. 
          generalize dependent l'.
          induction l; intros.
          ** simpl in *; subst. apply Forall2_nil.
          ** simpl in *. destruct a. rewrite Heql'.
             apply Forall2_cons.
             {rewrite Bool.andb_true_iff in Hforall.
              destruct Hforall as [Hwfp Hforall]. 
              repeat split. eauto. simpl.
              inversion H; subst. apply H2 with (e' := get_ok (elab k0 r R d) LUnit);
              destruct (is_error (elab k0 r R d)) eqn: eqerr; eauto.
              + discriminate.
              + apply get_ok_correct with (def := LUnit) in eqerr; 
                eauto. }
             {destruct l'; try discriminate. 
              inversion Heql'. apply IHl;
              inversion H; subst; 
              destruct (is_error (elab k0 r R d)) ; try discriminate; 
              rewrite Bool.andb_true_iff in Hforall; 
              destruct Hforall; eauto. }
        + simpl in Helab; inversion Helab; subst; apply Elab_Error; eauto.
      Qed.  


      Lemma In_Error: forall m r R d l, 
       In (Error m) (map (fun e => elab e r R d) l) -> 
       exists e', In e' l /\ elab e' r R d = Error m.
      Proof. 
        intros * HIn .
        induction l; simpl in *; try contradiction.
        destruct HIn as [Hel | HIn]. 
        exists a. split; try left; eauto.
        apply IHl in HIn. destruct HIn as [x [*]]. 
        exists x. split; try right; eauto.
      Qed.
      
      Lemma Forall2_In_ex: forall l r R d l' e1, 
       Forall2 (fun e le => Elab e r R d le) l l' -> 
       In e1 l -> 
       exists e2, Elab e1 r R d e2.
      Proof. 
        intros * HForall HIn.
        generalize dependent l'. 
        induction l; intros; try contradiction. 
        simpl in HIn. destruct HIn as [Heq | HIn]; 
        inversion HForall; subst.
        exists y. eauto. 
        apply IHl with (l' := l'0); eauto.
      Qed.


      Lemma forallb_false : forall l d, 
        forallb (fun '(p, _) => is_WFP d p) l = false -> 
        exists (x: KPat * KExpr), In x l /\ is_WFP d (fst x) = false. 
      Proof.  
        intros * Hforallb. 
        induction l; try discriminate.
        simpl in Hforallb. 
        rewrite Bool.andb_false_iff in Hforallb.
        destruct Hforallb as [Hwfp | Hforallb]. 
        + destruct a. exists (k, k0). split; simpl; eauto.
        + apply IHl in Hforallb. destruct Hforallb as [x H].
          destruct H; exists x; split; simpl; eauto.      
      Qed.

      Lemma Forall2_In : forall d p r R l l', 
        Forall2 (fun p p' => is_WFP d (fst p) = true /\ 
                             fst p = fst p' /\ 
                             Elab (snd p) r R d (snd p')) l l' ->
        In p l -> 
        is_WFP d (fst p) = true. 
      Proof. 
        intros * HForall HIn.
        generalize dependent l'. 
        induction l; intros; try contradiction.
        simpl in HIn. destruct HIn as [Heq | HIn]; 
        inversion HForall; subst.
        + destruct H1; eauto.
        + eauto.
      Qed.  


      Theorem elab_correct_err: forall e r R d m e', 
        WFET r R -> 
        WFEC d r R -> 
        elab e r R d = Error m -> 
        ~Elab e r R d e'.
      Proof. 
        intros * HWfet HWfec Hel. 
        unfold not. intro HEl. 
        generalize dependent e'. 
        generalize dependent d. 
        generalize dependent R. 
        generalize dependent r.
        induction e using KExpr_ind'; intros; 
        simpl in Hel; try discriminate.
        + destruct (find_error _) eqn: eqfind; try discriminate.
          generalize dependent e'. 
          induction l; intros; simpl in *; try discriminate.
          destruct (is_error _) eqn: eqerr; 
          unfold is_error in eqerr; 
          destruct (elab _) eqn: eqel; try discriminate;
          inversion H; inversion HEl; inversion H12; subst.
          * apply H2 with (r := r) (R := R) (d := d) (e' := y); 
            inversion eqfind; subst; eauto. 
          * assert (Hind: Elab (KOp op l) r R d (LOp op l'0)). 
            {apply Elab_Op; eauto. }
            pose proof eqfind as eqfind'.
            unfold find_error in eqfind. 
            apply find_some in eqfind.
            destruct eqfind as [HInerr]. 
            apply In_Error in HInerr.
            destruct HInerr as [e1 [HIn Hel]].
            apply Forall2_In_ex with (e1 := e1) in H17; 
            eauto. 
        + destruct (is_WFP _) eqn: eqwfp.
          * destruct (elab _) eqn: eqel; simpl in *; 
            unfold ok_LLam in Hel; try discriminate;
            inversion Hel; subst; inversion HEl; subst;   
            eauto.
          * inversion HEl; subst; rewrite eqwfp in H3; discriminate.
        + inversion HEl; 
          destruct (elab _) eqn: eqel; simpl in *. 
          * destruct (elab e2 _) eqn: eqel2; try discriminate.
            simpl in Hel; inversion Hel; subst.
            apply IHe2 with (r := r) (R := R) (d := d) (e' := e2'); 
            eauto.
          * inversion Hel; subst. 
            apply IHe1 with (r := r) (R := R) (d := d) (e' := e1');
            eauto.
        + inversion HEl; 
          destruct (elab _) eqn: eqel; simpl in *. 
          * destruct (elab e2 _) eqn: eqel2; try discriminate.
            inversion Hel; subst.
            apply IHe2 with (r := r) (R := R) (d := d) (e' := e2'); 
            eauto.
          * inversion Hel; subst. 
            apply IHe1 with (r := r) (R := R) (d := d) (e' := e1');
            eauto.
        + inversion HEl;  
          destruct (elab _) eqn: eqel; simpl in *. 
          * destruct (elab e2 _) eqn: eqel2; try discriminate.
            inversion Hel; subst.
            apply IHe2 with (r := r) (R := R) (d := d) (e' := e2'); 
            eauto.
          * inversion Hel; subst. 
            apply IHe1 with (r := r) (R := R) (d := d) (e' := e1');
            eauto.
        + inversion HEl; subst.
          destruct (lookup _) eqn: eqlkp; try discriminate.
          destruct (elab _) eqn: eqel; simpl in *;
          inversion Hel; subst; try discriminate;
          apply IHe with (r := r) (R := R) (d := d) (e' := e'0); 
          eauto.
        + inversion HEl; subst.
          destruct (elab _) eqn: eqel; simpl in *;
          inversion Hel; subst; try discriminate;
          apply IHe with (r := r) (R := R) (d := d) (e' := cls'); 
          eauto.
        + inversion HEl; subst.
          destruct (tblock_extends _) eqn: eqtb; try discriminate.
          destruct p; destruct (bind_constr_tblock _) eqn: eqbind; 
          try discriminate. inversion H3; inversion H4; subst.
          apply IHe with (r := r') (R := R') (d := d') (e' := e'); 
          eauto; apply tbl_ext_correct in eqtb;
          pose proof eqtb as eqtb';
          try apply TBlockExtends_correct in eqtb; eauto;
          apply tbl_ext_with_constr_correct2 with 
           (r := r)(R := R) (d := d) (B := l); eauto.
        + inversion HEl; subst.
          destruct (elab _) eqn : eqel; simpl in *.
          * destruct (forallb _) eqn: eqfll. 
            - destruct (find _) eqn : eqfind; try discriminate.
              destruct p. generalize dependent l'; 
              induction l; intros.
              {simpl in eqfind. discriminate. }
              {simpl in eqfind. destruct a; inversion H; 
               inversion H9; subst; simpl in eqfll; 
               rewrite Bool.andb_true_iff in eqfll;
               destruct eqfll.
               destruct (is_error _) eqn: eqerr; unfold is_error in eqerr.
               * destruct (elab k1 _) eqn:eqelk1; try discriminate.
                 inversion eqfind; subst. destruct H10 as [_ [_ H10]].
                 apply H5 with (r := r) (R := R) (d := d) (e' := (snd y)); 
                 eauto.
              * assert (Hind: Elab (KMatch e l) r R d (LMatch e'0 l'0)). 
                {apply Elab_Match; eauto. }
                inversion H; subst.
                apply IHl with (l' := l'0); eauto. }
            - apply forallb_false in eqfll.
              destruct eqfll as [p [* Hwfp]].
              apply Forall2_In with (p := p) in H9 ; eauto.
              rewrite H9 in H0; discriminate.
          * inversion Hel; subst; apply IHe with 
            ( r:= r) (R := R) (d:= d) (e':= e'0); eauto.
      Qed.
              
        
(*           
      Theorem elab_complete : forall e r R d e', 
       Elab e r R d e' -> elab e r R d = Ok e'.
      Proof. 
        intros * HElab. 
        induction HElab; simpl; eauto. 
        + destruct (find_error _) eqn: eqfind.
          destruct l; simpl in eqfind; try discriminate. 
          destruct (is_error _) eqn: eqerr.
          unfold is_error in eqerr.
          destruct (elab _) eqn: eqel; try discriminate.
          inversion H1; subst. 
          simpl in eqerr.
          inversion eqfind. unfold find_error in eqfind.
          simpl in eqfind.
              *)
                      
                          
        









     
                
                                  
    
End ELABORATION.
