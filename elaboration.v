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
    Local Notation " 'constr_eqb' " := (@constr_eqb I).
    Local Notation " 'id_eqb' " := (@id_eqb I).


    Ltac inversion_subst H := inversion H; subst; clear H.
    Ltac solve_base := try constructor; eauto.
    Ltac discard_case := 
      try contradiction; 
      try (simpl in *; discriminate).


    (* useful lemmas *)
    Lemma existsb_true_In_cblock : 
      forall (l : list (Constr * KTp)) c, 
        existsb (fun p => constr_eqb (fst p) c) l = true -> 
        exists t, In (c, t) l.
    Proof.
      intros * Hexb. induction l as [| (c', t') tail]; discard_case. 
      simpl in Hexb. destruct (constr_eqb c' c) eqn: eqc. 
      + rewrite <- constr_eqb_eq in eqc; subst. 
        exists t'. simpl; eauto. 
      + rewrite Bool.orb_false_l in Hexb. 
        apply IHtail in Hexb. destruct Hexb as [t *]. 
        exists t. simpl. right. eauto.
    Qed. 


    Lemma existsb_false_not_In_cblock : 
      forall (l: list (Constr * KTp)) c , 
        existsb (fun p => constr_eqb (fst p) c) l = false -> 
        forall t, ~In (c, t) l.
    Proof. 
      intros * Hexb. induction l as [| (c', t') tail]. 
      + unfold not; intros; contradiction.
      + intro t. simpl in Hexb. rewrite Bool.orb_false_iff in *.
        destruct Hexb as [Heq Hexb]. 
        destruct (constr_eqb _) eqn: eqc; discard_case.
        unfold not; intro contra. simpl in contra.
        destruct contra as [Hneq | HIn].
        * inversion_subst Hneq. rewrite <- constr_eqb_neq in eqc.
          contradiction.
        * apply IHtail in HIn; eauto.
    Qed.  
            

    Lemma In_split_cblock : 
      forall c t (l: list (Constr * KTp)), 
        In (c, t) l -> 
        In c (fst (split l)).
    Proof. 
      intros * HIn. 
      induction l as [| (c', t') tail]; discard_case .
      simpl in *. destruct (split _).
      simpl. destruct HIn as [HEq | HIn].
      + inversion_subst HEq; left; reflexivity.
      + right; eauto. 
    Qed.
    

    Lemma split_In_cblock : 
      forall c (l : list (Constr * KTp)), 
        In c (fst (split l)) -> 
        exists t, In (c, t) l.
    Proof. 
      intros * HIn. 
      induction l as [| (c', t') tail]; discard_case. 
      simpl in *. destruct (split _). 
      simpl in *. destruct HIn as [HEq | HIn]. 
      + subst. exists t'. left. reflexivity.
      + apply IHtail in HIn. destruct HIn as [t *].
        exists t. right. eauto.
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
      + simpl in *. apply Decidable.not_or in HInapp. 
        unfold not; split; intros; destruct HInapp. 
        * destruct H. contradiction.
          apply IHl in H1. destruct H1. 
          contradiction.
        * apply IHl in H1. destruct H1.  
          contradiction. 
    Qed.      

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
    |LFix (name: Ide) (e: LExpr)  
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
      fold_right (fun '(i, _) e => bind e i tt id_eqb) R B.

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
    



    Lemma dblock_constr_correct1 : forall i l B c l', 
      In (i, KTVariant l) B -> 
      In c (fst (split l)) -> 
      dblock_constr B = Some l' -> 
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
 

    
    Lemma dblock_constr_correct2 : forall B l c, 
      dblock_constr B = Some l -> 
      In c l -> 
      exists i cb t, In (i, KTVariant cb) B /\ In (c, t) cb.
    Proof. 
      intros * Hdb HIn. 
      generalize dependent l.
      induction B as [| (i', t') tail]; intros. 
      + simpl in *; inversion Hdb; subst; contradiction.
      + simpl in *. destruct t'; discard_case. 
        destruct (dblock_constr tail) eqn: eqtail; discard_case.
        inversion_subst Hdb. apply in_app_or in HIn.
        destruct HIn as [HInl | HInr]. 
        - apply split_In_cblock in HInl. destruct HInl as [t Hinl].
          exists i', tags, t. split; eauto. 
        - apply IHtail in HInr; eauto. 
          destruct HInr as [i [cb [t [HIn1 HIn2 ]]]]. 
          exists i, cb, t. split; try right; eauto.
    Qed.


    (* TBlockElab formalizes the elaboration 
       of a type declaration block . *)
    Inductive TBlockElab: tbe_state -> tbe_state -> Prop := 
    |TBElab : forall r R B l, 
                WFET r R -> 
                nodupb id_eqb (fst (split B)) = true -> 
                Forall (DT (early_binding R B)) (snd (split B)) ->  
                dblock_constr B = Some l -> 
                nodupb (constr_eqb) l = true ->  
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
          destruct (id_eqb i i') eqn: eqid. 
          (* id_eqb I i i' = true *)
          * unfold dom, lookup. exists tt. simpl.
            unfold bind. rewrite eqid; eauto.
          (* id_eqb I i i' = false *)
          * unfold tdom, tlookup, tbind in IHB. 
            assert (Hp: exists y, 
             assoc_opt (type_env_ext r B) i id_eqb = Some y) by 
            (exists x; eauto).  
            apply IHB in Hp. simpl. unfold dom, lookup, bind in *.
            destruct Hp. exists x0. rewrite eqid. eauto.
      (* <- *)
      + intros HDom; induction B; intros. 
        - simpl in *; apply Hdom; eauto.
        - simpl in HDom. destruct a as (i', t);
          unfold dom, lookup, bind in HDom;
          destruct HDom as [x HDom];  
          destruct (id_eqb i i') eqn: eqid.
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
      destruct (id_eqb i i') eqn: eqid; eauto.
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
        destruct (id_eqb i' i) eqn: eqid.
        (* id_eqb I i' i = true *)
        * right. destruct (split B). simpl.
          left. inversion_subst Htext; eauto.
        (* id_eqb I i' i = false *)
        * assert (Hp: exists i,  
           assoc_opt (type_env_ext r B) i id_eqb = Some t) by 
           (exists i'; eauto). apply IHB in Hp. 
          destruct Hp as [[i'' Hp] | HIn ].
          - left; eauto. 
          - destruct (split B). simpl; right; eauto.
    Qed.        



    (* TBlockElab extends (r, R) preserving well-formedness *)
    Theorem TBlockElab_preserves_wfet : forall r R r' R' B, 
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
    Definition tblock_elab r R B : tdblock_ext_result := 
      if nodupb id_eqb (fst (split B)) then 
        let R' := early_binding R B in 
        if forallb (fun p => is_DT R' (snd p)) B then
          match dblock_constr B with 
          |Some l  => if nodupb constr_eqb l then 
                        Ok (type_env_ext r B, R') 
                      else 
                        Error ("duplicated constructor is declared in the same block"%string)
          |None    => Error ("implementation error: invalid type has been declared"%string)
          end 
        else Error ("declaration of invalid type"%string)
      else Error ("duplicated name is declared in the same block"%string). 
      
    

    Lemma Forall_split_conv : forall {X Y} P (l: list (X * Y)), 
     Forall P (snd (split l)) <-> Forall (fun p => P (snd p)) l.
    Proof. 
      split; intros; induction l; 
      try apply Forall_nil; simpl in *;
      destruct a; destruct (split l); simpl;  
      apply Forall_cons; inversion H; subst;  
      try discriminate; eauto. 
    Qed.        

    
    
    Theorem tbl_elab_correct: forall r r' R R' B,
      WFET r R ->  
      tblock_elab r R B = Ok (r', R') -> 
      TBlockElab (r, R, B) (r', R', B).
    Proof. 
      intros * HWfet Hb_ext. 
      unfold tblock_elab in Hb_ext. 
      destruct (nodupb _) eqn: eqnodup; discard_case. 
      destruct (forallb _) eqn: eqforall; discard_case. 
      destruct (dblock_constr _) eqn: eqconstr; discard_case. 
      destruct (nodupb constr_eqb l) eqn: eqnodupb; discard_case. 
      inversion_subst Hb_ext. eapply TBElab; eauto.
      apply Forall_split_conv. apply Forall_DT_forall_is_DT. eauto.
    Qed.
    
    Theorem tbl_elab_complete: forall r r' R R' B,   
      TBlockElab (r, R, B) (r', R', B) -> 
      tblock_elab r R B = Ok (r', R'). 
    Proof. 
      intros * HBext. 
      inversion HBext as [r0 R0 B' l HWfet Hnodup1
                          HForall Hconstr Hnodup2]; subst. 
      unfold tblock_elab. 
      rewrite Hnodup1.
      apply Forall_split_conv in HForall.
      rewrite <- Forall_DT_forall_is_DT in HForall .
      rewrite HForall. rewrite Hconstr.
      rewrite Hnodup2. reflexivity.
    Qed.
    

    Theorem tbl_elab_fail_correct: forall r R B mssg, 
      tblock_elab r R B = Error mssg ->
      (forall r' R', ~TBlockElab (r, R, B) (r', R', B)).
    Proof. 
      intros * Hbe. unfold not. 
      intros * HBext. 
      inversion HBext as [r0 R0 B' l HWfet Hnodup1
                          HForall Hconstr Hnodup2]; subst. 
      unfold tblock_elab in Hbe.
      rewrite Hnodup1 in Hbe. 
      apply Forall_split_conv in HForall.
      rewrite <- Forall_DT_forall_is_DT in HForall.
      rewrite HForall in Hbe. 
      rewrite Hconstr in Hbe.
      rewrite Hnodup2 in Hbe.
      discriminate.
    Qed.   


    Theorem tbl_elab_fail_complete : forall r R B, 
       WFET r R -> 
       (forall r' R', ~TBlockElab (r, R, B) (r', R', B)) -> 
       (exists mssg, tblock_elab r R B = Error mssg).
    Proof. 
      intros * HWfet HBext. 
      unfold tblock_elab.   
      destruct (nodupb _) eqn: eqnodup1.
      + destruct (forallb _) eqn: eqforall. 
        * destruct (dblock_constr _) eqn: eqconstr. 
          - destruct (nodupb constr_eqb l) eqn: eqnodupb. 
            -- assert (contra: 
                TBlockElab (r, R, B)
                (type_env_ext r B, early_binding R B, B)). 
               {eapply TBElab; eauto; apply Forall_split_conv; 
                apply Forall_DT_forall_is_DT; eauto. }
                specialize HBext with 
                (r' := type_env_ext r B) (R' := early_binding R B).
                contradiction.
            -- exists 
              "duplicated constructor is declared in the same block"%string.
               reflexivity.
          - exists 
            "implementation error: invalid type has been declared"%string.
            reflexivity.
        * exists "declaration of invalid type"%string. 
          reflexivity. 
      + exists 
        "duplicated name is declared in the same block"%string.
        reflexivity.
    Qed.                   
                
    


    Definition cdblock := list (Constr * KTp). 

    (* given a constructor env `d`, a name `i` of a declared type   
       and a block of declared constructors `l`, it extends `d` binding 
       each constructor `c` with `(i, t)`, where `t` is the definition 
       of `c` in the block . *)
    Definition cblock_extends (d: constr_env) (i: Ide) (l: cdblock) 
                             : constr_env := 
      fold_right (fun '(c, t) acc => bind acc c (i, t) constr_eqb) d l.
      
           
       
    Lemma lookup_constr_env_ext_cases : forall d c i j l t,
      lookup (cblock_extends d i l) c = Some (j, t) -> 
      lookup d c = Some (j, t) \/ (j = i /\ In (c, t) l).
    Proof. 
      intros * Hlkp.
      generalize dependent d. 
      induction l as [| (c', t') tail]; intros. 
      + simpl in *. left. eauto.
      + simpl in Hlkp. pose proof Hlkp as Hlkp'.  
        unfold lookup, bind in Hlkp.
        destruct (constr_eqb c c') eqn: eqc .
        (* constr_eqb c c' = true *)
        - rewrite <- constr_eqb_eq in eqc;subst. 
          inversion Hlkp; subst.
          right. split; simpl; eauto.
        (* constr_eqb c c' = false *)
        - apply IHtail in Hlkp; eauto. 
          destruct Hlkp as [* | HIn]. 
          * left; eauto.
          * right. split; simpl; destruct HIn; eauto.
    Qed.  


    Lemma In_exists_constr_eqb: 
      forall c t (l: list (Constr * KTp)),  
       In (c, t) l -> 
       existsb (fun p => constr_eqb (fst p) c) l = true.
    Proof. 
      intros * HIn. 
      induction l as [| (c', t') tail]; discard_case.
      simpl in HIn. destruct HIn as [HEq | HIn].
      + inversion_subst HEq. simpl. apply Bool.orb_true_iff.
        left. apply constr_eqb_eq. reflexivity.
      + simpl. apply Bool.orb_true_iff. right. eauto.
    Qed. 
             

    Theorem cblock_extends_preserves_wfec : forall d r R i l, 
      WFEC d r R ->
      (forall c t, 
        In (c, t) l -> 
        last_type_def r c = Some (i, KTVariant l)) ->
      WFEC (cblock_extends d i l) r R. 
    Proof.
      intros * HWfec Hlkp.
      unfold WFEC; split; 
      inversion HWfec as [H0 H1]; eauto.
      intros * Hlkp'. 
      apply lookup_constr_env_ext_cases in Hlkp'.
      destruct Hlkp' as [Hlkp' | Heqin].
      + apply H1; eauto.
      + destruct Heqin as [Heq Hin]; subst.
        unfold tlookup in Hlkp.  
        pose proof Hin as Hin'. 
        apply Hlkp in Hin. exists l; eauto.
    Qed.
 
        
                
    (* given a constructor env `d` and a type declaration block `B` 
       it extends `d` binding every constructor in B through 
       cblock_extends. If 'B' includes a non declarable type, 
       it returns None. *)
    Fixpoint bind_constr_tblock (d: constr_env) (B: tdblock) := 
      match B with 
      |[]                    => Some d 
      |(i, KTVariant l)::B'  => bind_constr_tblock (cblock_extends d i l) B' 
      |_                     => None 
      end.
  
          
    Lemma lookup_bind_constr_dblock_cases : 
      forall d d' B c j t,
        bind_constr_tblock d B = Some d' -> 
        lookup d' c = Some (j, t) -> 
        lookup d c = Some (j, t) \/ 
        (exists i l, j = i /\ In (i, KTVariant l) B /\ In (c, t) l).
    Proof.
      intros * Hbind Hlkp. generalize dependent d.
      induction B as [| (c', t') tail]; intros. 
      + simpl in Hbind; inversion_subst Hbind; left; eauto.
      + pose proof Hbind as Hbind'. 
        simpl in Hbind; destruct t'; discard_case. 
        apply IHtail in Hbind. destruct Hbind as [Hl | Hr]. 
        * apply lookup_constr_env_ext_cases in Hl. 
          destruct Hl as [* | HEqIn]. 
          ** left; eauto.
          ** right. exists c'. exists tags.
             destruct HEqIn. repeat split; simpl; eauto.
        * right. destruct Hr as [i' [l [H1 [H2 H3]]]].
          exists i'. exists l. repeat split; eauto. 
          simpl. right . eauto.
    Qed.     
             



    Lemma last_type_def_correct: 
      forall i cb B c t l r,  
        In (i, KTVariant cb) B -> 
        In (c, t) cb -> 
        nodupb id_eqb (fst (split B)) = true -> 
        dblock_constr B = Some l -> 
        nodupb constr_eqb l = true ->
        last_type_def (type_env_ext r B) c = Some (i, KTVariant cb).
    Proof. 
      intros * HInB HIncb HnodupId Hdblock HnodupC .
      generalize dependent r.
      generalize dependent l.
      induction B as [| (i', t') tail]; discard_case; intros.
      simpl in HnodupId |-*. destruct (split tail). 
      simpl in HnodupId. destruct (find _) eqn: eqfind; discard_case. 
      simpl in HInB; destruct HInB as [HEq | HIntail].
      + inversion_subst HEq. apply In_exists_constr_eqb in HIncb.
        rewrite HIncb. reflexivity.
      + destruct t'; discard_case. destruct (existsb _) eqn: eqex.
        * simpl in Hdblock. rewrite existsb_exists in eqex. 
          destruct (dblock_constr tail) eqn: eqtail; discard_case.
          inversion_subst Hdblock. destruct eqex as [(c0, k) [HIn Heqc]].
           rewrite <- constr_eqb_eq in Heqc; simpl in Heqc; subst. 
            (* we reach a contradiction by the assumptions 
               `In (c, k) tags` and `In (c, t) cb`.
               We can use the correctness lemma for `dblock_constr`
               function. *)
            assert (Hp: In c l2). {
              apply (dblock_constr_correct1 i cb tail c); eauto. 
              eapply In_split_cblock; eauto. 
              } 
            assert (Hp': In c (fst (split tags))) by 
              (eapply In_split_cblock; eauto).
            assert (contra: 
              nodupb constr_eqb (fst (split tags) ++ l2) = false). 
            {eapply In_false_nodupb; eauto. 
             intros. apply Bool.iff_reflect. apply constr_eqb_eq.  }
            rewrite HnodupC in contra. discriminate.
        * simpl in Hdblock. destruct (dblock_constr tail) eqn: eqtail; 
          discard_case. eapply IHtail; eauto.  
          inversion_subst Hdblock; 
          rewrite <- nodupb_eq_NoDup in HnodupC |- *; 
          try (intros; apply Bool.iff_reflect; apply constr_eqb_eq);
          eapply NoDup_app_remove_l; eauto.
    Qed.
                  
      

    (* Theorem tbl_ext_with_constr_correct: forall r r' R R' B d d', 
      TBlockElab (r, R, B) (r', R', B) -> 
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
    Qed.     *)


    Lemma cblock_extends_lkp_correct: forall c t l d i, 
      In (c, t) l -> 
      nodupb constr_eqb (fst (split l)) = true  ->
      lookup (cblock_extends d i l) c = Some (i, t).
    Proof. 
      intros * HIn Hnodupb. 
      induction l as [| (c', t') tail]; discard_case.  
      simpl. unfold lookup, bind. 
      destruct (constr_eqb c c') eqn: eqc. 
      + simpl in HIn. destruct HIn as [Heq | HIn].
        inversion_subst Heq; eauto.  
        simpl in Hnodupb. destruct (split tail) eqn: eqsplit.
        simpl in Hnodupb. destruct (find _) eqn: eqfind; discard_case.  
        apply find_none with (x := c) in eqfind. 
        rewrite eqc in eqfind. discriminate. 
        apply In_split_cblock in HIn. rewrite eqsplit in HIn. eauto. 
      + simpl in HIn. destruct HIn as [Heq | HIn].  
        inversion_subst Heq. rewrite <- constr_eqb_neq in eqc.
        contradiction. 
        simpl in Hnodupb. destruct (split tail) eqn: eqsplit.
        simpl in *. destruct (find _) eqn: eqfind. discard_case.
        eauto.
    Qed.

         
    Lemma cblock_extends_preserves_bindings : 
      forall d c i t l i' , 
        lookup d c  = Some (i, t) -> 
        ~In c (fst (split l)) -> 
        lookup (cblock_extends d i' l) c = Some (i, t).
    Proof. 
      intros * Hlkp HIn. 
      induction l as [| (c', t') tail]; solve_base. 
      simpl in *. unfold lookup, bind. 
      destruct (split _) eqn: eqsplit. 
      simpl in *. apply Decidable.not_or in HIn. 
      destruct HIn as [HNeq *]. 
      destruct (constr_eqb c c') eqn: eqc; solve_base.
      rewrite <- constr_eqb_eq in eqc. 
      symmetry in eqc. contradiction.
    Qed.    

    
    Lemma cblock_extends_preserves_bindings_inv : 
      forall d i' l c i t, 
        lookup (cblock_extends d i' l) c = Some (i, t) -> 
        ~In c (fst (split l)) -> 
        lookup d c = Some (i, t).
    Proof. 
      intros * Hlkp HnIn. 
      generalize dependent d. 
      induction l as [| (c', t') tail]; intros; solve_base. 
      simpl in *. destruct (split tail). 
      unfold lookup, bind in Hlkp.
      simpl in HnIn. apply Decidable.not_or in HnIn.
      destruct HnIn as [HnInl HnInr].
      destruct (constr_eqb c c') eqn: eqc. 
      * rewrite <- constr_eqb_eq in eqc; subst.  
        contradiction.
      * apply IHtail; eauto.
    Qed. 


    Lemma bind_constr_tblock_preserves_bindings: 
      forall d d' i l c t B, 
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
      induction B as [| (i', t') tail]; intros. 
      + inversion_subst Hbct; eauto.
      + simpl in Hdb. destruct t'; discard_case. 
        destruct (dblock_constr tail) eqn: eqtail; discard_case.
        inversion_subst Hdb. apply not_In_app in HnIn.
        simpl in Hbct. eapply IHtail with 
         (d := cblock_extends d i' tags); eauto; 
        destruct HnIn; eauto.  
        apply cblock_extends_preserves_bindings; eauto.
    Qed.  
        

    Lemma bind_constr_tblock_preserves_bindings_inv: 
      forall d' d c i t B l,  
        bind_constr_tblock d B = Some d' -> 
        dblock_constr B = Some l -> 
        ~In c l -> 
        lookup d' c = Some (i, t) ->
        lookup d c = Some (i, t).
    Proof.
      intros * Hbd Hdb HnIn Hlkp. 
      generalize dependent l. 
      generalize dependent d. 
      induction B as [| (i', t') tail]; intros. 
      + simpl in *. inversion_subst Hbd; eauto. 
      + simpl in *. destruct t'; discard_case. 
        destruct (dblock_constr tail) eqn: eqtail; 
        discard_case; inversion_subst Hdb. 
        apply not_In_app in HnIn. 
        destruct HnIn as [HnIn1 HnIn2]. 
        assert (H: lookup (cblock_extends d i' tags) c = Some (i, t))
         by (eapply IHtail ; eauto).
        eapply cblock_extends_preserves_bindings_inv; eauto.
    Qed.


    Lemma exists_cdblock_In_tdblock : 
      forall d' d B l c i t, 
        bind_constr_tblock d B = Some d' ->
        dblock_constr B = Some l -> 
        nodupb constr_eqb l = true -> 
        In c l -> 
        lookup d' c = Some (i, t) -> 
        exists l', In (i, KTVariant l') B /\ In (c, t) l'.
    Proof. 
      intros * Hbctb Hdb Hndpb HIn Hlkp. 
      generalize dependent l. 
      generalize dependent d.
      induction B as [| (i', t') tail]; intros. 
      + simpl in *; inversion Hdb; subst; contradiction.
      + simpl in *. destruct t'; discard_case. 
        destruct (dblock_constr tail) eqn: eqtail; discard_case.
        inversion_subst Hdb. apply in_app_or in HIn. 
        destruct HIn as [HInl | HInr].
        * apply split_In_cblock in HInl. destruct HInl as [t' HInl].  
          pose proof HInl as HInl'. apply In_split_cblock in HInl.
          assert (Haux1: 
           lookup (cblock_extends d i' tags) c = Some (i', t')). 
          {   
              apply cblock_extends_lkp_correct; eauto.
              eapply nodupb_remove_r; eauto.
              eapply constr_refl. 
          }
          assert (HnIn : ~In c l0) by (
            eapply nodupb_In_false; 
            eauto; apply constr_refl
          ).
          assert (Hlkpc: lookup d' c = Some (i', t')) by (
              eapply bind_constr_tblock_preserves_bindings; eauto
          ).  
          rewrite Hlkpc in Hlkp. inversion_subst Hlkp.
          exists tags; split; eauto.
        * assert (HIn: 
           exists l', In (i, KTVariant l') tail /\ In (c, t) l'). 
          {eapply IHtail; eauto. 
           eapply nodupb_remove_l; eauto. 
           eapply constr_refl. } 
           destruct HIn as [l' [*]]. 
           exists l'. split; try right; eauto.
    Qed.


    
    Lemma type_env_ext_preserves_ltd : 
      forall r c i l B l', 
        dblock_constr B = Some l -> 
        ~In c l -> 
        last_type_def r c = Some (i, KTVariant l') ->
        last_type_def (type_env_ext r B) c = Some (i, KTVariant l').
    Proof.
      intros * Hdb HnIn Hltd. 
      generalize dependent l.
      generalize dependent r. 
      induction B as [| (i', t') tail]; intros; solve_base. 
      simpl in *. destruct t'; discard_case. 
      destruct (dblock_constr tail) eqn: eqdb; discard_case. 
      inversion_subst Hdb. apply not_In_app in HnIn. 
      destruct HnIn as [HnIn1 HnIn2]. 
      destruct (existsb _) eqn: eqx. 
      * apply existsb_exists in eqx. 
        destruct eqx as [(c', t) [HIn Heq]]. 
        rewrite <- constr_eqb_eq in Heq; subst. 
        apply In_split_cblock in HIn. contradiction.
      * eapply IHtail; eauto.
    Qed.   

             
    Theorem bind_constr_tblock_preserves_wfec: 
      forall r r' R R' B d d', 
        TBlockElab (r, R, B) (r', R', B) -> 
        WFEC d r R ->
        bind_constr_tblock d B = Some d' -> 
        WFEC d' r' R'. 
    Proof. 
      intros * HBEl HWfec Hbct. 
      unfold WFEC; split; 
      inversion HBEl as [r0 R0 B' l HWfet Hnodup1
                          HForall Hconstr Hnodup2]; subst; eauto;
      inversion HWfec as [HWfet' Hlkp].
      + eapply TBlockElab_preserves_wfet; eauto. 
      + intros i t c Hlkp'. destruct B as [| (i', t') tail]. 
        * simpl in *; inversion_subst Hbct; eauto.
        * simpl in Hbct. destruct t'; discard_case; simpl in *. 
          destruct (dblock_constr _) eqn: Hdb; discard_case.
          destruct (existsb _) eqn: eqfind. 
          - apply existsb_true_In_cblock in eqfind. 
            destruct eqfind as [t' HIn]. inversion_subst Hconstr.    
            pose proof HIn as HInt'.
            apply In_split_cblock in HIn.
            assert (Haux1: 
             lookup (cblock_extends d i' tags) c = Some (i', t')). 
            {   
              rewrite <- nodupb_eq_NoDup in Hnodup2;
              intros; try eapply constr_refl; 
              apply NoDup_app_remove_r in Hnodup2;
              eapply nodupb_eq_NoDup in Hnodup2;
              intros; try eapply constr_refl;
              apply cblock_extends_lkp_correct; eauto.
            }
            assert (HnIn : ~In c l0) 
             by (eapply nodupb_In_false; 
                 eauto; apply constr_refl).
            assert (Hlkpc: lookup d' c = Some (i', t')) by
            (eapply bind_constr_tblock_preserves_bindings; eauto). 
            rewrite Hlkpc in Hlkp'.
            inversion_subst Hlkp' . exists tags; split; eauto.
          
          - destruct (split tail) eqn: eqtail.
            simpl in Hnodup1. destruct (find _) eqn: eqfnd; 
            discard_case. inversion_subst Hconstr.

            assert(Hnodupb_l0: nodupb constr_eqb l0 = true ) by 
             (eapply nodupb_remove_l; eauto; 
              eapply constr_refl ).

            destruct (find (fun x => constr_eqb x c) l0) 
            eqn: eqfind'.
            -- apply find_some in eqfind'. 
               destruct eqfind' as [HInl0 Heqc].
               rewrite <- constr_eqb_eq in Heqc; subst.
               assert (H: exists l', 
                 In (i, KTVariant l') tail /\ In (c, t) l') by 
               (eapply exists_cdblock_In_tdblock; eauto). 
              destruct H as [l' [*]]. exists l'. 
              split; eauto. eapply last_type_def_correct; 
              try rewrite eqtail; eauto.
            -- apply find_none_not_In in eqfind'; 
               try eapply constr_refl.  
               assert (Hp1: 
                lookup (cblock_extends d i' tags) c = Some (i, t)) 
                by(eapply 
                 bind_constr_tblock_preserves_bindings_inv; eauto).
               assert (Hp2: lookup d c = Some (i, t)). 
               {eapply cblock_extends_preserves_bindings_inv; 
                eauto. unfold not. intro contra . 
                apply split_In_cblock in contra. 
                destruct contra as [t']. 
                apply existsb_false_not_In_cblock with (t := t') 
                in eqfind. contradiction. }
               apply Hlkp in Hp2. destruct Hp2 as [l' [Hltd HIn]].
               exists l'. split; eauto. 
               eapply type_env_ext_preserves_ltd; eauto.
    Qed.         
               

               
(*         
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
            *)
    
    
    (* specification of static elaboration *)
    Inductive Elab : KExpr -> tenv -> register -> constr_env -> LExpr -> Prop :=   
     |Elab_Var      : forall r R d i, 
                       WFET r R -> 
                       WFEC d r R -> 
                       Elab (KVar i) r R d (LVar i) 
     |Elab_Lit      : forall r R d x, 
                       WFET r R -> 
                       WFEC d r R -> 
                       Elab (KLit x) r R d (LLit x)
     |Elab_Op       : forall r R d l l' op,  
                       WFET r R -> 
                       WFEC d r R -> 
                       Forall2 (fun e le => Elab e r R d le) l l' -> 
                       Elab (KOp op l) r R d (LOp op l')
     |Elab_Lam      : forall r R d p e e', 
                       WFET r R -> 
                       WFEC d r R -> 
                       WFP d r R p  -> 
                       Elab e r R d e' -> 
                       Elab (KLam p e) r R d (LLam p e')  
     |Elab_App      : forall r R d e1 e1' e2 e2', 
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
     |Elab_Pair     : forall r R d e1 e1' e2 e2', 
                       WFET r R -> 
                       WFEC d r R -> 
                       Elab e1 r R d e1' -> 
                       Elab e2 r R d e2' -> 
                       Elab (KPair e1 e2) r R d (LPair e1' e2') 
     |Elab_Cons     : forall r R d  e1 e1' e2 e2' , 
                       WFET r R -> 
                       WFEC d r R -> 
                       Elab e1 r R d e1' -> 
                       Elab e2 r R d e2' -> 
                       Elab (KCons e1 e2) r R d (LCons e1' e2')
     |Elab_Variant : forall r R d c (inf: Ide * KTp) e e' , 
                       WFET r R -> 
                       WFEC d r R -> 
                       lookup d c = Some inf -> 
                       Elab e r R d e' -> 
                       Elab (KVariant c e) r R d (LVariant c inf e')
     |Elab_Fix      : forall r R d e e' name, 
                       WFET r R -> 
                       WFEC d r R -> 
                       Elab e r R d e' ->  
                       Elab (KFix name e) r R d (LFix name e')  
     |Elab_DefType  : forall r R d r' R' B d' e e', 
                       WFET r R -> 
                       WFEC d r R -> 
                       TBlockElab (r, R, B) (r', R', B) ->
                       bind_constr_tblock d B = Some d' ->  
                       Elab e r' R' d' e'  ->
                       Elab (KDefType B e) r R d e'    
     |Elab_Match    : forall r R d e e' l l', 
                        WFET r R -> 
                        WFEC d r R -> 
                        Elab e r R d e' -> 
                        Forall2 (fun p p' => 
                          WFP d r R (fst p) /\ 
                          fst p = fst p' /\ 
                          Elab (snd p) r R d (snd p')) l l' -> 
                        Elab (KMatch e l) r R d (LMatch e' l') 
     |Elab_Error    : forall r R d m, 
                        WFET r R ->   
                        WFEC d r R -> 
                        Elab (KError m) r R d (LError m) .

  

    Section Elab_ind'.  
      
      Variable Q : 
       KExpr -> tenv -> register -> constr_env -> LExpr -> Prop .

      Hypothesis Elab_Var_case : forall r R d i,
                                  WFET r R -> 
                                  WFEC d r R ->  
                                  Q (KVar i) r R d (LVar i).
      Hypothesis Elab_Lit_case : forall r R d x,
                                  WFET r R -> 
                                  WFEC d r R -> 
                                  Q (KLit x) r R d (LLit x).
      Hypothesis Elab_Op_case : forall r R d l l' op,
                                  WFET r R -> 
                                  WFEC d r R ->   
                                  Forall2 (fun ke le => 
                                    Q ke r R d le) l l' -> 
                                  Q (KOp op l) r R d (LOp op l').
      Hypothesis Elab_Lam_case : forall r R d p e e', 
                                  WFET r R -> 
                                  WFEC d r R -> 
                                  WFP d r R p  -> 
                                  Q e r R d e' -> 
                                  Q (KLam p e) r R d (LLam p e').
      Hypothesis Elab_App_case : forall r R d e1 e1' e2 e2', 
                                  WFET r R ->
                                  WFEC d r R -> 
                                  Q e1 r R d e1' -> 
                                  Q e2 r R d e2' -> 
                                  Q (KApp e1 e2) r R d (LApp e1' e2').
      Hypothesis Elab_Unit_case : forall r R d, 
                                   WFET r R -> 
                                   WFEC d r R -> 
                                   Q KUnit r R d LUnit .
      Hypothesis Elab_Nil_case : forall r R d, 
                                  WFET r R -> 
                                  WFEC d r R -> 
                                  Q KNil r R d LNil. 
      Hypothesis Elab_Pair_case : forall r R d e1 e1' e2 e2', 
                                   WFET r R -> 
                                   WFEC d r R -> 
                                   Q e1 r R d e1' -> 
                                   Q e2 r R d e2' -> 
                                   Q (KPair e1 e2) r R d (LPair e1' e2').
      Hypothesis Elab_Cons_case : forall r R d e1 e1' e2 e2', 
                                   WFET r R -> 
                                   WFEC d r R -> 
                                   Q e1 r R d e1' -> 
                                   Q e2 r R d e2' -> 
                                   Q (KCons e1 e2) r R d (LCons e1' e2').
      Hypothesis Elab_Variant_case : forall r R d c inf e e', 
                                      WFET r R -> 
                                      WFEC d r R -> 
                                      lookup d c = Some inf -> 
                                      Q e r R d e' -> 
                                      Q (KVariant c e) r R d 
                                        (LVariant c inf e').
      Hypothesis Elab_Fix_case : forall r R d e e' name,
                                  WFET r R -> 
                                  WFEC d r R -> 
                                  Q e r R d e' -> 
                                  Q (KFix name e) r R d (LFix name e').
      Hypothesis Elab_DefType_case : forall r R d B r' R' d' e e', 
                                      WFET r R ->  
                                      WFEC d r R -> 
                                      TBlockElab (r, R, B) (r', R', B) ->
                                      bind_constr_tblock d B = Some d' ->  
                                      Q e r' R' d' e'  ->
                                      Q (KDefType B e) r R d e'.
      Hypothesis Elab_Match_case : forall r R d e e' l l', 
                                    WFET r R -> 
                                    WFEC d r R -> 
                                    Q e r R d e' -> 
                                    Forall2 (fun p p' => 
                                      WFP d r R (fst p) /\ 
                                      fst p = fst p' /\ 
                                      Q (snd p) r R d (snd p')) l l' -> 
                                    Q (KMatch e l) r R d (LMatch e' l').
      Hypothesis Elab_Error_case : forall r R d mssg,
                                    WFET r R -> 
                                    WFEC d r R -> 
                                    Q (KError mssg) r R d (LError mssg).

    

      Fixpoint Elab_ind' e r R d e' (H: Elab e r R d e') 
                         : Q e r R d e' := 
        match H with 
        |Elab_Var Hwfet Hwfec  => Elab_Var_case Hwfet Hwfec 
        |Elab_Lit Hwfet Hwfec  => Elab_Lit_case Hwfet Hwfec 
        |Elab_Op Hwfet Hwfec HFall => Elab_Op_case Hwfet Hwfec  
          ((fix elab_ind_op l l' (H: Forall2 (fun ke le => 
                                  Elab ke _ _ _ le) l l')
                           : Forall2 (fun ke le => 
                                  Q ke _ _ _ le) l l' := 
            match H with 
            |Forall2_nil _ => Forall2_nil _ 
            |Forall2_cons _ _ H HFall => 
               Forall2_cons _ _ (Elab_ind' H) (elab_ind_op _ _ HFall) end) 
          _ _ HFall)
        |Elab_Lam Hwfet Hwfec Hwfp H  => 
          Elab_Lam_case Hwfet Hwfec Hwfp (Elab_ind' H)   
        |Elab_App Hwfet Hwfec H1 H2   => 
          Elab_App_case Hwfet Hwfec (Elab_ind' H1) (Elab_ind' H2) 
        |Elab_Unit Hwfet Hwfec => Elab_Unit_case Hwfet Hwfec
        |Elab_Nil Hwfet Hwfec => Elab_Nil_case Hwfet Hwfec
        |Elab_Pair Hwfet Hwfec H1 H2 =>
          Elab_Pair_case Hwfet Hwfec (Elab_ind' H1) (Elab_ind' H2)
        |Elab_Cons Hwfet Hwfec H1 H2 =>
          Elab_Cons_case Hwfet Hwfec (Elab_ind' H1) (Elab_ind' H2)
        |Elab_Variant Hwfet Hwfec Hlookup H =>
          Elab_Variant_case Hwfet Hwfec Hlookup (Elab_ind' H)
        |Elab_Fix Hwfet Hwfec H =>
          Elab_Fix_case Hwfet Hwfec (Elab_ind' H)
        |Elab_DefType Hwfet Hwfec HTBlock Hbind H =>
          Elab_DefType_case Hwfet Hwfec HTBlock Hbind (Elab_ind' H)
        |Elab_Match Hwfet Hwfec H HFall =>
          Elab_Match_case Hwfet Hwfec (Elab_ind' H)
           ((fix elab_ind_match l l' (H: 
               Forall2 (fun p p' => WFP _ _ _ (fst p) /\ 
                                    fst p = fst p' /\ 
                                    Elab (snd p) _ _ _ (snd p')) l l')
               : Forall2 (fun p p' => WFP _ _ _ (fst p) /\ 
                                      fst p = fst p' /\ 
                                      Q (snd p) _ _ _ (snd p')) l l' := 
              match H with 
              |Forall2_nil _ => Forall2_nil _ 
              |Forall2_cons _ _ Hconj HFall  => 
                  match Hconj with 
                  |conj A (conj B C) =>  
                    Forall2_cons _ _ 
                      (conj A (conj B (Elab_ind' C))) 
                      (elab_ind_match _ _ HFall) 
                  end 
              end) _ _ HFall)
        |Elab_Error Hwfet Hwfec => Elab_Error_case Hwfet Hwfec
      end .  

    End Elab_ind'.


    (* the `inf` annotation in the new node `LVariant c inf e` 
       contains the name of the last declared type having `c`
       among its constructors, together with the constructor 
       argument. *)
    Corollary Elab_labels_constr_with_ltd:
      forall r R d c i t,
         WFET r R ->  
         WFEC d r R -> 
         lookup d c = Some (i, t) -> 
         exists (l: list (Constr * KTp)), 
           last_type_def r c = Some (i, KTVariant l) /\
           In (c, t) l .
    Proof. 
      intros * Hwfet Hwfec Hlkp. 
      unfold WFEC in Hwfec; destruct Hwfec; eauto.
    Qed.  

                                             
    (* Each KExpr term elaborates to at most one LExpr term *)
     Theorem Elab_deterministic: 
       forall e e' e'' r R d, 
         Elab e r R d e' -> 
         Elab e r R d e'' -> 
         e' = e''. 
     Proof. 
       intros * HEl1 HEl2. 
       induction HEl1; inversion_subst HEl2; 
       try constructor.
       +         
                        
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
      |KDefType B e => match tblock_elab r R B with 
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
