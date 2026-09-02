Require Import Lists.List ids primitives kernel_syntax.
Import ListNotations.

Set Implicit Arguments.

Section TEnv. 

    Context (I: IDS). 
    Context (P: PRIM_DATA). 
 
    Fixpoint assoc_opt {X Y: Type} (e: list (X * Y)) (i: X) (eq: X -> X -> bool) : option Y := 
      match e with 
      |(i', t)::l => if eq i i' then Some t else assoc_opt l i eq 
      |_          => None 
      end.


    Local Notation " 'Ide' " := (@Ide I).
    Local Notation " 'Constr' " := (@Constr I).
    Local Notation " 'KTp' " := (@KTp I P).
    Local Notation " 'id_eqb' " := (@id_eqb I) .
    Local Notation " 'constr_eqb' " := (@constr_eqb I).

    Definition tenv := list (Ide * KTp). 
    Definition empty_tenv : tenv := [].
    Definition tlookup (e: tenv) (i: Ide) : option KTp := assoc_opt e i id_eqb.   
    Definition tdom (e: tenv) (i: Ide) : Prop := exists y, tlookup e i = Some y. 
    Definition timm (e: tenv) (y: KTp) : Prop := exists i, tlookup e i = Some y.   
    Definition tincludes (e: tenv) (i:Ide) : bool := 
        match tlookup e i with None => false | _ => true end. 
    Definition tbind (e: tenv) (i: Ide) (t: KTp) : tenv := (i, t)::e.    
    
    
    (* given a well-formed tenv `e` and a constructor `c` returns the option
       pair Some (i, t), if it exists, where `i` is the name of the most recent 
       declared type in `e` declaring `c` with type `t`. If `l` contains a type 
       being not a variant the input environment will be considered automatically 
       ill-formed and rejected returning None. *)
    Fixpoint last_constr_def (e: tenv) (c: Constr) :=  
      match e with  
      |(i, KTVariant l)::e'  => match assoc_opt l c constr_eqb with 
                                |Some t => Some (i, t)
                                |None   => last_constr_def e' c 
                                end                            
      |_                      => None 
      end.
    
    (* given a well-formed tenv `e` and a constructor `c` returns the option
       pair Some (i, t), if it exists, where `i` is the name of `t` and `t` is
       the most recent declared type in `l` having `c` among its constructors .
       If `l` contains a type being not a variant the input environment will be 
       considered automatically ill-formed and rejected returning None. *)
    Fixpoint last_type_def (e: tenv) (c: Constr) := 
      match e with 
      |(i, KTVariant l)::e' => if existsb (fun p => constr_eqb (fst p) c) l 
                                then Some (i, KTVariant l)
                               else last_type_def e' c 
      |_                    => None 
      end. 

    
   

    
    Lemma tlookup_empty: forall i, 
      tlookup (empty_tenv) i = None.
    Proof. 
      intro. 
      unfold tlookup. 
      unfold empty_tenv. 
      reflexivity.
    Qed. 
    

    Lemma tbind_extends: forall e i x , 
      tlookup (tbind e i x) i = Some x.
    Proof. 
      intros .
      unfold tlookup.
      unfold tbind. 
      simpl.
      destruct (id_eqb i i) eqn: eq. 
      reflexivity.
      rewrite <- id_eqb_neq in eq.
      contradiction.
    Qed.
    
    
    Lemma tbind_preserves_old_env: forall e i x, 
      tlookup e i = Some x -> 
        forall i' x',
            i <> i' -> 
            tlookup (tbind e i' x') i = Some x. 
    Proof. 
      intros * Htlkp * Hneq.
      unfold tlookup, tbind.
      simpl.
      rewrite id_eqb_neq in Hneq.
      rewrite Hneq.
      unfold tlookup in Htlkp.
      eauto. 
    Qed. 
    

    (* if an identifier has been bound in the env `e` then 
        it will be bound yet in any extension of `e`. *)
    Corollary tbind_preserves_bound_id's: forall e i x, 
      tlookup e i = Some x ->
        forall i' x', 
          exists x'', tlookup (tbind e i' x') i = Some x''. 
    Proof. 
      intros * Hlkp * .
      unfold tlookup, tbind.
      simpl. 
      destruct (id_eqb i i') eqn: eqi.  
      - exists x'. eauto.
      - exists x. unfold tlookup in Hlkp. eauto.
    Qed. 



End TEnv.