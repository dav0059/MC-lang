Require Import ids primitives kernel_syntax type_env env type_theory. 
Require Import Lists.List. 
Import ListNotations. 

Set Implicit Arguments. 
Set Contextual Implicit. 

Section PATTERN_THEORY. 
    
    Context (I: IDS). 
    Context (P: PRIM_DATA). 
    
    Local Notation " 'Ide' " := (@Ide I). 
    Local Notation " 'KPat' " := (@KPat I P). 
    Local Notation " 'Constr' " := (@Constr I).
    Local Notation " 'KTp' " := (@KTp I P).
    Local Notation " 'tenv' " := (@tenv I P).
    Local Notation " 'register' " := (@register I).

    Ltac solve_base := 
      try simpl in *; try constructor; eauto.


    (* function for computing the list of pattern variables *)
     Fixpoint pv (p: KPat) : list Ide := 
      match p with 
      |KPVar x         => [x]
      |KPLit _         => [] 
      |KPAny           => []
      |KPAs p i        => i::(pv p)
      |KPUnit          => []
      |KPNil           => []
      |KPPair p1 p2    => pv p1 ++ pv p2 
      |KPCons p1 p2    => pv p1 ++ pv p2 
      |KPVariant c p   => pv p 
      end.  

      (* optimized version of pv *)
      Fixpoint pat_vars_aux (p: KPat) (acc: list Ide): list Ide := 
        match p with 
        |KPVar x  => x::acc
        |KPLit _  => acc 
        |KPAny    => acc 
        |KPAs p i => i::pat_vars_aux p acc
        |KPUnit   => acc 
        |KPNil    => acc 
        |KPPair p1 p2 => pat_vars_aux p1 (pat_vars_aux p2 acc)
        |KPCons p1 p2 => pat_vars_aux p1 (pat_vars_aux p2 acc)
        |KPVariant c p => pat_vars_aux p acc 
        end.

      Definition pat_vars p := pat_vars_aux p []. 


      (* we can prove that the list of variables 
         produced by pv and that produced by pat_vars 
         are equal. This allows to adopt 
         the optimized version for implementations 
         while maintaining pv as cleaner functional 
         specification. *)

      Theorem pat_vars_aux_eq_pv : 
        forall p acc, 
          pat_vars_aux p acc = pv p ++ acc.
      Proof. 
        intros. generalize dependent acc. 
        induction p; intros; eauto.
        (* KPas p i *)
        + simpl. destruct IHp with (acc := acc).
          eauto.
        (* KPPair p1 p2 *)
        + simpl. specialize IHp2 with (acc := acc).
          specialize IHp1 with (acc := pv p2 ++ acc).
          rewrite IHp2, IHp1, app_assoc. eauto.
        (* KPCons p1 p2 *)
        + simpl. specialize IHp2 with (acc := acc).
          specialize IHp1 with (acc := pv p2 ++ acc).
          rewrite IHp2, IHp1, app_assoc. eauto.
      Qed.

      Corollary pat_vars_eq_pv : 
        forall (p: KPat), pat_vars p = pv p.
      Proof. 
        intros; unfold pat_vars. rewrite <- app_nil_r.
        eapply pat_vars_aux_eq_pv. 
      Qed.



    Definition constr_env := env Constr (Ide * KTp). 

    (* NOTE: this definition doesn't require the admissibility 
             of the last type declared having c among its constructors. 
             The reason is that in general we don't know what is the 
             type environment and the names register to refer to for 
             proving the well-formedness of the retrieved type. *)
    Definition WFEC (d: constr_env) (r: tenv) (R: register) :=
      WFET r R /\  
      forall i t c,
        lookup d c = Some (i, t) -> 
        exists l, last_type_def r c = Some (i, KTVariant l) /\ 
                  In (c, t) l.
    
        

      (* decides if all constructors in p are reachable in 
         the constr_env d *)
      Fixpoint all_constrs_knows (d: constr_env) (p: KPat) := 
        match p with 
        |KPVar _   => true 
        |KPLit _   => true 
        |KPAny     => true
        |KPAs p i  => all_constrs_knows d p 
        |KPUnit    => true 
        |KPNil     => true 
        |KPPair p1 p2 => all_constrs_knows d p1 && 
                         all_constrs_knows d p2 
        |KPCons p1 p2 => all_constrs_knows d p1 && 
                         all_constrs_knows d p2
        |KPVariant c p => includes d c && 
                          all_constrs_knows d p  
        end.


      (* collect all pattern constructors in a list *)
      Fixpoint pat_constrs (p: KPat) := 
        match p with 
        |KPVar x         => []
        |KPLit _         => [] 
        |KPAny           => []
        |KPAs p i        => pat_constrs p
        |KPUnit          => []
        |KPNil           => []
        |KPPair p1 p2    => pat_constrs p1 ++ 
                            pat_constrs p2 
        |KPCons p1 p2    => pat_constrs p1 ++ 
                            pat_constrs p2 
        |KPVariant c p   => c::pat_constrs p 
        end.



      Theorem all_pat_constrs_are_known: 
        forall d p, 
          (forall c, In c (pat_constrs p) -> 
                     includes d c = true) <-> 
          all_constrs_knows d p = true.
      Proof. 
        intros *. split. 
        + intros HIn. induction p; solve_base.
          (* KPPair p1 p2 *)
          * rewrite Bool.andb_true_iff. split. 
            ** eapply IHp1. intros * HIn1.
               apply or_introl with 
               (B := In c (pat_constrs p2)) in HIn1.
               apply in_or_app in HIn1. apply HIn. eauto.
            ** eapply IHp2. intros * HIn2.
               apply or_intror with 
               (A := In c (pat_constrs p1)) in HIn2.
               apply in_or_app in HIn2. apply HIn. eauto.
          (* KPCons p1 p2 *)
          * rewrite Bool.andb_true_iff. split. 
            ** eapply IHp1. intros * HIn1.
               apply or_introl with 
               (B := In c (pat_constrs p2)) in HIn1.
               apply in_or_app in HIn1. apply HIn. eauto.
            ** eapply IHp2. intros * HIn2.
               apply or_intror with 
               (A := In c (pat_constrs p1)) in HIn2.
               apply in_or_app in HIn2. apply HIn. eauto.
          (* KPVariant c p *)
          * rewrite Bool.andb_true_iff; split.
            ** eapply HIn. left; eauto. 
            ** eapply IHp; intros * HInc.
               apply or_intror with (A := c = c0) in HInc.
               apply HIn; eauto.
        + intros HIn * HInc. induction p; solve_base; 
          try rewrite Bool.andb_true_iff in HIn; 
          try rewrite in_app_iff in HInc; 
          destruct HInc; destruct HIn; subst; eauto.
      Qed.

        
    (* functional specification for Well-formed patterns *)
      Definition is_WFP d p := 
        nodupb (id_eqb I) (pat_vars p) && all_constrs_knows d p.  
           
      

End PATTERN_THEORY.

