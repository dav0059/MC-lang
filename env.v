Require Import Bool. 


 Set Implicit Arguments. 
 
  Section Env. 

    Variable X Y: Type. 

    Definition env (X Y: Type) : Type := X -> option Y. 
    Definition empty_env : env X Y := fun _ => None.
    Definition lookup (e: env X Y) (i: X) : option Y := e i.
    Definition dom (e: env X Y) (i: X) : Prop := exists y, lookup e i = Some y. 
    Definition imm (e: env X Y) (y: Y) : Prop := exists i, lookup e i = Some y.   
    Definition includes (e: env X Y) (i :X) : bool := 
      match lookup e i with None => false | _ => true end. 
    Definition bind (e: env X Y) (i: X) (x: Y) (eqb: X -> X -> bool)  : env X Y := 
        fun j => if eqb j i then Some x else lookup e j. 
        

    Lemma lookup_empty: forall  i, 
      lookup (empty_env) i = None.
    Proof. 
      intro. 
      unfold lookup. 
      unfold empty_env. 
      reflexivity.
    Qed. 
    

    Lemma bind_extends: forall e i x eqb, 
      (forall x y, Bool.reflect (x = y) (eqb x y)) -> 
      lookup (bind e i x eqb) i = Some x.
    Proof. 
      intros * Hrefl.
      unfold lookup.
      unfold bind.
      apply (Bool.reflect_iff (i = i) (eqb i i)) in Hrefl. 
      destruct (eqb i i) eqn: eq. 
      reflexivity.
      assert (H : i = i) by reflexivity. 
      apply Hrefl in H; discriminate.
    Qed.
    
    

    Lemma bind_preserves_old_env: forall e i x eqb, 
      (forall x y, Bool.reflect (x = y) (eqb x y)) ->
      lookup e i = Some x -> 
        forall i' x',
            i <> i' -> 
            lookup (bind e i' x' eqb) i = Some x. 
    Proof. 
      intros * Hrefl Hlkp * Hneq.
      unfold lookup.
      unfold bind. 
      apply (Bool.reflect_iff (i = i') (eqb i i')) in Hrefl.
      destruct (eqb i i') eqn: eqid. 
      * assert (H: true = true) by reflexivity.
        apply Hrefl in H; contradiction. 
      * assumption. 
    Qed. 
    

    (* if an identifier has been bound in the env e then 
        it will be bound yet in any extension of e. *)
    Corollary bind_preserves_bound_id's: forall e i x eqb,
      (forall x y, Bool.reflect (x = y) (eqb x y)) -> 
      lookup e i = Some x ->
        forall i' x', 
          exists x'', lookup (bind e i' x' eqb) i = Some x''. 
    Proof. 
      intros * Hrefl Hlkp * .
      unfold lookup. 
      apply (Bool.reflect_iff (i = i') (eqb i i')) in Hrefl.
      destruct (eqb i i') eqn: eqi.  
      - exists x'. 
        unfold bind. 
        rewrite eqi. 
        reflexivity. 
      - exists x.
        unfold bind.
        rewrite eqi.
        assumption. 
    Qed. 
     
  End Env.

  


 

 
    
     