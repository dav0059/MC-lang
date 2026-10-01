Require Import Lists.List. 
Import ListNotations. 


Set Implicit Arguments.  
Set Contextual Implicit. 

Section RESULT. 
    Variable A E B: Type. 

    Inductive result A E : Type := 
    |Ok (_ : A)
    |Error (_ : E).

     Definition ok (a: A) : result A E := Ok a. 
     Definition error (e: E) : result A E := Error e.
      
     Definition bind (a: result A E) (f: A -> result B E) := 
      match a with 
      |Ok a    => f a 
      |Error e => Error e 
      end. 
      
    
     Definition join (a: result (result A E) E) := 
      match a with 
      |Ok a    => a 
      |Error e => Error e  
      end.

     Definition product (a: result A E) (b: result B E) :=
      match a with 
      |Error e  => Error e 
      |Ok a     => match b with 
                   |Error e  => Error e 
                   |Ok b     => Ok(a, b)
                   end 
      end.

     Definition is_ok (a: result A E) := 
      match a with 
      |Ok a  => true 
      |_     => false 
      end. 
      
     Definition is_error (a: result A E) := 
      match a with 
      |Error e  => true 
      |_        => false 
      end. 

     Lemma is_error_correct : forall x, 
       is_error x = true -> (exists a, x = Error a).
     Proof. 
      intros * Herr *. 
      destruct x; simpl; try discriminate.
      exists e; reflexivity.
     Qed.
      
      
     Definition get_ok (a: result A E) (def: A) := 
      match a with 
      |Ok a  => a 
      |_     => def
     end.
     
     
     Lemma get_ok_correct : forall x def,
       is_error x = false -> x = Ok (get_ok x def).
     Proof.
      intros * Herr. 
      destruct x. 
      + eauto. 
      + simpl in *; discriminate.
     Qed.     

End RESULT.

Notation " a '>>=' f" := (bind a f) (at level 50, left associativity).

 