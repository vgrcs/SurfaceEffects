Require Import Definitions.Types.
Require Import Definitions.Values.
Require Import Definitions.Regions.


Definition find_type_ext_stores_def  := 
   forall stty stty' l (t' : tau),
      ST.find l stty = Some t' ->
      ST.find l stty' = Some t' -> 
      ST.find l stty =  ST.find l stty'.

Lemma find_type_ext_stores: find_type_ext_stores_def.  
Proof.
  intros stty stty' l t' H1 H2.
  rewrite <- H1 in H2.
  symmetry in H2.
  assumption.
Qed.


Definition get_store_typing_val {A B:Type} (p : Sigma * A * B) : Sigma   
  := fst (fst p).

Definition get_store_typing_env {A B C:Type} (p : Sigma * A * B * C) : Sigma   
  := fst (fst (fst p)).

Definition mk_TcVal_ext_store_ty (p : Sigma * Val * tau) (stty' : Sigma)
  := TcVal (stty', snd (fst p), snd p).

Definition mk_TcEnv_ext_store_ty (p : Sigma * Rho * Env * Gamma) (stty' : Sigma)
  := TcEnv (stty', snd (fst (fst p)), snd (fst p), snd p).

Lemma ext_stores__exp__bt__aux:
  (forall p, TcExp p ->
             match p with (ctxt, rgns, e, t, eff) => 
                TcExp (ctxt, rgns, e, t, eff)
             end)
    /\
  (forall p, BackTriangle p ->
             match p with (ctxt, rgns, rho, ec, ee) => 
                BackTriangle (ctxt, rgns, rho, ec, ee)
             end)
   /\  
  (forall p,
        TcVal p ->        
        forall stty stty',
        (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t') -> 
        get_store_typing_val p = stty -> mk_TcVal_ext_store_ty p stty') 
  /\
     (forall p,
        TcEnv p ->           
        forall stty stty',
        (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t') -> 
        get_store_typing_env p = stty -> mk_TcEnv_ext_store_ty p stty').
Proof.
  apply tc__xind; try (solve [econstructor;eauto] ).
  - intros. 
    unfold mk_TcVal_ext_store_ty, 
           mk_TcEnv_ext_store_ty, 
           get_store_typing_val, 
           get_store_typing_env in *; simpl in *.
    subst.
    econstructor; eauto.
  - intros.
     unfold mk_TcVal_ext_store_ty, 
           mk_TcEnv_ext_store_ty, 
           get_store_typing_val, 
           get_store_typing_env in *; simpl in *.
    subst.
    econstructor; eauto.
  - intros.
    unfold mk_TcVal_ext_store_ty, 
           mk_TcEnv_ext_store_ty, 
           get_store_typing_val, 
           get_store_typing_env in *; simpl in *.
    subst.
    econstructor; eauto.
  - intros.
    unfold mk_TcVal_ext_store_ty, 
           mk_TcEnv_ext_store_ty, 
           get_store_typing_val, 
           get_store_typing_env in *; simpl in *.
    subst.
    econstructor; eauto.
Qed.

Lemma ext_stores__val:
   forall stty stty',
     (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t') -> 
     (forall v t, TcVal (stty, v, t) -> 
      TcVal (stty', v, t)).
Proof.
  intros.
  eapply (match ext_stores__exp__bt__aux with conj _ (conj _ (conj F _)) =>
   F (stty, v, t) end); eauto.
Qed.

Lemma ext_stores__env:
   forall stty stty',
     (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t') -> 
     (forall rho env ctxt, TcEnv (stty, rho, env, ctxt) ->  
      TcEnv (stty', rho, env, ctxt)).
Proof.
  intros.
  eapply (match ext_stores__exp__bt__aux 
          with conj _ (conj _ (conj _ F)) =>
               F (stty, rho, env, ctxt) end); eauto.
Qed.


