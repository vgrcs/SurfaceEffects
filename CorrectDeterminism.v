Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.FSets.FMapAVL. 
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Arith.Peano_dec.
Require Import Ascii String.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Mult.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Minus.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.

Add LoadPath "." as Top.
Require Import Top.Keys.
Require Import Top.Heap.
Require Import Top.Tactics.
Require Import Top.EffectSystem.
Require Import Top.Environment.
Require Import Top.TypeSystem.
Require Import Top.Determinism.
Require Import Top.DeterminismExt.
Require Import Top.Definitions.
Require Import Top.CorrectnessLemmas.
Require Import Top.Axioms.

Import TypeSoundness.
Import EffectSoundness.

Lemma EvalTrueIsTrue:
  forall h h' h'' env rho e efft efff eff tacts,
  (h, env, rho, Cond e efft efff) ⇓ (h'', Eff eff, tacts) ->
  (h, env, rho, e) ⇓ (h', Bit true, Phi_Nil) ->
  (h', env, rho, efft) ⇓ (h'', Eff eff, tacts).
Proof.
  intros.
  inversion H; subst.   
  - assert ( Hbit : H.Equal h' cheap /\ Bit true = Bit true /\  Phi_Nil = cacts ).
    eapply DynamicDeterminism_ext; eauto.   
    assert ( HD :h = h') by (eapply EmptyTracePreservesHeap_1; eauto).  apply HMapP.Equal_refl.
    destruct Hbit as [? [H_ ?]]; inversion H_; subst.
    assert ( HD :h = cheap) by (eapply EmptyTracePreservesHeap_1; eauto). 
    rewrite Phi_Seq_Nil_L.
    assert ( HD_ :h = h') by (eapply EmptyTracePreservesHeap_1; eauto).
    subst.
    rewrite <- HD_.
    assumption. 
  - assert ( Hbit : H.Equal h' cheap /\ Bit true = Bit false /\  Phi_Nil = cacts )
      by (eapply DynamicDeterminism_ext; eauto; 
          assert ( HD :h = h') by (eapply EmptyTracePreservesHeap_1; eauto); 
          apply HMapP.Equal_refl).
     destruct Hbit as [? [H_ ?]]; inversion H_; subst.
Qed.

Lemma EvalFalseIsFalse:
forall h h' h'' env rho e efft efff eff tacts,
  (h, env, rho, Cond e efft efff) ⇓ (h'', Eff eff, tacts) ->
  (h, env, rho, e) ⇓ (h', Bit false, Phi_Nil) ->
  (h', env, rho, efff) ⇓ (h'', Eff eff, tacts).
Proof.
  intros.
  inversion H; subst. 
  - assert ( Hbit : H.Equal h' cheap /\ Bit false = Bit true /\  Phi_Nil = cacts )
      by (eapply DynamicDeterminism_ext; eauto; 
          assert ( HD :h = h') by (eapply EmptyTracePreservesHeap_1; eauto); 
          apply HMapP.Equal_refl).
     destruct Hbit as [? [H_ ?]]; inversion H_; subst.
  - assert ( Hbit : H.Equal h' cheap /\ Bit false = Bit false /\  Phi_Nil = cacts ).
    eapply DynamicDeterminism_ext; eauto.   
    assert ( HD :h = h') by (eapply EmptyTracePreservesHeap_1; eauto).  apply HMapP.Equal_refl.
    destruct Hbit as [? [H_ ?]]; inversion H_; subst.
    assert ( HD :h = cheap) by (eapply EmptyTracePreservesHeap_1; eauto). 
    rewrite Phi_Seq_Nil_L.
    assert ( HD_ :h = h') by (eapply EmptyTracePreservesHeap_1; eauto).
    subst.
    rewrite <- HD_.
    assumption. 
Qed. 

Definition Correctness_ext_1 :
  forall h h' h'' env rho  p p' v eff stty ctxt rgns ea ee,
    (h, env, rho, ea) ⇓ (h', v, p) ->
    forall h_ h'_ v_ p_,
      H.Equal h h_ ->
      (h_, env, rho, ea) ⇓ (h'_, v_, p_) ->
      (h, env, rho, ee) ⇓ (h'', Eff eff, p') ->
    BackTriangle (stty, ctxt, rgns, rho, ea, ee) ->
    forall static ty, 
      ReadOnlyPhi p' ->
      TcHeap (h, stty) ->
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) -> 
      TcExp (stty, ctxt, rgns, ea, ty, static) ->
      H.Equal h' h'_ /\ v = v_ /\ p = p_.
Proof.
   intros h  h'  h'' env rho p  p' v  eff stty ctxt rgns ea ee BS1. 
   generalize dependent p'. 
   generalize dependent ee.
   generalize dependent stty.
   generalize dependent ctxt.
   generalize dependent rgns.
   generalize dependent eff.
   generalize dependent h''.
   dynamic_cases (dependent induction BS1) Case;
     intros h'' eff rgns ctxt stty ee_exp p'; 
     intros h_ h'_ v_ p_ HEqual BS2;
     intros HEff HBt static ty HRonly HHeap HRho HEnv HExp;
     inversion BS2; subst;
     try (solve [intuition]).
   Case "var x".
     inversion BS2; subst. intuition. 
     rewrite H in H1. inversion H1; subst. reflexivity.
   Case "mu_app".
      { inversion HBt as [ | | | |  
                                 | ? ? ? ? ? ? ? ? ? ? ? ? TcExp_ef TcExp_ea HBt_ef HBt_ea HR_ef HR_ea 
                                 | | | | | | | | |]; subst.
        - inversion HEff; subst. inversion H11; subst.
          inversion HRonly; subst.  inversion H5; subst.
          assert ( RH1 : H.Equal fheap fheap0 /\ Cls (env', rho', Mu f x ec' ee') = 
                                           Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0) /\ facts = facts0 ).
          eapply IHBS1_1 with (ee:=efff); eauto.
          destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst. 
          assert ( RH2 : H.Equal aheap aheap0 /\ v0 = v1 /\ aacts = aacts0).
          assert (HEq_1 : fheap = h'').  
          { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts0) in HR_ef. 
            - apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1.  
              assumption. assumption.
            - assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, facts0)) by
                  (eapply eff_sound; eauto). 
              eassumption. }
          assert (aacts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ea, aacts)) by
              (eapply eff_sound; eauto; rewrite HEq_1; assumption).
          assert (HEq_2 : aheap = fheap).   
          { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=aacts) in HR_ea.
            - apply ReadOnlyTracePreservesHeap_1 in BS1_2. symmetry in BS1_2.
              assumption. assumption. 
            - eassumption. }
          { eapply IHBS1_2 with (ee:=effa) (p':=phia0); eauto.
            - rewrite HEq_1. eassumption.
            - rewrite HEq_1. eassumption. } 
          destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]; subst. 
          
          assert ( RH3 : H.Equal h' h'_ /\ v = v_ /\ bacts = bacts0).
          assert (HEq_1 : fheap = h'').  
          { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts0) in HR_ef. 
            - apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1.  
              assumption. assumption.
            - assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, facts0)) by
                  (eapply eff_sound; eauto). 
              eassumption. }
          assert (aacts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ea, aacts0)) by
              (eapply eff_sound; eauto; rewrite HEq_1; assumption).
          assert (HEq_2 : aheap = fheap).   
          { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=aacts0) in HR_ea.
            - apply ReadOnlyTracePreservesHeap_1 in BS1_2. symmetry in BS1_2.
              assumption. assumption. 
            - eassumption. }
          { eapply IHBS1_3 with (ee:=ee'0); eauto.
            - admit.
            - eapply ext_stores__bt; eauto.
          destruct RH3 as [h_eq_3 [v_eq_3 a_eq_3]]; subst.
          auto.

eapply IHBS1_3
            with 
                   (ee:= ee') 
                   (h'':= h''); eauto.
            -  
            - inversion HRonly; subst. inversion H5; subst. inversion H8; subst. assumption.
            - { apply update_env; simpl.  
                - eapply ext_stores__env; eauto. 
                  apply update_env.  
                  + eassumption.
                  + eapply ext_stores__val with (stty:=sttyb); eauto.
                - eapply ext_stores__val with (stty:=sttya); eauto. }
            - eapply ext_stores__exp; eauto. } 

Definition Correctness_ext :
  forall h h' h'' env rho  p p' v eff stty ctxt rgns ea ee,
    (h, env, rho, ea) ⇓ (h', v, p) ->
    forall h_ h'_ v_ p_,
      H.Equal h h_ ->
      (h_, env, rho, ea) ⇓ (h'_, v_, p_) ->
      (h, env, rho, ee) ⇓ (h'', Eff eff, p') ->
    BackTriangle (stty, ctxt, rgns, rho, ea, ee) ->
    forall static ty, 
      ReadOnlyPhi p' ->
      TcHeap (h, stty) ->
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) -> 
      TcExp (stty, ctxt, rgns, ea, ty, static) ->
      p ⊑ eff /\ H.Equal h' h'_ /\ v = v_ /\ p = p_.
Proof.
    intros h  h'  h'' env rho p  p' v  eff stty ctxt rgns ea ee BS1. 
    generalize dependent p'. 
    generalize dependent ee.
    generalize dependent stty.
    generalize dependent ctxt.
    generalize dependent rgns.
    generalize dependent eff.
    generalize dependent h''.
    dynamic_cases (dependent induction BS1) Case;
    intros h'' eff rgns ctxt stty ee_exp p'; 
    intros h_ h'_ v_ p_ HEqual BS2;
    intros HEff HBt static ty HRonly HHeap HRho HEnv HExp;
    try (solve [assert (Phi_Nil ⊑ eff) by (constructor); inversion BS2; subst; intuition]).
    Case "var x".
    assert (Phi_Nil ⊑ eff) by (constructor).
    inversion BS2; subst; intuition.
    rewrite H in H2. now inversion H2.
    Case "mu_app".  
     
      (* Start the proof of the "effect soundness" part *) 
      inversion HExp as  [ | | | | | 
                           ? ? ? ? ? ? ? ? ? ? ? HExp_ef HExp_ea 
                           | | | | | | | | | | | | | | | | | | | ]; subst.
      assert (clsTcVal : exists stty',  
                           (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
                           /\ TcHeap (fheap, stty')
                           /\ TcVal (stty', 
                                     Cls (env', rho', Mu f x ec' ee'), 
                                     subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
        by (eapply ty_sound; eauto).
      destruct clsTcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
      
      assert (argTcVal : exists stty',
                           (forall l t', ST.find l sttyb = Some t' -> ST.find l stty' = Some t')
                           /\ TcHeap (aheap, stty')
                           /\ TcVal (stty', v0, subst_rho rho tya))
        by (eapply ty_sound; eauto using update_env, ext_stores__env, ext_stores__exp).
      destruct argTcVal as [sttya [Weaka [TcHeapa TcVal_v']]]; eauto.
      
      inversion TcVal_cls as [ | | | 
                               ? ? ? ? ? ? ? TcRho_rho' TcEnv_env' TcExp_abs [A B C D HSubst] 
                               | | |]; subst. 
      inversion TcExp_abs as [ | | | 
                               ? ? ? ? ? ? ? ? ? ? ? HBt_ec_ee TcExp_ec' TcExp_ee' 
                               | | | | | | | | | | | | | | | | | | | | |]; subst.
      rewrite <- HSubst in TcVal_cls.
      do 2 rewrite subst_rho_arrow in HSubst. 
      inversion HSubst as [[H_tyx_tya A C D E]]; clear A C D E.
      rewrite <- H_tyx_tya in TcVal_v'.
    
      (* left part of the conjunction *)
      assert (HSOUND : Phi_Seq (Phi_Seq facts aacts) bacts ⊑ eff).
    
      { apply PTS_Seq. 
        SCase "Phi_Seq facts aacts ⊑ eff".
          apply PTS_Seq.
          SSCase "facts ⊑ eff".
            assert (H_ : facts  ⊑ eff). 
            {
              inversion HBt as [ | | | |  
                                 | ? ? ? ? ? ? ? ? ? ? ? ? TcExp_ef TcExp_ea HBt_ef HBt_ea HR_ef HR_ea 
                                 | | | | | | | | |]; subst.
              SSSCase "Mu_App ef ea0 << (efff0 ⊕ (effa0 ⊕ Eff_App ef ea0))". 
                inversion HEff; subst.  
                assert (facts  ⊑ effa1).
                { eapply IHBS1_1 with (h_:=h'') (p_:=facts); eauto.  
                  - apply HFacts.Equal_refl.
                  - inversion HRonly. assumption. }
                apply Theta_introl. assumption. 
              SSSCase "Mu_App ef ea0 << (⊤)".  
                inversion HEff; subst.
                apply PhiInThetaTop.
            }
            exact H_.    
      SSCase " aacts ⊑ eff".   
        inversion HBt as [ | | | |  
                           | ? ? ? ? ? ? ? ? ? ? ? ? TcExp_ef TcExp_ea HBt_ef HBt_ea HR_ef HR_ea 
                           | | | | | | | | |]; subst.
        SSSCase "Mu_App ef ea0 << (efff0 ⊕ (effa0 ⊕ Eff_App ef ea0))". 
          assert (H_ : aacts  ⊑ eff).
          { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts) in HR_ef. 
            - apply ReadOnlyTracePreservesHeap_1 in BS1_1. 
              + symmetry in BS1_1.
                inversion HEff; subst. inversion H8; subst. 
                assert (aacts  ⊑ effa2).
                eapply IHBS1_2 with (h_:=h'') (p_:=aacts); eauto.
                * apply HFacts.Equal_refl.  
                * inversion HRonly as [ | | ? ? ? ROnly2 | ]; subst. 
                  inversion ROnly2; subst; assumption.     
                * apply Theta_intror. apply Theta_introl. 
                  assumption.
              + assumption.  
            - assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, facts)) by
                  (eapply eff_sound; eauto). 
              eassumption. }
          exact H_.
        SSSCase "Mu_App ef ea0 << (⊤)".  
          assert (H_ : aacts  ⊑ eff).
          { induction eff; inversion HEff; subst. 
            apply PhiInThetaTop. }
          exact H_.
      SCase "bacts ⊑ eff".       
        inversion HEff; subst; 
        inversion HBt as [ | | | |  
                           | ? ? ? ? ? ? ? ? ? ? ? ? TcExp_ef TcExp_ea HBt_ef HBt_ea HR_ef HR_ea 
                           | | | | | | | | |]; subst. 
        SSSCase "Mu_App ef ea0 << (efff0 ⊕ (effa0 ⊕ Eff_App ef ea0))".
          assert (HEq_1 : fheap = h'').  
          { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts) in HR_ef. 
            - apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1.  
              assumption. assumption.
            - assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, facts)) by
                  (eapply eff_sound; eauto). 
              eassumption. }
          
          assert (aacts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ea, aacts)) by
              (eapply eff_sound; eauto; rewrite HEq_1; assumption).
          
          assert (HEq_2 : aheap = fheap).  
          { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=aacts) in HR_ea.
            - apply ReadOnlyTracePreservesHeap_1 in BS1_2. symmetry in BS1_2.
              assumption. assumption. 
            - eassumption. }
          
          inversion H7; subst.   
          
          assert (H' : facts  ⊑ effa0).
          { eapply IHBS1_1 with (h_:=h'') (ee:=a); eauto. 
            - apply HFacts.Equal_refl. 
            - inversion HRonly; subst; assumption. }
          
          assert (H'' : aacts  ⊑ effa2).   
          { eapply IHBS1_2 with (ee:=effa1) (p':=phia0) (h_:=h''); eauto.
            - apply HFacts.Equal_refl. 
            - inversion HRonly as [| | ? ? ? A |]; inversion A; subst; assumption. } 
          
          inversion H9; subst.
          assert (HD: facts  ⊑ effa0 /\
                      H.Equal h'' h'' 
                      /\  Cls (env', rho', Mu f x ec' ee') = Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0)
                      /\ facts = facts0) by
              (eapply  IHBS1_1  with (h_:=h''); eauto; [apply HFacts.Equal_refl | now inversion HRonly]).
          destruct HD as [A [HeqHeap [HEqCls HEqfacts]]].  symmetry in HEqCls.   inversion HEqCls; subst. 
          
          assert (HD' : aacts  ⊑ effa2 /\  H.Equal h'' h'' /\ v0 =  v' /\ aacts =  aacts0) by
              (eapply IHBS1_2; eauto; inversion HRonly; inversion H5; assumption).
          destruct HD' as [A_ [B [C D]]]; symmetry in C, D; subst.
          
          assert (H_ : bacts  ⊑ effb0). 
          { eapply IHBS1_3
            with (stty:=sttya) 
                   (ee:= ee') 
                   (h'':= h''); eauto.
            - eapply ext_stores__bt; eauto. 
            - inversion HRonly; subst. inversion H5; subst. inversion H8; subst. assumption.
            - { apply update_env; simpl.  
                - eapply ext_stores__env; eauto. 
                  apply update_env.  
                  + eassumption.
                  + eapply ext_stores__val with (stty:=sttyb); eauto.
                - eapply ext_stores__val with (stty:=sttya); eauto. }
            - eapply ext_stores__exp; eauto. } 
          apply Theta_intror.  apply Theta_intror. 
          exact H_.
        SSSCase "Mu_App ef ea0 << (⊤)".
          assert (H_ : bacts ⊑ None).
          { eapply IHBS1_3 
            with (stty:=sttya) (ee:=⊤); eauto. 
            SSSSCase "Equal Heaps".
              apply HFacts.Equal_refl. 
            SSSSCase "Effect Evaluation".
              econstructor.
            SSSSCase "Back Triangle". 
              econstructor.
            SSSSCase "Extended TcEnv".
              { apply update_env; simpl.  
                - eapply ext_stores__env; eauto. 
                  apply update_env.  
                  + eassumption.
                  + eapply ext_stores__val with (stty:=sttyb); eauto.
                - eapply ext_stores__val with (stty:=sttya); eauto. }
              SSSSCase "Extended TcExp". 
              eapply ext_stores__exp; eauto. }
          exact H_. } 

      (* Start the proof of the "determinism" part *) 
 
      eapply BS_Mu_App in BS1_3; eauto.
      assert (RH : H.Equal h' h'_ /\ v = v_ /\ Phi_Seq (Phi_Seq facts aacts) bacts = p_).
      eapply DynamicDeterminism_ext_1; eauto.
      intuition.   
  Case "rgn_app".
Admitted.