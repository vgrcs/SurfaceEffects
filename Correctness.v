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

Definition Correctness :
  forall h h' h'' env rho  p p' v eff stty ctxt rgns ea ee,
    (h, env, rho, ea) ⇓ (h', v, p) ->
    (h, env, rho, ee) ⇓ (h'', Eff eff, p') ->
    BackTriangle (stty, ctxt, rgns, rho, ea, ee) ->
    forall static ty, 
      ReadOnlyPhi p' ->
      TcHeap (h, stty) ->
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) -> 
      TcExp (stty, ctxt, rgns, ea, ty, static) ->
      p ⊑ eff.
Proof.
  intros h h' h'' env rho p p' v eff stty ctxt rgns ea ee BS1. 
  generalize dependent p'. 
  generalize dependent ee.
  generalize dependent stty.
  generalize dependent ctxt.
  generalize dependent rgns.
  generalize dependent eff.
  generalize dependent h''.
  dynamic_cases (dependent induction BS1) Case;
  intros; try (solve [econstructor]).
  Case "mu_app". 
    try (solve [inversion H; subst; inversion_clear H0]).
    inversion_clear H5.
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
      
      inversion TcVal_cls as [ | | | ? ? ? ? ? ? ? TcRho_rho' TcEnv_env' TcExp_abs | | ]; subst. 
      inversion TcExp_abs as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | | | | | | | | | | | | | ]; subst.
      rewrite <- H11 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H11. inversion H11. 
      rewrite <- H12 in TcVal_v'.
 
      apply PTS_Seq. 
      SCase "Phi_Seq facts aacts ⊑ eff".
        apply PTS_Seq.
        SSCase "facts ⊑ eff".
          inversion H0; subst.
          SSSCase "Mu_App ef ea0 << (efff0 ⊕ (effa0 ⊕ Eff_App ef ea0))". 
            inversion H; subst. 
            assert (facts  ⊑ effa1).
            eapply IHBS1_1; eauto. 
            inversion H1. assumption.
            apply Theta_introl. assumption. 
          SSSCase " Mu_App ef ea0 << Eff_App ef ea0".  
             eapply IHBS1_1; eauto. 
          SSSCase "Mu_App ef ea0 << (⊤)".  
            inversion H; subst.
            apply PhiInThetaTop.
        SSCase " aacts ⊑ eff".    
          inversion H0; subst.
          SSSCase "Mu_App ef ea0 << (efff0 ⊕ (effa0 ⊕ Eff_App ef ea0))". 
            eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts) in H27.
            apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1.
            inversion H; subst. inversion H31; subst.
            assert (aacts  ⊑ effa2). 
            eapply IHBS1_2; subst; eauto.
            inversion H1; subst. inversion H21; subst. assumption.
            apply Theta_intror. apply Theta_introl. assumption.
            assumption.
            assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, facts)).
            eapply eff_sound; eauto. 
            eassumption.
          SSSCase "Mu_App ef ea0 << Eff_App ef ea0".  
            eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts) in H27. 
            apply ReadOnlyTracePreservesHeap_1 in BS1_1. 
            symmetry in BS1_1.  rewrite <- BS1_1 in H.
                
            eapply IHBS1_2; eauto using ext_stores__env,  ext_stores__exp.    
            
            eapply EqualHeaps; eauto. now apply Equal_heap_equal.
            assumption.
            
            assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, facts)).
            eapply eff_sound; eauto. 
            eassumption.
          SSSCase "Mu_App ef ea0 << (⊤)".  
            induction eff; inversion H.
            eapply IHBS1_2 with (h'':=fheap) (ee:=⊤) ; eauto using ext_stores__env,  ext_stores__exp.  
            rewrite <- H21; econstructor. 
            econstructor.
      SCase "bacts ⊑ eff".     
        inversion H; subst; inversion H0; subst. 
        SSSCase "Mu_App ef0 ea << Eff_App ef0 ea".
          assert (HEq_1 : fheap = h'').  
          eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts) in H31. 
          apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1.  
          assumption. assumption.

          assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, facts)).
          eapply eff_sound; eauto. 
          eassumption.

          assert (aacts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ea, aacts)).
          eapply eff_sound; eauto. rewrite HEq_1. assumption.

          assert (HEq_2 : aheap = fheap).  
          eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=aacts) in H32.
          apply ReadOnlyTracePreservesHeap_1 in BS1_2. symmetry in BS1_2.
          assumption. assumption. eassumption. 
 
          assert (facts  ⊑ eff). 
          eapply IHBS1_1  with (stty:=stty) ; eauto.
  
          assert (aacts  ⊑ eff).      
          { eapply IHBS1_2 with (stty:=stty); eauto.
            - rewrite HEq_1. eassumption.
            - eapply EqualHeaps; eauto. symmetry in HEq_1. now apply Equal_heap_equal. }  
          
          assert (HSubset : Phi_Seq facts aacts ⊑ (Union_Theta eff eff)).
          eapply EnsembleUnionComp; eauto.
 
          assert (HD: H.Equal h'' h'' /\ Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0) =
                                           Cls (env', rho', Mu f x ec' ee') /\ facts0 = facts)
            by (eapply DynamicDeterminism_ext; eauto; 
                rewrite HEq_1 in BS1_1; [apply HFacts.Equal_refl | assumption]).  
          destruct HD as [? [HD_ ?]]; inversion HD_; subst.
          
          assert (HD' : H.Equal h'' h'' /\  v' = v0 /\ aacts0 = aacts)
            by (eapply DynamicDeterminism_ext; eauto). destruct HD' as [? [? ?]]; subst. 
          
          { eapply IHBS1_3
            with (stty:=sttya) 
                   (ee:= ee') 
                   (h'':= h''); eauto. 
            - eapply ext_stores__bt; eauto.
            - inversion H1. assumption.
            - { apply update_env; simpl.  
                - eapply ext_stores__env; eauto. 
                 apply update_env.  
                  + eassumption.
                  + eapply ext_stores__val with (stty:=sttyb); eauto.
                - eapply ext_stores__val with (stty:=sttya); eauto. }
            - eapply ext_stores__exp; eauto. }
        SSSCase "Mu_App ef ea0 << (efff0 ⊕ (effa0 ⊕ Eff_App ef ea0))".
          assert (HEq_1 : fheap = h'').  
          eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts) in H30. 
          apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1.  
          assumption. assumption.

          assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, facts)).
          eapply eff_sound; eauto. 
          eassumption.

          assert (aacts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ea, aacts)).
          eapply eff_sound; eauto. rewrite HEq_1. assumption.

          assert (HEq_2 : aheap = fheap).  
          eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=aacts) in H31.
          apply ReadOnlyTracePreservesHeap_1 in BS1_2. symmetry in BS1_2.
          assumption. assumption. eassumption. 
 
          inversion H24; subst.   
          
          assert (facts  ⊑ effa0) by
              (eapply IHBS1_1 with (ee:=a); eauto; inversion H1; subst; assumption).
 
          assert (aacts  ⊑ effa2) by   
              (eapply IHBS1_2 with (ee:=effa1) (p':=phia0); eauto;
               inversion H1; inversion H22; subst; assumption). 

          inversion H32; subst.
          assert (HD: H.Equal h'' h'' /\  Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0)  =
                                          Cls (env', rho', Mu f x ec' ee') /\ facts0 = facts)
            by (eapply DynamicDeterminism_ext; eauto;  apply HMapP.Equal_refl).  
          destruct HD as [? [H_ ?]]; inversion H_; subst.
          
          assert (HD' : H.Equal h'' h'' /\ v' =  v0 /\ aacts0 =  aacts).
          eapply DynamicDeterminism_ext; eauto.
          destruct HD' as [? [H__ ?]]; inversion H__; subst.

          assert (bacts  ⊑ effb0). 
          { eapply IHBS1_3
              with (stty:=sttya) 
                   (ee:= ee') 
                   (h'':= h''); eauto.
            - eapply ext_stores__bt; eauto. 
            - inversion H1; subst. inversion H35; subst. inversion H39; subst. assumption.
            - { apply update_env; simpl.  
                - eapply ext_stores__env; eauto. 
                  apply update_env.  
                  + eassumption.
                  + eapply ext_stores__val with (stty:=sttyb); eauto.
                - eapply ext_stores__val with (stty:=sttya); eauto. }
            - eapply ext_stores__exp; eauto. }
          apply Theta_intror.  apply Theta_intror. assumption.
        SSSCase "Mu_App ef ea0 << (⊤)".
          eapply IHBS1_3 
            with (stty:=sttya) 
                 (ee:=⊤); eauto.
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
              eapply ext_stores__exp; eauto.
  Case "rgn_app".
    inversion_clear H6; subst.    
    assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Lambda x eb), 
                         subst_rho rho (Ty2_ForallRgn effr tyr))). 
    eapply ty_sound;eauto. 
    destruct clsTcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
    inversion TcVal_cls as  [ | | | ? ? ? ? ? ? ? TcRho_rho' TcEnv_env' TcExp_abs | | ]; subst.  
    inversion TcExp_abs as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | | | | | | | | | | | | | ]; subst.
    rewrite <- H12 in TcVal_cls.
    do 2 rewrite subst_rho_forallrgn in H12.
    inversion H12.
    
    apply PTS_Seq.
    SCase "facts ⊑ eff".
      eapply IHBS1_1; eauto. 
      inversion H1; subst; eauto.
      econstructor; eauto.
    SCase " bacts ⊑ eff".
      inversion H1; subst.
      SSCase "Rgn_App er w << (∅)".
        eapply IHBS1_2 with (ee:=∅); eauto. 
        inversion H0; subst. econstructor.
        apply update_rho; auto.
        eapply extended_rho; eauto.
      SSCase "Rgn_App er w << (⊤)".  
        eapply IHBS1_2 with (ee:=⊤); eauto using update_rho, extended_rho. 
        induction eff.
        SSSCase "Top evaluates to None". 
          inversion_clear H0.  
        SSSCase "Top heaps are equal". 
          inversion H0; subst; econstructor. 
        SSSCase "eb << (⊤)". 
          econstructor. 
  Case "eff_app". 
    inversion H0; subst.   
    { apply PTS_Seq.
      - apply PTS_Seq. 
        + inversion H; subst.
          apply PhiInThetaTop.
        +  inversion H; subst.
           apply PhiInThetaTop.
      - inversion H; subst.
        apply PhiInThetaTop. }
  Case "par_pair".
    inversion H6; subst.
    apply PTS_Seq; inversion H5; subst; apply PhiInThetaTop.
  Case "cond_true". 
    inversion H0; subst. 
    SCase "Cond e et ef << Cond e efft efff".
      assert (cacts ⊑ Some empty_set) by
          (eapply IHBS1_1 with (p':=Phi_Nil); eauto; constructor).
      apply EmptyUnionIsIdentity.
      apply EmptyIsNil in H6; subst.
      apply PTS_Seq; [apply PTS_Nil |].
      assert (ef_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e, Phi_Nil)).
      eapply eff_sound; eauto.
      assert (HEq_1 :  cheap = h). 
      eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=Phi_Nil) in H17.
      apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
      assumption. constructor. eassumption.
      rewrite UnionEmptyWithEffIsEff. 
      eapply IHBS1_2 with (ee:=efft); eauto. 
      SSCase "Invoke DynamicDeterminism to prove equal heaps".
        eapply EvalTrueIsTrue; eauto.
        eapply EqualHeaps; eauto. 
        apply Equal_heap_equal. auto.
    SCase "Cond e et ef << (⊤)". 
      inversion H; subst.  
      constructor; apply PhiInThetaTop.
  Case "cond_false".    
    inversion H0; subst. 
    SCase "Cond e et ef << Cond e efft efff".
      assert (cacts ⊑ Some empty_set) by 
          (eapply IHBS1_1 with (p':=Phi_Nil); eauto; constructor).
      apply EmptyUnionIsIdentity.
      apply EmptyIsNil in H6; subst.
      apply PTS_Seq; [apply PTS_Nil |].
      assert (ef_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e, Phi_Nil)).
      eapply eff_sound; eauto.
      assert (HEq_1 :  cheap = h). 
      eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=Phi_Nil) in H17.
      apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
      assumption. constructor. eassumption.
      rewrite UnionEmptyWithEffIsEff.
      eapply IHBS1_2 with (ee:=efff); eauto; [| rewrite HEq_1; assumption].
      SSCase "Invoke DynamicDeterminism to prove equal heaps".
        eapply EvalFalseIsFalse; eauto. 
    SCase "Cond e et ef << (⊤)".  
      inversion H; subst. 
      constructor; apply PhiInThetaTop.
  Case "new_ref e".
  inversion H1; subst; inversion H2; subst.
    apply EnsembleUnionComp.    
    SCase "Ref w e << (a ⊕ AllocAbs w)". 
     eapply IHBS1; eauto; inversion H3; assumption.
     inversion H16; subst.
     apply PTS_Elem. apply DAT_Alloc_Abs.
     rewrite H in H9. inversion H9.
     apply In_singleton.
    SCase "Ref w e << (⊤)". 
     apply PhiInThetaTop.  
  Case "get_ref e".     
   inversion H2; subst.
   SCase "DeRef w ea0 << (eff0 ⊕ ReadAbs w)".
     inversion H1; subst. 
     apply EnsembleUnionComp.
     SSCase "aacts ⊑ effa".
       eapply IHBS1; eauto. 
       inversion H3; subst. assumption.
     SSCase "Phi_Elem (DA_Read r l v) ⊑ effb".
       apply PTS_Elem. inversion H19; subst.
       rewrite H in H9; inversion H9.
       apply DAT_Read_Abs. apply In_singleton.
   SCase "DeRef (Rgn2_Const true false r0) ea0 << ReadConc ea0".    
     inversion H1; subst.
     assert (aacts ⊑ Some empty_set) by (eapply IHBS1; eauto; constructor).
     apply PTS_Seq.
     SSCase " aacts ⊑ Some (singleton_set (CA_ReadConc r1 l0))".
      apply EmptyInAnyTheta. assumption.
     SSCase " Phi_Elem (DA_Read r l v) ⊑ Some (singleton_set (CA_ReadConc r1 l0))".  
      apply PTS_Elem.
      simpl in H; inversion H; subst.
      assert (HD: H.Equal h'' h' /\  Loc (Rgn2_Const true false r1) l0 =
                                     Loc (Rgn2_Const true false r) l /\ Phi_Nil = aacts)
        by (eapply DynamicDeterminism_ext; eauto; apply HMapP.Equal_refl).
      destruct HD as [? [H_ ?]]; inversion H_; subst.
      apply DAT_Read_Conc. apply In_singleton.
   SCase "DeRef w ea0 << (⊤)".   
     econstructor.  
     SSCase "aacts ⊑ eff".
       inversion H1; subst.
       inversion H7; subst.
       eapply IHBS1; eauto.  econstructor. 
     SSCase "Phi_Elem (DA_Read r l v) ⊑ eff".
       inversion H1; subst.    
       apply PTS_Elem. apply DAT_Top.
  Case "set_ref e1 e2".
    inversion H1; subst.
    SCase "Assign w ea0 ev << (eff1 ⊕ (eff2 ⊕ WriteAbs w))".
      inversion H0; subst.
      apply PTS_Seq.
      SSCase "Phi_Seq aacts vacts ⊑ Union_Theta effa effb".
        apply EnsembleUnionComp.
        SSSCase "aacts ⊑ effa".
          inversion H6; subst.
          eapply IHBS1_1; eauto. 
          inversion H2; subst. assumption.
        SSSCase "vacts ⊑ effb". 
          inversion H20; subst. inversion H6; subst.
            
          assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e1, aacts)).
          eapply eff_sound; eauto. 
          assert (HEq_1 : heap' = h'').   
          eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=aacts) in H18.
          apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
          assumption. assumption. eassumption.
        
          assert (vacts ⊑ effa0). 
          { eapply IHBS1_2 with (p':= phia0); eauto.   
            - rewrite HEq_1. eassumption.
            - inversion H2; subst. inversion H13; subst. eassumption.
            - rewrite HEq_1. assumption. }
          apply Theta_introl. assumption.
      SSCase "Phi_Elem (DA_Write r l v0) ⊑ Union_Theta effa effb".    
       inversion H20; subst. 
       assert (Phi_Elem (DA_Write r l v0) ⊑ effb0).
       apply PTS_Elem. inversion H21; subst.
       rewrite H in H8. inversion H8; subst.
       apply DAT_Write_Abs; apply In_singleton.
       apply Theta_intror. apply Theta_intror. assumption.
    SCase " Assign (Rgn2_Const true false r0) ea0 ev << (eff1 ⊕ (eff2 ⊕ WriteConc ea0))".
      inversion H0; subst.
      apply PTS_Seq.
      SSCase "Phi_Seq aacts vacts ⊑ Union_Theta effa effb".
        apply EnsembleUnionComp.
          SSSCase "aacts ⊑ effa".
            inversion H6; subst.
            eapply IHBS1_1; eauto. 
            inversion H2; subst. assumption.
          SSSCase "vacts ⊑ effb". 
            inversion H6; subst.
            inversion H20; subst.

            assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e1, aacts)).
            eapply eff_sound; eauto. 
            assert (HEq_1 : heap' = h''). 
            eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=aacts) in H18.
            apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
            assumption. assumption. eassumption.

            assert (vacts ⊑ effa0). 
            { eapply IHBS1_2 with (p':= phia0); eauto.   
              - rewrite HEq_1. eassumption.
              - inversion H2; subst. inversion H14; subst. assumption.
              - rewrite HEq_1. assumption. }
            apply Theta_introl. assumption. 
      SSCase "Phi_Elem (DA_Write r l v0) ⊑ Union_Theta effa effb".
        inversion H20; subst. 
        assert (Phi_Elem (DA_Write r l v0) ⊑ effb0).
        apply PTS_Elem. inversion H21; subst.
        assert (HD: H.Equal heap' h'' /\  Loc (Rgn2_Const true false r0) l =
                                          Loc (Rgn2_Const true false r1) l0 /\ aacts = Phi_Nil)
          by (eapply DynamicDeterminism_ext; eauto; apply HMapP.Equal_refl).
        destruct HD as [? [H_ ?]]; inversion H_; subst.
        inversion H; subst.
        apply DAT_Write_Conc; apply In_singleton.
        apply Theta_intror. apply Theta_intror. assumption.
    SCase "Assign w ea0 ev << (⊤)". 
      inversion H0; subst.   
      apply PhiInThetaTop.
  Case "nat_plus x y". 
    inversion H0; subst.
    apply PTS_Seq. 
    SCase "lacts ⊑ eff".
      inversion H; subst. 
      apply PhiInThetaTop.  
    SCase "racts ⊑ eff".    
      inversion H; subst.
      apply PhiInThetaTop. 
  Case "nat_minus x y".    
    inversion H0; subst.
    apply PTS_Seq. 
    SCase "lacts ⊑ eff".
      inversion H; subst. 
      apply PhiInThetaTop.  
    SCase "racts ⊑ eff".    
      inversion H; subst.
      apply PhiInThetaTop.
  Case "nat_times x y".
    inversion H0; subst.
    apply PTS_Seq. 
    SCase "lacts ⊑ eff".
      inversion H; subst. 
      apply PhiInThetaTop.  
    SCase "racts ⊑ eff".    
      inversion H; subst.
      apply PhiInThetaTop.
  Case "bool_eq x y".
    inversion H0; subst.
    apply PTS_Seq. 
    SCase "lacts ⊑ eff".
      inversion H; subst. 
      apply PhiInThetaTop.  
    SCase "racts ⊑ eff".    
      inversion H; subst.
      apply PhiInThetaTop.
  Case "eff_concat".
    inversion H0; subst.
    apply PTS_Seq. 
    SCase "lacts ⊑ eff".
      inversion H; subst. 
      apply PhiInThetaTop.  
    SCase "racts ⊑ eff".    
      inversion H; subst.
      apply PhiInThetaTop. 
Admitted.