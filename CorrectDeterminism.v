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
     
      (* Start the proof of the "type soundness" part *) 
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
            { inversion HBt as [ | | | |  
                                 | ? ? ? ? ? ? ? ? ? ? ? ? TcExp_ef TcExp_ea HBt_ef HBt_ea HR_ef HR_ea 
                                 | | | | | | | | |
                                 ]; subst.
              SSSCase "Mu_App ef ea0 << Eff_App ef ea0". 
              inversion HEff; subst.  
              assert (facts  ⊑ eff)
                by (eapply IHBS1_1 with (h_:=h'') (p_:=facts); eauto using  HFacts.Equal_refl).  
              assumption. 
            }
            exact H_.    
      SSCase " aacts ⊑ eff".   
        inversion HBt as [ | | | |  
                           | ? ? ? ? ? ? ? ? ? ? ? ? TcExp_ef TcExp_ea HBt_ef HBt_ea HR_ef HR_ea 
                           | | | | | | | | |
                            ]; subst.
        SSSCase "Mu_App ef ea0 << Eff_App ef ea0". 
          assert (H_ : aacts  ⊑ eff).
          { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts) in HR_ef. 
            - apply ReadOnlyTracePreservesHeap_1 in BS1_1. 
              + symmetry in BS1_1.
                inversion HEff; subst. 
                assert (H_ : aacts  ⊑ eff)
                  by (eapply IHBS1_2 with (h_:=h'') (p_:=aacts); eauto using  HFacts.Equal_refl).
                exact H_. 
              + assumption.   
            - assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, facts)) by
                  (eapply eff_sound; eauto). 
              eassumption. 
          }
          exact H_.  
      SSCase "bacts ⊑ eff".       
        inversion HEff; subst; 
        inversion HBt as [ | | | |  
                           | ? ? ? ? ? ? ? ? ? ? ? ? TcExp_ef TcExp_ea HBt_ef HBt_ea HR_ef HR_ea 
                           | | | | | | | | | 
                           ]; subst. 
        SSSCase "Mu_App ef ea0 << Eff_App ef ea0".
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
          
          assert (HD: facts  ⊑ eff /\
                      H.Equal h'' h'' 
                      /\  Cls (env', rho', Mu f x ec' ee') = Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0)
                      /\ facts = facts0).
          eapply  IHBS1_1  with (h_:=h''); eauto.
          rewrite HEq_1. reflexivity. 
          apply HFacts.Equal_refl.
          destruct HD as [A [HeqHeap [HEqCls HEqfacts]]].  symmetry in HEqCls.   inversion HEqCls; subst. 
          
          assert (HD' : aacts  ⊑ eff /\  H.Equal h'' h'' /\ v0 =  v' /\ aacts =  aacts0) by
              (eapply IHBS1_2; eauto; inversion HRonly as [ | | ? ? A B | ]; inversion B; assumption).
          destruct HD' as [A_ [B [C D]]]; symmetry in C, D; subst.
          
          assert (H_ : bacts  ⊑ eff). 
          { eapply IHBS1_3
            with (stty:=sttya) 
                   (ee:= ee') 
                   (h'':= h''); eauto.
            - eapply ext_stores__bt; eauto. 
            - inversion HRonly; subst. assumption.
            - { apply update_env; simpl.  
                - eapply ext_stores__env; eauto. 
                  apply update_env.  
                  + eassumption.
                  + eapply ext_stores__val with (stty:=sttyb); eauto.
                - eapply ext_stores__val with (stty:=sttya); eauto. }
            - eapply ext_stores__exp; eauto. 
          } 
          exact H_.
      } 
      (* Start the proof of the "determinism" part *) 
      { inversion BS2; subst. 
        inversion HBt as [ | | | |  
                           | ? ? ? ? ? ? ? ? ? ? ? ? TcExp_ef TcExp_ea HBt_ef HBt_ea HR_ef HR_ea 
                           | | | | | | | | | 
                            ]; subst. 
        - inversion HEff; subst.
          inversion HRonly as [ | | ? ? A B | ]; inversion A.

          assert ( RH1 : H.Equal fheap fheap0 /\ Cls (env', rho', Mu f x ec' ee') = 
                                           Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0) /\ facts = facts0 ).
          eapply IHBS1_1; eauto.
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
          { eapply IHBS1_2 with (p':=Phi_Seq (Phi_Seq facts1 aacts1) bacts1); eauto.
            - rewrite HEq_1. eassumption.
            - rewrite HEq_1. eassumption. } 
          destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]; subst. 
          assert ( RH3 : H.Equal h' h'_ /\ v = v_ /\ bacts = bacts0).
          { eapply IHBS1_3 with (ee:=ee'0) (stty:=sttya)  (h'':=aheap) (p':=bacts1); eauto.
            - eapply EvaluationMuAppIncludesEffectEvaluation; eauto.
            - eapply ext_stores__bt; eauto.
            - { apply update_env; simpl.  
                - eapply ext_stores__env; eauto. 
                  apply update_env.  
                  + eassumption.
                  + eapply ext_stores__val with (stty:=sttyb); eauto.
                - eapply ext_stores__val with (stty:=sttya); eauto. }
            - eapply ext_stores__exp; eauto. } 
          destruct RH3 as [h_eq_3 [v_eq_3 a_eq_3]]; subst.
          auto.
      }   
  Case "rgn_app". 
    (* Start the proof of the "type soundness" part *) 
    inversion HExp as  [ | | | | | 
                           | ? ? ? ? ? ? ? ? HTcExp_er HTcRgn_w 
                           | | | | | | | | | | | | | | | | | |]; subst.
    assert (clsTcVal : exists stty',  
                         (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
                         /\ TcHeap (fheap, stty')
                         /\ TcVal (stty', Cls (env', rho', Lambda x eb), 
                                   subst_rho rho (Ty2_ForallRgn effr tyr))). 
    eapply ty_sound;eauto. 
    destruct clsTcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
    
    inversion TcVal_cls as [ | | | 
                             ? ? ? ? ? ? ? TcRho_rho' TcEnv_env' TcExp_abs [A B C D HSubst] 
                             | | |]; subst. 
    inversion TcExp_abs as [ | | | |
                             ? ? ? ? ? ? ? HNo HLc1 HLc2 HBt_eb HTExp_eb
                             | | | | | | | | | | | | | | | | | | | |]; subst.
    rewrite <- HSubst in TcVal_cls.
    do 2 rewrite subst_rho_forallrgn in HSubst.
    inversion HSubst as [[H_fold A]]; clear A.

    (* left part of the conjunction *)
    assert (HSOUND : Phi_Seq facts bacts ⊑ eff). 
    {
      apply PTS_Seq.
      SCase "facts ⊑ eff".
        eapply IHBS1_1 with (h_:=h); eauto. apply HFacts.Equal_refl. 
        inversion HBt; subst; eauto.
      SCase " bacts ⊑ eff".
        inversion HBt; subst.
        SSCase "Rgn_App er w << (∅)". 
          { eapply IHBS1_2 with (ee:=∅); eauto. 
            - inversion HEff; subst. econstructor.
            - inversion HEff; subst. econstructor. 
            - apply update_rho; auto.
            - eapply extended_rho; eauto. 
          }
    }      
    (* start the proof of the "determinism" part *)
    inversion BS2; subst. 
    { assert ( RH1 : H.Equal fheap fheap0 /\  Cls (env', rho', Lambda x eb) =
                                              Cls (env'0, rho'0, Lambda x0 eb0) /\ facts = facts0 ).
      { eapply IHBS1_1; eauto.
        inversion HBt as [ | | | | | ? ? ? ? ? ? ? ? ? ? ? ? TcExp_ef TcExp_ea HBt_ef HBt_ea HR_ef HR_ea 
                           | | ? ? ? ? ? ? ? ? TcExp_er TcExp_ HBt_ | | | | | | |]; subst.  
        - assumption. 
      }
      destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
      rewrite H in H9. inversion H9; subst.
      
      assert ( RH2 : H.Equal h' h'_ /\ v = v_ /\ bacts = bacts0).
      { eapply IHBS1_2 with (h'':=fheap) (eff:=Some empty_set) (p':=Phi_Nil); eauto. 
        - constructor.
        - constructor.
        - apply update_rho; auto.
        - eapply extended_rho; eauto. }
      
      destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. subst.
      intuition.    
    }
  Case "eff_app".

      (* Start the proof of the "type soundness" part *) 
      inversion HExp as  [ | | | | | | | 
                           ? ? ? ? ? ? ? ? ? ? ? HExp_ef HExp_ea 
                           | | | | | | | | | | | | | | | | | ]; subst.
      assert (clsTcVal : exists stty',  
                           (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
                           /\ TcHeap (h', stty')
                           /\ TcVal (stty', 
                                     Cls (env', rho', Mu f x ec' ee'), 
                                     subst_rho rho (Ty2_Arrow tya effc tyc  effe Ty2_Effect))) 
        by (eapply ty_sound; eauto).
      destruct clsTcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
      
      assert (argTcVal : exists stty',
                           (forall l t', ST.find l sttyb = Some t' -> ST.find l stty' = Some t')
                           /\ TcHeap (h', stty')
                           /\ TcVal (stty', v', subst_rho rho tya))
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

      (*  left part of the conjunction *)
      assert (HSOUND : Phi_Seq (Phi_Seq facts aacts) bacts ⊑ eff).
      inversion HBt; subst.   
      
      (* start the proof of the "determinism" part *)
      inversion HBt; subst.
      
  Case "par_pair".
    (* Start the proof of the "effect soundness" part *) 
    
    (* left part of the conjunction *)
    assert (HSOUND :  Phi_Seq (Phi_Par acts_eff1 acts_eff2) (Phi_Par acts_mu1 acts_mu2) ⊑ eff).
    inversion HBt as [ | | | |  
                       | ? ? ? ? ? ? ? ? ? ? ? ? TcExp_ef TcExp_ea HBt_ef HBt_ea HR_ef HR_ea 
                       | ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? A B C D HBt_a HBt_b HBt_c HBt_d 
                       | | | | | | | | ]; subst; 
    inversion HEff; subst. 
     
    clear H2. clear H3.  
    clear H. clear H0.
     
    inversion HExp as  [ | | | | | ? ? ? ? ? ? ? ? ? ? ? HExp_ef HExp_ea 
                               | | | 
                               ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? HBt_1 HBt_2 HExp_mu1 HExp_mu2 HExp_eff1 HExp_eff2 
                               | | | | | | | | | | | | | | | | ]; subst.  
    inversion HEff; subst. inversion H2; subst. inversion H12; subst.

    assert (H' : acts_eff1 ⊑ effa1).
    { eapply IHBS1_1; eauto.
      + { assert (HEq_1 : h'' = h_).
          assert (H.Equal h'' h'') by (apply HFacts.Equal_refl).
          eapply EquivalenceUpToPermutations; eauto. 
          rewrite <- HEq_1. eassumption. }
      + inversion HRonly as [ | | ? ? X Y | ]; inversion X; inversion Y; assumption. }
    assert (H'' : acts_eff2 ⊑ effb1).
    { eapply IHBS1_2; eauto.
      + { assert (HEq_1 : h'' = h_).
          assert (H.Equal h'' h'') by (apply HFacts.Equal_refl).
          eapply EquivalenceUpToPermutations; eauto. 
          rewrite <- HEq_1. eassumption. }
      + inversion HRonly as [ | | ? ? X Y | ]; inversion X; inversion Y; assumption. }
    assert (H''' : acts_mu1 ⊑ effa0).
    { eapply IHBS1_3; eauto.
      + { assert (HEq_1 : h'' = h_).
          assert (H.Equal h'' h'') by (apply HFacts.Equal_refl).
          eapply EquivalenceUpToPermutations; eauto. 
          rewrite <- HEq_1. eassumption. }
      + inversion HRonly as [ | | ? ? X Y | ]; inversion X; inversion Y; assumption. }
    assert (H'''' : acts_mu2 ⊑ effb2).
    { eapply IHBS1_4; eauto.
      + { assert (HEq_1 : h'' = h_).
          assert (H.Equal h'' h'') by (apply HFacts.Equal_refl).
          eapply EquivalenceUpToPermutations; eauto. 
          rewrite <- HEq_1. eassumption. }
      + inversion HRonly as [ | | ? ? X Y | ]; inversion X; inversion Y; assumption. }
    
    assert (H_ : (Phi_Par acts_eff1 acts_eff2) ⊑ (Union_Theta effa1 effb1)). 
    apply PTS_Par; [ apply Theta_introl | apply Theta_intror ]; eauto.

    assert (H__ : (Phi_Par acts_mu1 acts_mu2) ⊑ (Union_Theta effa0 effb2)). 
    apply PTS_Par; [ apply Theta_introl | apply Theta_intror ]; eauto.

    assert (_H__ :  ReadOnlyPhi acts_eff1).
    { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:= acts_eff1) in B; auto.
      assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ee_1, acts_eff1)) by
          (eapply eff_sound; eauto). 
      assumption. }
    
    assert (_H_ : acts_mu1 ⊑ theta1). 
     { induction theta1; [| apply PhiInThetaTop].
      eapply IHBS1_3; eauto.
      + assert (HEq_1 : h'' = h_).
        assert (H.Equal h'' h'') by (apply HFacts.Equal_refl).
        eapply EquivalenceUpToPermutations; eauto. 
        rewrite <- HEq_1. eassumption. } 

    assert (_H____ :  ReadOnlyPhi acts_eff2).
    { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:= acts_eff2) in D; auto.
      assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ee_2, acts_eff2)) by
          (eapply eff_sound; eauto). 
      assumption. }

    assert (_H___ : acts_mu2 ⊑ theta2).
    { induction theta2; [| apply PhiInThetaTop].
      eapply IHBS1_4; eauto.
      + assert (HEq_1 : h'' = h_).
        assert (H.Equal h'' h'') by (apply HFacts.Equal_refl).
        eapply EquivalenceUpToPermutations; eauto. 
        rewrite <- HEq_1. eassumption. } 
    apply PTS_Seq. 
    apply  Theta_introl. assumption.
    apply Theta_intror. assumption.

    (* start the proof of the "determinism" part *)
    inversion BS2; subst.
    { inversion HBt as [ | | | |  
                       | ? ? ? ? ? ? ? ? ? ? ? ? TcExp_ef TcExp_ea HBt_ef HBt_ea HR_ef HR_ea 
                       | ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? A B C D HBt_a HBt_b HBt_c HBt_d 
                       | | | | | | | | ]; subst.
      inversion HExp as  [ | | | | | ? ? ? ? ? ? ? ? ? ? ? HExp_ef HExp_ea 
                           | | | 
                           ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? HBt_1 HBt_2 HExp_mu1 HExp_mu2 HExp_eff1 HExp_eff2 
                           | | | | | | | | | | | | | | | | ]; subst.
      inversion HEff; subst. inversion HEff; subst. inversion H28; subst.  inversion H9; subst.
      
      clear H18. clear H19. clear H23. clear H24.
      clear H. clear H0. clear H2. clear H3.
      assert (HR1 : H.Equal h'' h_ /\ Eff theta1 = Eff theta0 /\ acts_eff1 = acts_eff0). 
      
      { eapply IHBS1_1 with (ee:=eff1); eauto.
        inversion HRonly as [ | | ? ? X Y | ]; inversion X; inversion Y; assumption. }   
      destruct HR1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
      
      assert (HR2 : H.Equal h'' h_ /\ Eff theta2 = Eff theta3 /\ acts_eff2 = acts_eff3). 
      { eapply IHBS1_2 with (ee:=eff2); eauto.
        inversion HRonly as [ | | ? ? X Y | ]; inversion X; inversion Y; assumption. }
      destruct HR2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2. subst.
      
      assert (HR3 : H.Equal heap_mu1 heap_mu0 /\ Num v1 = Num v0 /\ acts_mu1 = acts_mu0).  
      { inversion HExp; subst.
        eapply IHBS1_3 with (ee:=eff3) (ty:=ty1) (static:=eff0); eauto.   
        inversion HRonly as [ | | ? ? X Y | ]; inversion X; inversion Y; assumption.
      }
      inversion HR3 as [h_eq_3 [v_eq_3 a_eq_3]]. inversion v_eq_3; subst.
      
      assert (HR4 : H.Equal heap_mu2 heap_mu3 /\ Num v2 = Num v3 /\ acts_mu2 = acts_mu3).  
      { inversion HExp; subst.
        eapply IHBS1_4 with (ee:=eff4); eauto.
        inversion HRonly as [ | | ? ? X Y | ]; inversion X; inversion Y; assumption. }
      inversion HR4 as [h_eq_4 [v_eq_4 a_eq_4]]. inversion v_eq_4. subst.
      split.
      - rewrite <- H13 in HSOUND.
        assumption.
      - inversion HEff; subst. rewrite <- H13 in HSOUND. 
        assert (_H__ :  ReadOnlyPhi acts_eff0).
        { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:= acts_eff0) in B; auto.
          assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ee_1, acts_eff0)) by
              (eapply eff_sound; eauto). 
          assumption. }
        
        assert (_H_ : acts_mu0 ⊑ theta0). 
        { induction theta0; [| apply PhiInThetaTop].
          eapply IHBS1_3; eauto. }
        
        assert (_H____ :  ReadOnlyPhi acts_eff3).
        { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:= acts_eff3) in D; auto.
          assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ee_2, acts_eff3)) by
              (eapply eff_sound; eauto). 
          assumption. }
        
        assert (_H___ : acts_mu3 ⊑ theta3).
        { induction theta3; [| apply PhiInThetaTop].
          eapply IHBS1_4; eauto. } 
        
        intuition. 
        eapply unique_heap_new with (heapa := h'') (heapb := h_) (theta1:=theta0) (theta2:=theta3); eauto.
        + assert (Det_Trace (Phi_Par acts_mu0 acts_mu3))
            by (eapply Det_trace_from_theta; eauto; 
                [ apply Dynamic_DetTrace in BS1_3 | apply Dynamic_DetTrace in BS1_4]; assumption).
          inversion H18. assumption.
        + assert (Det_Trace (Phi_Par acts_mu0 acts_mu3))
            by (eapply Det_trace_from_theta; eauto; 
                [ apply Dynamic_DetTrace in BS1_3 | apply Dynamic_DetTrace in BS1_4]; assumption).
        inversion H18. assumption. 
    }
  Case "cond_true".
   (* left part of the conjunction *)
    assert (HSOUND :  Phi_Seq cacts tacts ⊑ eff).
    { inversion HBt as [ | | | | | | |   
                       | ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? 
                           TcExp_e TcExp_et TcExp_ef HBt_e HBt_et HBt_ef
                       | | | | | | ]; subst. 
      - assert (H' : cacts ⊑ Some empty_set).
        { eapply IHBS1_1 with (h_:=h) (p':=Phi_Nil); eauto. 
          - apply HFacts.Equal_refl. 
          - constructor.
          - constructor. } 
        
        apply EmptyUnionIsIdentity.
        apply EmptyIsNil in H'. subst. 
        apply PTS_Seq; [apply PTS_Nil |].

        assert (HEq_1 :  cheap = h).
        { apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
          assumption.
          constructor. }

        rewrite UnionEmptyWithEffIsEff.
        
        (*assert (ef_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e, Phi_Nil)) by
            (eapply eff_sound; eauto).      
        assert (HEq_1 :  cheap = h). 
        { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=Phi_Nil) in HR.
          - apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
            assumption. constructor. 
          - eassumption. } *)
        
        { eapply IHBS1_2 with (ee:=efft)  (h_:=h) ; eauto.
          - apply Equal_heap_equal. auto.
          - subst. eassumption.
          - eapply EvalTrueIsTrue; eauto. 
          - subst. assumption. }
      -  inversion HEff; subst.
         apply PhiInThetaTop. 
    }
    (* start the proof of the "determinism" part *) 
    { inversion BS2; subst.
      inversion HExp; subst.
      assert (bitVal : exists stty',  
                         (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
                         /\ TcHeap (cheap0, stty')
                         /\ TcVal (stty', 
                                   Bit true, 
                                   subst_rho rho Ty2_Boolean)). 
      eapply ty_sound; eauto using EqualHeaps.
      destruct bitVal as [sttyb [Weakb [TcHeapb TcVal_bit]]]; eauto.

      - inversion HBt as [ | | | | | | |   
                         | ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? 
                             TcExp_e TcExp_et TcExp_ef HBt_e HBt_et HBt_ef
                         | | | | | | ]; subst.
        + assert ( RH1 : H.Equal cheap cheap0 /\  Bit true = Bit true /\ cacts = cacts0 )
            by (eapply IHBS1_1 with (ee:=∅) (p':=Phi_Nil); eauto; econstructor).
          destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. subst.
          
          assert (H' : cacts0 ⊑ Some empty_set).
          { eapply IHBS1_1 with (h_:=h) (p':=Phi_Nil); eauto. 
            - apply HFacts.Equal_refl. 
            - constructor.
            - constructor. } 
          apply EmptyIsNil in H'. subst.  
          
          assert ( RH2 : H.Equal h' h'_ /\ v = v_ /\ tacts = tacts0 ).
          { eapply IHBS1_2 ; eauto.
            - eapply EvalTrueIsTrue; eauto. 
            - apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
              subst. assumption.  constructor. }
          destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. subst.
          intuition.
        + induction eff; inversion HEff; subst. 
      
          assert ( RH1 : H.Equal cheap cheap0 /\  Bit true = Bit true /\ cacts = cacts0 ). 
          eapply IHBS1_1 ; eauto; econstructor.
          destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. subst.
           
          assert ( RH2 : H.Equal h' h'_ /\ v = v_ /\ tacts = tacts0 ). 
          { eapply IHBS1_2 with (ee:=⊤) (stty:=sttyb) (p':=Phi_Nil); 
            eauto using ext_stores__env, ext_stores__exp, ext_stores__bt.   
            - econstructor.
            - symmetry in h_eq_1. eapply EqualHeaps; eauto. }
          destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. subst.
          intuition.         
        
      - inversion HExp; subst. 
        assert ( RH1: H.Equal cheap cheap0 /\ Bit true = Bit false /\ cacts = cacts0). 
        eapply IHBS1_1  with (ee:=⊤) (p':=Phi_Nil); eauto; econstructor. 
        destruct RH1 as [? [D ?]]. discriminate D. 
    }
  Case "cond_false".
    admit.
  Case "new_ref e".
    admit.
  Case "get_ref e". 
    (* left part of the conjunction *)
    assert (HSOUND : Phi_Seq aacts (Phi_Elem (DA_Read r l v)) ⊑ eff ).
    { inversion HBt as [ | | | | | | |   
                       | ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TcExp_e TcExp_et TcExp_ef HBt_e HBt_et HBt_ef | 
                       | ? ? ? ? ? ? ? ? ? TcExp_ea0 HBt_ea0 | 
                       | | | ]; subst. 
      - inversion HEff; subst. 
        apply EnsembleUnionComp.
        + eapply IHBS1 with (h_:=h''); eauto using HFacts.Equal_refl.  
          inversion HRonly; subst. assumption.
        + apply PTS_Elem. inversion H10; subst.
          rewrite H in H2; inversion H2.
          apply DAT_Read_Abs. apply In_singleton.  
      - inversion HEff; subst.
        assert (aacts ⊑ Some empty_set). 
        eapply IHBS1 with (h_:=h); eauto using HFacts.Equal_refl; constructor.
        apply PTS_Seq.
        + apply EmptyInAnyTheta. assumption.
        + apply PTS_Elem.
          simpl in H; inversion H; subst.  
          assert (HD: H.Equal h' h'' /\  
                      Loc (Rgn2_Const true false r) l = Loc (Rgn2_Const true false r1) l0 /\ 
                      aacts  = Phi_Nil ).
          eapply IHBS1 with (h_:=h) (ee:=∅); eauto using HFacts.Equal_refl; constructor.
          destruct HD as [? [H_ ?]]; inversion H_; subst.
          apply DAT_Read_Conc. apply In_singleton.
      - econstructor; inversion HEff; subst; apply PhiInThetaTop.
    }  
    (* start the proof of the "determinism" part *) 
    { inversion BS2; subst.
      inversion HExp; subst. 
      
      inversion HBt as [ | | | | | | |   
                       | ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TcExp_e TcExp_et TcExp_ef HBt_e HBt_et HBt_ef | 
                       | ? ? ? ? ? ? ? ? ? TcExp_ea0 HBt_ea0 | 
                       | | | ]; subst. 
      - inversion HEff; subst.
        assert ( RH1 : H.Equal h' h'_ /\  
                       Loc (Rgn2_Const true false s) l =  Loc (Rgn2_Const true false s) l0 /\ 
                       aacts = aacts0 ) 
          by (eapply IHBS1 with (ee:=eff0); eauto; inversion HRonly; assumption).
        destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. 
        inversion v_eq_1.
        assert (H_ : forall k, find_H k h' = find_H k h'_)
          by (unfold find_H, update_H; simpl; intro; apply HFacts.find_m; intuition).
         rewrite H_ in H0.
         simpl in H10. inversion H10. 
         simpl in H. inversion H.
         subst. rewrite H6 in H11.
         rewrite H11 in H0.
         inversion H0; subst.
         intuition.
      -  inversion HEff; subst.
         assert ( RH1 : H.Equal h' h'_ /\  
                       Loc (Rgn2_Const true false s) l =  Loc (Rgn2_Const true false s) l0 /\ 
                       aacts = aacts0 ) 
           by (eapply IHBS1 with (ee:=∅); eauto; econstructor).
         destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1; subst.
         assert (H_ : forall k, find_H k h' = find_H k h'_)
           by (unfold find_H, update_H; simpl; intro; apply HFacts.find_m; intuition).
         rewrite H_ in H0.
         simpl in H10, H. inversion H; inversion H10; subst.
         rewrite H7 in H0. rewrite H11 in H0.
         inversion H0; subst.
         intuition.
      -  inversion HEff; subst.
         assert ( RH1 : H.Equal h' h'_ /\  
                       Loc (Rgn2_Const true false s) l =  Loc (Rgn2_Const true false s) l0 /\ 
                       aacts = aacts0 ) 
           by (eapply IHBS1 with (ee:=⊤); eauto; econstructor).
         destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1; subst.
         assert (H_ : forall k, find_H k h' = find_H k h'_)
           by (unfold find_H, update_H; simpl; intro; apply HFacts.find_m; intuition).
         rewrite H_ in H0.
         simpl in H10, H. inversion H; inversion H10; subst. 
         rewrite H3 in H0. rewrite H11 in H0.
         inversion H0; subst.
         intuition.
    }
  Case "set_ref e1 e2".
    (* left part of the conjunction *)
    assert (HSOUND : Phi_Seq (Phi_Seq aacts vacts) (Phi_Elem (DA_Write r l v0)) ⊑ eff ).
    { inversion HBt as [| | | | | | | | | | |
                      | ? ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                      | ? ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                      | ]; subst. 
      SCase "Assign w ea0 ev << (eff1 ⊕ (eff2 ⊕ WriteAbs w))".
        inversion HEff; subst.
        apply PTS_Seq. 
        SSCase "Phi_Seq aacts vacts ⊑ Union_Theta effa effb".
          apply EnsembleUnionComp.
          SSSCase "aacts ⊑ effa".
            inversion HExp; subst.
            eapply IHBS1_1 with (h_:=h''); eauto using HFacts.Equal_refl. 
            inversion HRonly; subst. assumption.
          SSSCase "vacts ⊑ effb". 
            inversion HEff; subst. 
            inversion H9; subst.
            inversion HExp; subst.
            
            assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e1, aacts)) by
                (eapply eff_sound; eauto). 
            assert (HEq_1 : heap' = h'').   
            eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=aacts) in HR.
            { apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
              - assumption. 
              - assumption. } 
            exact facts_Eff. 
            
            assert (vacts ⊑ effa1). 
            { eapply IHBS1_2 with (p':= phia0); eauto using HFacts.Equal_refl.  
              - rewrite HEq_1. eassumption.
              - inversion HRonly as [ | | ? ? X Y | ]; inversion X; inversion Y; assumption.
              - rewrite HEq_1. assumption. }
            apply Theta_introl. assumption.
        SSCase "Phi_Elem (DA_Write r l v0) ⊑ Union_Theta effa effb".    
          inversion H9; subst. 
          assert (Phi_Elem (DA_Write r l v0) ⊑ effb0).
          apply PTS_Elem. inversion H10; subst.
          rewrite H in H1. inversion H1; subst.
          apply DAT_Write_Abs; apply In_singleton.
          apply Theta_intror. apply Theta_intror. 
          assumption.
      SCase " Assign (Rgn2_Const true false r0) ea0 ev << (eff1 ⊕ (eff2 ⊕ WriteConc ea0))".
         inversion HEff; subst. 
         apply PTS_Seq.
         SSCase "Phi_Seq aacts vacts ⊑ Union_Theta effa effb".
           apply EnsembleUnionComp.
           SSSCase "aacts ⊑ effa".
             inversion HExp; subst.
             eapply IHBS1_1 with (h_:=h'');  eauto using HFacts.Equal_refl.  
             inversion HRonly; subst. 
             assumption.
           SSSCase "vacts ⊑ effb". 
             inversion HExp; subst. 
             inversion H13; subst. 
             inversion H9; subst.

             assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e1, aacts)) by
                 (eapply eff_sound; eauto). 
             assert (HEq_1 : heap' = h''). 
             { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=aacts) in HR.
               - apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
                 assumption. assumption. 
               - eassumption. }
             
             assert (vacts ⊑ effa0). 
             { eapply IHBS1_2 with (p':= phia0);  eauto using HFacts.Equal_refl.     
               - rewrite HEq_1. eassumption.
               - inversion HRonly as [ | | ? ? X Y | ]; inversion X; inversion Y; assumption.
               - rewrite HEq_1. assumption. }
             apply Theta_introl. assumption. 
        SSCase "Phi_Elem (DA_Write r l v0) ⊑ Union_Theta effa effb".
          inversion H9; subst. 
          assert (Phi_Elem (DA_Write r l v0) ⊑ effb0).
          apply PTS_Elem. inversion H10; subst.   
          assert (HD: H.Equal heap' h'' /\  Loc (Rgn2_Const true false r0) l =
                                            Loc (Rgn2_Const true false r1) l0 /\ aacts = Phi_Nil)
            by (eapply IHBS1_1 with (h_:=h'') (ee:=eff1); eauto using HFacts.Equal_refl;
                inversion HRonly; assumption).
          destruct HD as [? [H_ ?]]; inversion H_; subst.
          inversion H; subst.
          apply DAT_Write_Conc; apply In_singleton.
          apply Theta_intror. apply Theta_intror. assumption.
      SCase "Assign w ea0 ev << (⊤)".
        inversion HEff; subst.   
        apply PhiInThetaTop.
    }
    (* start the proof of the "determinism" part *) 
    { inversion BS2; subst.
      inversion HExp; subst. 
      
      inversion HBt as [| | | | | | | | | | |
                      | ? ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                      | ? ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                      | ]; subst. 
      - inversion HEff; subst. 
        inversion H15; subst.
        
        assert ( RH1 : H.Equal heap' heap'0 /\  
                       Loc (Rgn2_Const true false s) l = Loc (Rgn2_Const true false s) l0 /\ 
                       aacts = aacts0 ). 
        eapply IHBS1_1 with (ee:=eff1); eauto. inversion HRonly. assumption.
        destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1.
        assert ( RH2 : H.Equal heap'' heap''0 /\ v0 = v /\ vacts = vacts0 ). 
        eapply IHBS1_2 with (eff:=effa0) (p':=phia0); eauto.
        assert (HEq_1 : h'' = heap') by admit.
        rewrite <- HEq_1. eassumption.
        inversion HRonly as [ | | ? ? A B | ]; inversion B; assumption.
        assert (HEq_1 : h'' = heap') by admit.
        rewrite <- HEq_1. assumption.
        destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2.
        rewrite H in H11; inversion H11; subst. 
        intuition.
        unfold update_H; simpl. apply HMapP.add_m; auto. 
      - inversion HEff; inversion H15; subst.
         assert ( RH1 : H.Equal heap' heap'0 /\  
                       Loc (Rgn2_Const true false s) l = Loc (Rgn2_Const true false s) l0 /\ 
                       aacts = aacts0 ). 
         eapply IHBS1_1 with (ee:=eff1); eauto. inversion HRonly. assumption.
         destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1.
         assert ( RH2 : H.Equal heap'' heap''0 /\ v0 = v /\ vacts = vacts0 ). 
         eapply IHBS1_2 with (eff:=effa0) (p':=phia0); eauto.
         assert (HEq_1 : h'' = heap') by admit.
         rewrite <- HEq_1. eassumption.  
         inversion HRonly as [ | | ? ? A B | ]; inversion B; assumption.
         assert (HEq_1 : h'' = heap') by admit.
         rewrite <- HEq_1. assumption.
         destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2.
         rewrite H in H11; inversion H11; subst. 
         intuition.
         unfold update_H; simpl. apply HMapP.add_m; auto. 
        
      - inversion HEff; subst. 
        assert ( RH1 : H.Equal heap' heap'0 /\  
                       Loc (Rgn2_Const true false s) l = Loc (Rgn2_Const true false s) l0 /\ 
                       aacts = aacts0 ). 
         eapply IHBS1_1 with (ee:= ⊤); eauto; constructor.
         destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1.
         assert ( RH2 : H.Equal heap'' heap''0 /\ v0 = v /\ vacts = vacts0 ). 
         eapply IHBS1_2 ; eauto.
         + assert (HEq_1 : h'' = heap') by admit.
           rewrite <- HEq_1. eassumption. 
         + constructor.
         + assert (HEq_1 : h'' = heap') by admit.
           rewrite <- HEq_1. eassumption. 

         + intuition.  
           * apply PhiInThetaTop.
           * unfold update_H; simpl. apply HMapP.add_m; auto.
             rewrite H in H11. inversion H11; auto.
           * rewrite H in H11. inversion H11; subst.
             reflexivity.
    }
  Case "nat_plus x y".
    (* left part of the conjunction *)
    assert (HSOUND : (Phi_Seq racts lacts) ⊑ eff ).
    { inversion HBt; subst.
      apply PTS_Seq. 
      SCase "lacts ⊑ eff".
        inversion HEff; subst. 
        apply PhiInThetaTop.  
      SCase "racts ⊑ eff".    
        inversion HEff; subst.
        apply PhiInThetaTop. }
    (* start the proof of the "determinism" part *) 
    { inversion BS2; subst.
      inversion HExp; subst.  
      inversion HBt as [| | | | | | | | | | |
                      | ? ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                      | ? ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                      | ]; subst.
      inversion HEff; subst.
      assert ( RH1 : H.Equal lheap lheap0 /\  Num va = Num va0 /\ lacts = lacts0 ). 
      eapply IHBS1_1; eauto. constructor.  
      destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
      assert ( RH2 : H.Equal h' h'_ /\ Num vb = Num vb0 /\ racts = racts0 ). 
      eapply IHBS1_2; eauto.
      - assert (HEq_1 : h'' = lheap) by admit.
        rewrite <- HEq_1. eassumption.
      - constructor. 
      - assert (HEq_1 : h'' = lheap) by admit.
        rewrite <- HEq_1. eassumption. 
      - intuition.
        * apply PhiInThetaTop.
        * inversion H3; subst.
          reflexivity.
        * subst. reflexivity. }
    intuition.
  Case "nat_minus x y".    
Admitted.
