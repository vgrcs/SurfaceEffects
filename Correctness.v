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
Require Import Keys.
Require Import Heap.
Require Import EffectSystem.
Require Import Environment.
Require Import TypeSystem.
Require Import Determinism.
Require Import Definitions.
Require Import CorrectnessLemmas.

Import TypeSoundness.
Import EffectSoundness.

 
Axiom BackTriangle_intror : 
  forall stty ctxt rgns e effa effb,
    BackTriangle (stty, ctxt, rgns, e, effa) ->
    BackTriangle (stty, ctxt, rgns, e, effa ⊕ effb).

Axiom BackTriangle_introl : 
  forall stty ctxt rgns e effa effb,
    BackTriangle (stty, ctxt, rgns, e, effa) ->
    BackTriangle (stty, ctxt, rgns, e, effb ⊕ effa).


Lemma EvalTrueIsTrue:
forall h env rho e efft efff eff tacts,
  (h, env, rho, Cond e efft efff) ⇓ (h, Eff eff, tacts) ->
  (h, env, rho, e) ⇓ (h, Bit true, Phi_Nil) ->
  (h, env, rho, efft) ⇓ (h, Eff eff, tacts).
Proof.
  intros.
  inversion H; subst. 
  - assert ( Hbit : (h, Bit true, Phi_Nil) = (cheap, Bit true, cacts) )
      by (eapply DynamicDeterminism; eauto); inversion Hbit; subst.
    now rewrite Phi_Seq_Nil_L.
  - assert ( Hbit : (h, Bit true, Phi_Nil) = (cheap, Bit false, cacts) )
      by (eapply DynamicDeterminism; eauto); inversion Hbit; subst.
Qed.

Lemma EvalFalseIsFalse:
forall h env rho e efft efff eff tacts,
  (h, env, rho, Cond e efft efff) ⇓ (h, Eff eff, tacts) ->
  (h, env, rho, e) ⇓ (h, Bit false, Phi_Nil) ->
  (h, env, rho, efff) ⇓ (h, Eff eff, tacts).
Proof.
  intros.
  inversion H; subst. 
  - assert ( Hbit : (h, Bit false, Phi_Nil) = (cheap, Bit true, cacts) )
      by (eapply DynamicDeterminism; eauto); inversion Hbit; subst.
  - assert ( Hbit : (h, Bit false, Phi_Nil) = (cheap, Bit false, cacts) )
      by (eapply DynamicDeterminism; eauto); inversion Hbit; subst.
    now rewrite Phi_Seq_Nil_L.
Qed.

Definition Correctness :
  forall h h' h'' env rho  p p' v eff stty ctxt rgns ea ee,
    (h, env, rho, ea) ⇓ (h', v, p) ->
    (h, env, rho, ee) ⇓ (h'', Eff eff, p') ->
    BackTriangle (stty, ctxt, rgns, ea, ee) ->
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
  dependent induction BS1;
  intros; try (solve [econstructor]).
  - try (solve [inversion H; subst; inversion_clear H0]).
    inversion_clear H5.
    assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
        by (eapply ty_sound; eauto).
      destruct clsTcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
   
      assert (argTcVal : exists stty',
             (forall l t', ST.find l sttyb = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (aheap, stty')
               /\ TcVal (stty', v0, subst_rho rho tya))
        by (eapply ty_sound; eauto using update_env, ext_stores__env, ext_stores__exp).
      destruct argTcVal as [sttya [Weaka [TcHeapa TcVal_v']]]; eauto.

      
      inversion TcVal_cls as  [ | | | ? ? ? ? ? ? ? TcRho_rho' TcEnv_env' TcExp_abs | | ]; subst. 
      inversion TcExp_abs as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | |  | | | | | | | | | | |  ]; subst.
      rewrite <- H11 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H11. inversion H11. 
      rewrite <- H12 in TcVal_v'.
 
      apply PTS_Seq. 
      + apply PTS_Seq. 
         * { eapply IHBS1_1; eauto. 
             inversion H0; subst.
             - now apply BackTriangle_intror.   
             - econstructor; eauto. }
        * { inversion H0; subst. 
            - eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts) in H28.
              apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1.
              eapply IHBS1_2; subst; eauto.
              + eapply ext_stores__bt; eauto.
                eapply BackTriangle_introl. 
                eapply BackTriangle_intror. 
                eassumption.
              + eapply ext_stores__env; eauto.
              + eapply ext_stores__exp; eauto.
              + assumption. 
              + assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, facts)).
                 eapply eff_sound; eauto. 
                 eassumption.
            - induction eff; inversion H.
              eapply IHBS1_2 with (h'':=fheap) (ee:=⊤) ; eauto. 
              + rewrite <- H21. econstructor. 
              + econstructor.
              + eapply ext_stores__env; eauto.
              + eapply ext_stores__exp; eauto. }
      + inversion H; subst; inversion H0; subst. 
        * { 
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
            
            inversion H24; subst.  
            inversion H34; subst.
            assert (HD: (h'', Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0), facts0) =
                        (h'', Cls (env', rho', Mu f x ec' ee'), facts))
              by (eapply DynamicDeterminism; eauto). inversion HD; subst.
 
            assert (HD' : (h'', v', aacts0) = (h'', v0, aacts))
              by (eapply DynamicDeterminism; eauto). inversion HD'; subst.  
 
            (*assert (facts  ⊑ effa0) by
              (eapply IHBS1_1 with (ee:=a); eauto; inversion H1; subst; assumption).

            assert (aacts  ⊑ effa2) by
              (eapply IHBS1_2 with (ee:=effa1) (p':=phia0); eauto;
              inversion H1; inversion H22; subst; assumption).*)

            assert (bacts  ⊑ effb0).
            eapply IHBS1_3
            with (stty:=sttya) 
                   (ee:= ee') 
                   (h'':= h'');  eauto.
            - eapply ext_stores__bt; eauto. 
            - inversion H1; subst. inversion H21; subst. inversion H33; subst. assumption.
            - { apply update_env; simpl.  
                - eapply ext_stores__env; eauto. 
                  apply update_env.  
                  + eassumption.
                  + eapply ext_stores__val with (stty:=sttyb); eauto.
                - eapply ext_stores__val with (stty:=sttya); eauto. }
            - eapply ext_stores__exp; eauto.
 
            - apply Theta_intror.  apply Theta_intror. assumption.
          }
        * { eapply IHBS1_3 with (stty:=sttya) (ee:=⊤); eauto.
            - econstructor.
            - econstructor.
            - { apply update_env; simpl.  
                - eapply ext_stores__env; eauto. 
                  apply update_env.  
                  + eassumption.
                  + eapply ext_stores__val with (stty:=sttyb); eauto.
                - eapply ext_stores__val with (stty:=sttya); eauto. }
            - eapply ext_stores__exp; eauto.
          }
  - inversion_clear H6; subst.    
    assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Lambda x eb), 
                         subst_rho rho (Ty2_ForallRgn effr tyr))). 
    eapply ty_sound;eauto. 
    destruct clsTcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
    inversion TcVal_cls as  [ | | | ? ? ? ? ? ? ? TcRho_rho' TcEnv_env' TcExp_abs | | ]; subst.  
    inversion TcExp_abs as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | |  | | | | | | | | | | |  ]; subst.
    rewrite <- H12 in TcVal_cls.
    do 2 rewrite subst_rho_forallrgn in H12.
    inversion H12.
    
    apply PTS_Seq.
    + eapply IHBS1_1; eauto. 
      inversion H1; subst.
      * assumption.
      * econstructor; eauto.
    + inversion H1; subst.
      { eapply IHBS1_2 with (ee:=∅); eauto. 
        inversion H0; subst. econstructor.
        apply update_rho; auto.
        eapply extended_rho; eauto. }
      { eapply IHBS1_2 with (ee:=⊤); eauto. 
        induction eff.
        - inversion H0. 
        -  inversion H0. econstructor. 
        - econstructor.
        - apply update_rho; auto.
        - eapply extended_rho; eauto. }
  - inversion H0; subst.  
    apply PTS_Seq.
    + apply PTS_Seq; inversion H; subst; apply PhiInThetaTop.
    + inversion H; apply PhiInThetaTop.
  - inversion H6; subst.
    apply PTS_Seq; inversion H5; subst; apply PhiInThetaTop.
  - inversion H0; subst. 
    + assert (cacts ⊑ Some empty_set) by
          (eapply IHBS1_1 with (p':=Phi_Nil); eauto; constructor).
      apply EmptyUnionIsIdentity.
      apply EmptyIsNil in H6; subst.
      apply PTS_Seq; [apply PTS_Nil |].
      assert (ef_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e, Phi_Nil)).
      eapply eff_sound; eauto.
      assert (HEq_1 :  cheap = h). 
      eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=Phi_Nil) in H16.
      apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
      assumption. constructor. eassumption.
      rewrite UnionEmptyWithEffIsEff. 
      eapply IHBS1_2 with (ee:=efft); eauto.
      * { eapply EvalTrueIsTrue; eauto. 
          - assert (h=h'').
            eapply  ReadOnlyTracePreservesHeap_1; eauto.
            rewrite <- H6 in H.
            rewrite HEq_1. rewrite HEq_1 in BS1_1.
            eassumption. 
          - rewrite <- HEq_1 in BS1_1. assumption. }
      * rewrite HEq_1. assumption.
    + inversion H; subst. constructor. apply PhiInThetaTop.  apply PhiInThetaTop.
  - inversion H0; subst. 
    + assert (cacts ⊑ Some empty_set) by 
          (eapply IHBS1_1 with (p':=Phi_Nil); eauto; constructor).
      apply EmptyUnionIsIdentity.
      apply EmptyIsNil in H6; subst.
      apply PTS_Seq; [apply PTS_Nil |].
      assert (ef_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e, Phi_Nil)).
      eapply eff_sound; eauto.
      assert (HEq_1 :  cheap = h). 
      eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=Phi_Nil) in H16.
      apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
      assumption. constructor. eassumption.
      rewrite UnionEmptyWithEffIsEff.
      eapply IHBS1_2 with (ee:=efff); eauto.
      * { eapply EvalFalseIsFalse; eauto. 
          - assert (h=h'').
            eapply  ReadOnlyTracePreservesHeap_1; eauto.
            rewrite <- H6 in H.
            rewrite HEq_1. rewrite HEq_1 in BS1_1.
            eassumption. 
          - rewrite <- HEq_1 in BS1_1. assumption. }
      * rewrite HEq_1. assumption.
    + inversion H; subst. constructor. apply PhiInThetaTop.  apply PhiInThetaTop.
  - inversion H1; subst; inversion H2; subst.
    apply EnsembleUnionComp.  
     + eapply IHBS1; eauto. inversion H3. assumption.
     + inversion H16; subst.
       apply PTS_Elem. apply DAT_Alloc_Abs.
       rewrite H in H9. inversion H9.
       apply In_singleton.
     + apply PhiInThetaTop.  
  - inversion H2; subst. 
    + inversion H1; subst. 
      apply EnsembleUnionComp.
      * eapply IHBS1; eauto. 
        inversion H3; subst. assumption.
      * apply PTS_Elem. inversion H19; subst.
        rewrite H in H9; inversion H9.
        apply DAT_Read_Abs. apply In_singleton.
    + inversion H1; subst.
      assert (aacts ⊑ Some empty_set) by (eapply IHBS1; eauto; constructor).
      apply PTS_Seq.
      * apply EmptyInAnyTheta. assumption.
      * apply PTS_Elem.
        simpl in H; inversion H; subst.
        assert ( HD : (h'', Loc (Rgn2_Const true false r1) l0, Phi_Nil) 
                      =  (h', Loc (Rgn2_Const true false r) l, aacts))
          by (eapply DynamicDeterminism; eauto). inversion HD; subst. 
        apply DAT_Read_Conc. apply In_singleton.
    + econstructor.  
      * inversion H1; subst.
        inversion H7; subst.
        eapply IHBS1; eauto.  econstructor. 
      * inversion H1; subst.    
        apply PTS_Elem. apply DAT_Top.
  - inversion H1; subst.
    + inversion H0; subst.
      apply PTS_Seq.
      * { apply EnsembleUnionComp.
          - inversion H6; subst.
            eapply IHBS1_1; eauto. 
            inversion H2; subst. assumption.
          - inversion H20; subst. inversion H6; subst.
            
            assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e1, aacts)).
            eapply eff_sound; eauto. 
            assert (HEq_1 : heap' = h'').   
            eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=aacts) in H17.
            apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
            assumption. assumption. eassumption.

            assert (vacts ⊑ effa0). 
            eapply IHBS1_2 with (p':= phia0); eauto.   
            + rewrite HEq_1. eassumption.
            + inversion H2; subst. inversion H13; subst. eassumption.
            + rewrite HEq_1. assumption.
            + apply Theta_introl. assumption. 
        }
      * inversion H20; subst. 
        assert (Phi_Elem (DA_Write r l v0) ⊑ effb0).
        apply PTS_Elem. inversion H21; subst.
        rewrite H in H8. inversion H8; subst.
        apply DAT_Write_Abs; apply In_singleton.
        apply Theta_intror. apply Theta_intror. assumption.
    + inversion H0; subst.
      apply PTS_Seq.
      * { apply EnsembleUnionComp.
          - inversion H6; subst.
            eapply IHBS1_1; eauto. 
            inversion H2; subst. assumption.
          - inversion H6; subst.
            inversion H20; subst.

            assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e1, aacts)).
            eapply eff_sound; eauto. 
            assert (HEq_1 : heap' = h''). 
            eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=aacts) in H17.
            apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
            assumption. assumption. eassumption.

            assert (vacts ⊑ effa0). 
            eapply IHBS1_2 with (p':= phia0); eauto.   
            + rewrite HEq_1. eassumption.
            + inversion H2; subst. inversion H14; subst. assumption.
            + rewrite HEq_1. assumption.
            + apply Theta_introl. assumption. 
        }
      * inversion H20; subst. 
        assert (Phi_Elem (DA_Write r l v0) ⊑ effb0).
        apply PTS_Elem. inversion H21; subst.
        assert ( HD : (heap', Loc (Rgn2_Const true false r0) l, aacts) 
                      =  (h'', Loc (Rgn2_Const true false r1) l0, Phi_Nil))
         by (eapply DynamicDeterminism; eauto). inversion HD; subst.
         inversion H; subst.
         apply DAT_Write_Conc; apply In_singleton.
         apply Theta_intror. apply Theta_intror. assumption.
    + inversion H0. 
      econstructor. 
      * inversion H6. 
        apply PTS_Seq.
        {  subst. eapply IHBS1_1; eauto. econstructor.  }
        { apply PhiInThetaTop.  }
      * econstructor. apply DAT_Top.
  - inversion H0; subst.
    apply PTS_Seq.
    + inversion H; subst.
      inversion H5; subst.
      eapply IHBS1_1; eauto.
      * econstructor.
    + inversion H. 
      apply PhiInThetaTop.        
  - inversion H0; subst.
    apply PTS_Seq.
    + inversion H; subst.
      inversion H5; subst.
      eapply IHBS1_1; eauto.
      * econstructor.
    + inversion H. 
      apply PhiInThetaTop. 
  - inversion H0; subst.
    apply PTS_Seq.
    + inversion H; subst.
      inversion H5; subst.
      eapply IHBS1_1; eauto.
      * econstructor.
    + inversion H. 
      apply PhiInThetaTop.
  - inversion H0; subst.
    apply PTS_Seq.
    + inversion H; subst.
      inversion H5; subst.
      eapply IHBS1_1; eauto.
      * econstructor.
    + inversion H. 
      apply PhiInThetaTop.
  - inversion H0; subst.
    apply PTS_Seq.
    + inversion H; subst.
      inversion H5; subst.
      eapply IHBS1_1; eauto.
      * econstructor.
    + inversion H. 
      apply PhiInThetaTop. 
Qed.