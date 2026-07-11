From stdpp Require Import gmap.
From stdpp Require Import strings.

Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Meta.Tactics.
Require Import theories.Runtime.Semantics.
Require Import theories.Core.Values.
Require Import theories.Core.Regions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Core.DynamicActions.
Require Import theories.Meta.EffectFacts.
Require Import theories.Meta.TypingWeakeningFacts.
Require Import theories.Meta.TypeFacts.
Require Import theories.Determinism.Determinism.
Require Import theories.Soundness.TypeSystem.
Require Import theories.Soundness.EffectSystem.
Require Import theories.Meta.TraceFacts.
Require Import theories.Determinism.ReadOnlyDeterminism.
Require Import theories.Meta.RegionFacts.

Import EffectSoundness.
Import TypeSoundness.
Import Expressions.
Import ComputedActions.
Import StaticActions.
Import Semantics.


Lemma EvaluationEffectFromEffApp:
 forall h env rho ef env' rho' f x ec' ee' ea v eff
        facts aacts eff_facts eff_aacts bacts,
   (h, env, rho, ef) ⇓ (h, Cls (env', rho', Mu f x ec' ee'), facts) ->
   (h, env, rho, ea) ⇓ (h, v, aacts) ->
   (h, env, rho, Eff_App ef ea)
     ⇓ (h, eff, Phi_Seq (Phi_Seq eff_facts eff_aacts) bacts) ->
   ReadOnlyPhi facts ->
   ReadOnlyPhi aacts ->
   ReadOnlyPhi (Phi_Seq (Phi_Seq eff_facts eff_aacts) bacts) ->
   (h, update_rec_E (f, Cls (env', rho', Mu f x ec' ee')) (x, v) env', rho', ee')
     ⇓ (h, eff, bacts).
Proof.
  intros h env rho ef env' rho' f x ec' ee' ea v eff
    facts aacts eff_facts eff_aacts bacts
    HFun HArg HEff HFunRO HArgRO HEffRO.
  inversion HEff; subst.
  repeat match goal with
  | H : ReadOnlyPhi (Phi_Seq _ _) |- _ =>
      inversion H; subst; clear H
  end.
  inversion H9; subst.
  assert (HFunEq :
            h ≡@{Heap} h /\
            Cls (env', rho', Mu f x ec' ee') =
            Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0))
    by (eapply ReadOnlyEvalDeterminism; eauto).
  destruct HFunEq as [_ HFunEq]. inversion HFunEq; subst.
  assert (HArgEq : h ≡@{Heap} h /\ v = v')
    by (eapply ReadOnlyEvalDeterminism; eauto).
  destruct HArgEq as [_ HArgEq]. subst.
  assumption.
Qed. 


Lemma DeterminismReadOnlyCond:
  forall h env rho e b1 b2 h' cheap cacts,
    (h, env, rho, e) ⇓ (h', Bit b1, Phi_Nil) ->
    (h, env, rho, e) ⇓ (cheap, Bit b2, cacts) ->
    h' ≡@{Heap} cheap /\ Bit b1 = Bit b2 /\  Phi_Nil = cacts.
Proof.
  intros.
  generalize dependent cacts.
  generalize dependent cheap.
  generalize dependent b2. 
  dependent induction H; intros; inversion H0; subst.
  - repeat split.
  - intuition.
    + now inversion H1.
    + inversion H1; subst.
      rewrite H2 in H10.
      inversion H10; subst. reflexivity.
    + now inversion H1.  
Qed.
  
Lemma EvalTrueIsTrue:
  forall h h' h'' env rho e efft efff eff tacts,
  (h, env, rho, Cond e efft efff) ⇓ (h'', Eff eff, tacts) ->
  (h, env, rho, e) ⇓ (h', Bit true, Phi_Nil) ->
  exists tacts',
    (h', env, rho, efft) ⇓ (h'', Eff eff, tacts') /\
    tacts = Phi_Seq Phi_Nil tacts'.
Proof.
  intros.
  inversion H; subst.
  - assert ( Hbit : h' ≡@{Heap} cheap /\ Bit true = Bit true /\  Phi_Nil = cacts )
     by (eapply DeterminismReadOnlyCond; eauto).
    assert ( HD :h ≡@{Heap} h') by (eapply EmptyTracePreservesHeap_1; eauto).
    destruct Hbit as [? [H_ ?]]; inversion H_; subst.
    unfold equiv, heap_equiv in H1; subst.
    exists tacts0. split; [assumption | reflexivity].
  - assert ( Hbit : h'≡@{Heap}   cheap /\ Bit true = Bit false /\  Phi_Nil = cacts )
      by (eapply DeterminismReadOnlyCond; eauto; 
          assert ( HD :h = h') by (eapply EmptyTracePreservesHeap_1; eauto); 
          apply symmetry).
     destruct Hbit as [? [H_ ?]]; inversion H_; subst.
Qed.


Lemma EvalFalseIsFalse:
forall h h' h'' env rho e efft efff eff tacts,
  (h, env, rho, Cond e efft efff) ⇓ (h'', Eff eff, tacts) ->
  (h, env, rho, e) ⇓ (h', Bit false, Phi_Nil) ->
  exists facts',
    (h', env, rho, efff) ⇓ (h'', Eff eff, facts') /\
    tacts = Phi_Seq Phi_Nil facts'.
Proof.
  intros.
  inversion H; subst.   
  - assert ( Hbit : h' ≡@{Heap}  cheap /\ Bit false = Bit true /\  Phi_Nil = cacts )
      by (eapply DeterminismReadOnlyCond; eauto; 
          assert ( HD :h = h') by (eapply EmptyTracePreservesHeap_1; eauto); 
          apply syymetry).
     destruct Hbit as [? [H_ ?]]; inversion H_; subst.
  - assert ( Hbit : h' ≡@{Heap}  cheap /\ Bit false = Bit false /\  Phi_Nil = cacts )
     by (eapply DeterminismReadOnlyCond; eauto).
    assert ( HD :h = h') by (eapply EmptyTracePreservesHeap_1; eauto).
    destruct Hbit as [? [H_ ?]]; inversion H_; subst.
    assert ( HD :h' = cheap) by (eapply EmptyTracePreservesHeap_1; eauto). 
    unfold equiv, heap_equiv in H1; subst.
    exists facts. split; [assumption | reflexivity].
Qed.

Lemma EvalTrueIsTrue_EmptySound:
  forall h h' h'' env rho e efft efff eff condacts effacts
         stty ctxt rgns ty static,
    TcHeap (h, stty) ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns, e, ty, static) ->
    (h, env, rho, Cond e efft efff) ⇓ (h'', Eff eff, effacts) ->
    (h, env, rho, e) ⇓ (h', Bit true, condacts) ->
    condacts ⋞ Theta_Empty ->
    ReadOnlyPhi effacts ->
    exists branch_acts,
      (h', env, rho, efft) ⇓ (h'', Eff eff, branch_acts) /\
      ReadOnlyPhi branch_acts.
Proof.
  intros h h' h'' env rho e efft efff eff condacts effacts
    stty ctxt rgns ty static HTcHeap HTcRho HTcInc HTcEnv HTcExp
    Hcond Htrue Hempty HRO.
  inversion Hcond; subst.
  - inversion HRO; subst.
    assert (HcondRO : ReadOnlyPhi condacts)
      by (eapply EmptySoundReadOnlyPhi; eauto).
    assert (Hh_h' : h ≡@{Heap} h')
      by (eapply ReadOnlyEvalPreservesHeap; eauto).
    assert (Hh_cheap : h ≡@{Heap} cheap)
      by (eapply ReadOnlyEvalPreservesHeap; eauto).
    unfold equiv, heap_equiv in *; subst.
    exists tacts. split; assumption.
  - inversion HRO; subst.
    assert (Hsame : true = false)
      by (eapply EmptySoundReadOnlyBitDeterminism; eauto).
    discriminate.
Qed.

Lemma EvalFalseIsFalse_EmptySound:
  forall h h' h'' env rho e efft efff eff condacts effacts
         stty ctxt rgns ty static,
    TcHeap (h, stty) ->
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns, e, ty, static) ->
    (h, env, rho, Cond e efft efff) ⇓ (h'', Eff eff, effacts) ->
    (h, env, rho, e) ⇓ (h', Bit false, condacts) ->
    condacts ⋞ Theta_Empty ->
    ReadOnlyPhi effacts ->
    exists branch_acts,
      (h', env, rho, efff) ⇓ (h'', Eff eff, branch_acts) /\
      ReadOnlyPhi branch_acts.
Proof.
  intros h h' h'' env rho e efft efff eff condacts effacts
    stty ctxt rgns ty static HTcHeap HTcRho HTcInc HTcEnv HTcExp
    Hcond Hfalse Hempty HRO.
  inversion Hcond; subst.
  - inversion HRO; subst.
    assert (Hsame : false = true)
      by (eapply EmptySoundReadOnlyBitDeterminism; eauto).
    discriminate.
  - inversion HRO; subst.
    assert (HcondRO : ReadOnlyPhi condacts)
      by (eapply EmptySoundReadOnlyPhi; eauto).
    assert (Hh_h' : h ≡@{Heap} h')
      by (eapply ReadOnlyEvalPreservesHeap; eauto).
    assert (Hh_cheap : h ≡@{Heap} cheap)
      by (eapply ReadOnlyEvalPreservesHeap; eauto).
    unfold equiv, heap_equiv in *; subst.
    exists facts. split; assumption.
Qed.

Lemma DeterminismReadOnlyRefs :
  forall h env rho ea0 h'' h' r1 l0 r l aacts,
  (h, env, rho, ea0) ⇓ (h'', Loc (Rgn_Const true false r1) l0, Phi_Nil) -> 
  (h, env, rho, ea0) ⇓ (h', Loc (Rgn_Const true false r) l, aacts) ->
  h'' ≡@{Heap}  h' /\
    Loc (Rgn_Const true false r1) l0 = Loc (Rgn_Const true false r) l /\
    Phi_Nil = aacts.
Proof.
  intros. 
  generalize dependent aacts.
  generalize dependent r.
  generalize dependent l.
  generalize dependent h'.
  dependent induction H. 
  intros. inversion H1; subst.
  repeat split.
  - inversion H1; subst. 
    rewrite H0 in H8. inversion H8; subst.
    reflexivity.
Qed.


Theorem Correctness_soundness_ext :
  forall h h' h'' env rho  p p' v eff stty ctxt rgns ea ee,
    (h, env, rho, ea) ⇓ (h', v, p) ->
    forall h_ h'_ v_ p_,
      h ≡@{Heap} h_ ->
      (h_, env, rho, ea) ⇓ (h'_, v_, p_) ->
      (h, env, rho, ee) ⇓ (h'', Eff eff, p') ->
    BackTriangle (ctxt, rgns, rho, ea, ee) ->
    forall static ty, 
      ReadOnlyPhi p' ->
      TcHeap (h, stty) ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) -> 
      TcExp (ctxt, rgns, ea, ty, static) ->
      p ⋞ eff.
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
    intros HEff HBt static ty HRonly HHeap HRho HInc HEnv HExp. 
  Case "cnt n".
    assert (Phi_Nil ⋞ eff) by (constructor).
    inversion H; subst.
    inversion BS2; subst; assumption.
  Case "bool b".
    assert (Phi_Nil ⋞ eff) by (constructor).
    inversion H; subst.
    inversion BS2; subst; assumption.
  Case "var x".  
    assert (Phi_Nil ⋞ eff) by (constructor).
    inversion H; subst.
    inversion BS2; subst; assumption.
  Case "mu_abs".
    assert (Phi_Nil ⋞ eff) by (constructor).
    inversion H; subst.
    inversion BS2; subst; assumption.
  Case "rgn_abs".
    assert (Phi_Nil ⋞ eff) by (constructor).
    inversion H; subst.
    inversion BS2; subst; assumption.
  Case "mu_app".   
    inversion HExp as  [ | | | | | 
                         ? ? ? ? ? ? ? ? ? ? ? HExp_ef HExp_ea 
                         | | | | | | | | | | | | | | | | | | | ]; subst.
    assert (clsTcVal :
             exists stty',
               (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f x ec' ee'),
                      subst_rho rho (Ty_Arrow tya effc ty effe Ty_Effect))) 
      by (eapply ty_sound; eauto).
    destruct clsTcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
    
    assert (argTcVal :
             exists stty',
               (forall l t', find_ST l sttyb = Some t' -> find_ST l stty' = Some t')
               /\ TcHeap (aheap, stty')
               /\ TcVal (stty', v0, subst_rho rho tya))
        by (eapply ty_sound; eauto using update_env, ext_stores__env).
    destruct argTcVal as [sttya [Weaka [TcHeapa TcVal_v']]]; eauto.
    
    inversion TcVal_cls as [ | | | 
                             ? ? ? ? ? ? ?  TcRho_rho' TcInc' TcEnv_env' TcExp_abs [A B C D HSubst]  
                             | | |]; subst. 
    inversion TcExp_abs as [ | | | 
                             ? ? ? ? ? ? ? ? ? ? ? ? ? TcExp_ec' TcExp_ee' 
                             | | | | | | | | | | | | | | | | | | | | |]; subst.
    rewrite <- HSubst in TcVal_cls.
    do 2 rewrite subst_rho_arrow in HSubst. 
    inversion HSubst as [[H_tyx_tya A C D E]]; clear A C D E.
    rewrite <- H_tyx_tya in TcVal_v'.
    
    (* goal *)
    assert (HSOUND : Phi_Seq (Phi_Seq facts aacts) bacts ⋞  eff).
    
    { apply PTS_Seq. 
      SCase "Phi_Seq facts aacts ⋞  eff".
        apply PTS_Seq.
        SSCase "facts ⋞  eff".
          assert (H_ : facts  ⋞  eff). 
          {
            inversion HBt as [ | | | |  
                               | ? ? ? ? ? ? ? ? ? ?  TcExp_ef TcExp_ea HBt_ef HBt_ea HR_ef HR_ea 
                               | | | | | | | | | | | | | ]; subst.
            SSSCase "Mu_App ef ea0 << (efff0 ⊕ (effa0 ⊕ Eff_App ef ea0))". 
              inversion HEff; subst.  
              assert (facts  ⋞  eff).
              { eapply IHBS1_1 with (h_:=h'') (p_:=facts); eauto.  } 
              assumption.
            SSSCase "Mu_App ef ea0 << (⊤)".  
              inversion HEff; subst.
              apply PhiInThetaTop.
          }
          exact H_.    
        SSCase " aacts ⋞  eff".   
          inversion HBt as [ | | | |  
                             | ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?  TcExp_ef TcExp_ea HBt_ef HBt_ea HR_ef HR_ea 
                             | | | | | | | | | | | | | ]; subst.
          SSSCase "Mu_App ef ea0 << Eff_App ef ea0".  
            assert (H_ : aacts ⋞ eff).
            { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts) in HR_ef.   
              - unfold equiv, heap_equiv in H. 
                inversion HEff; subst.
                 assert (aacts  ⋞  eff).
                 unfold equiv, heap_equiv in BS1_1. subst.
                eapply IHBS1_2 with (h_:=h'') (stty:=stty) (p_:=aacts); eauto.
                  * eassumption.                    
              - assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ef, facts)) by
                    (eapply eff_sound; eauto). 
                eassumption. }
            exact H_. 
            SSSCase "Mu_App ef ea0 << (⊤)".  
              assert (H_ : aacts  ⋞  eff).
              { induction eff; inversion HEff; subst. 
                apply PhiInThetaTop. }
              exact H_. 
      SCase "bacts ⋞ eff".       
        inversion HEff; subst; 
        inversion HBt as [ | | | |  
                           | ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?  TcExp_ef TcExp_ea HBt_ef HBt_ea HR_ef HR_ea 
                           | | | | | | | | | | | | | ]; subst. 
        SSSCase "Mu_App ef ea0 << Eff_App ef ea0".
            assert (HD3 : bacts ⋞ eff). 
            { eapply IHBS1_3
                with (stty:=sttya) (p':=bacts0); eauto; try reflexivity.
              - assert (HfactsRO : ReadOnlyPhi facts).
                { eapply ReadOnlyStaticImpliesReadOnlyPhi
                    with (eps:=fold_subst_eps rho static_ef); eauto.
                  eapply eff_sound; eauto. }
                assert (Hfheap : h'' ≡@{Heap} fheap)
                  by (eapply ReadOnlyEvalPreservesHeap; eauto).
                unfold equiv, heap_equiv in Hfheap; subst.
                assert (HaactsRO : ReadOnlyPhi aacts).
                { eapply ReadOnlyStaticImpliesReadOnlyPhi
                    with (eps:=fold_subst_eps rho static_ea); eauto.
                  eapply eff_sound; eauto. }
                assert (Haheap : fheap ≡@{Heap} aheap)
                  by (eapply ReadOnlyEvalPreservesHeap; eauto).
                unfold equiv, heap_equiv in Haheap; subst.
                eapply EvaluationEffectFromEffApp; eauto.
              - inversion HRonly as [ | | ? ? A B | ]. exact B.
            - apply ExtendedTcInv_2. 
              + assumption.
              + inversion_clear TcInc' as [? ? HInc'].
                now apply HInc' in H3.
              + inversion_clear TcInc' as [? ? HInc'].
                now apply HInc' in H4. 
            - { apply update_env; simpl.  
                - eapply ext_stores__env; eauto. 
                  apply update_env.  
                  + eassumption.
                  + eapply ext_stores__val with (stty:=sttyb); eauto.
                - eapply ext_stores__val with (stty:=sttya); eauto. }
          }
          exact HD3.
        SSSCase "Mu_App ef ea0 << (⊤)".
          assert (H_ : bacts ⋞ None).
          { eapply IHBS1_3 
              with (stty:=sttya) (ee:=Top)
                   (ctxt:=update_rec_T (f, Ty_Arrow tyx effc0 tyc effe0 Ty_Effect)
                            (x, tyx) ctxt0); eauto.
            SSSSCase "Effect Evaluation". 
              eapply BS_Eff_Top. 
              auto.
            SSSSCase "Back Triangle". 
              econstructor.
            SSSSCase "Extended Inc".
              {apply ExtendedTcInv_2. 
               - assumption.
               - inversion_clear TcInc' as [? ? HInc'].
                 now apply HInc' in H3.
               - inversion_clear TcInc' as [? ? HInc'].
                 now apply HInc' in H4.  }
            SSSSCase "Extended TcEnv".
              { apply update_env; simpl.  
                - eapply ext_stores__env; eauto. 
                  apply update_env.  
                  + eassumption.
                  + eapply ext_stores__val with (stty:=sttyb); eauto.
                - eapply ext_stores__val with (stty:=sttya); eauto. }
              }
          exact H_. }
    exact HSOUND.
   Case "rgn_app".    
     inversion HExp as  [ | | | | | 
                          | ? ? ? ? ? ? ?  HTcExp_er HTcRgn_w 
                          | | | | | | | | | | | | | | | | | |]; subst.
     assert (clsTcVal :
              exists stty',
                (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
                /\ TcHeap (fheap, stty')
                /\ TcVal (stty', Cls (env', rho', Lambda x eb),
                       subst_rho rho (Ty_ForallRgn effr tyr))). 
     eapply ty_sound;eauto. 
     destruct clsTcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
     
     inversion TcVal_cls as [ | | | 
                              ? ? ? ? ? ? ? TcRho_rho' TcInc' TcEnv_env' TcExp_abs [A B C D HSubst] 
                              | | |]; subst. 
     inversion TcExp_abs as [ | | | |
                              ? ? ? ? ? ?  HNo HLc1 HLc2 HBt_eb HTExp_eb
                              | | | | | | | | | | | | | | | | | | | |]; subst.
     rewrite <- HSubst in TcVal_cls.
     do 2 rewrite subst_rho_forallrgn in HSubst.
     inversion HSubst as [[H_fold A]]; clear A.
     
     (* goal *)
     assert (HSOUND : Phi_Seq facts bacts ⋞ eff). 
     {apply PTS_Seq.
      SCase "facts ⋞ eff".
        eapply IHBS1_1 with (h_:=h); eauto. 
        inversion HBt; subst; eauto.
        econstructor; eauto.
      SCase " bacts ⋞ eff".
        inversion HBt; subst.
        SSCase "Rgn_App er w << (∅)". 
          { unfold equiv, heap_equiv in HEqual; subst.
            eapply IHBS1_2 with (ee:=Empty); eauto. 
            - inversion HEff; subst. econstructor. reflexivity.
            - apply update_rho; auto.
            - apply update_inc; auto.
            - eapply extended_rho; eauto. }
        SSCase "Rgn_App er w << (⊤)".  
          { eapply IHBS1_2 with (ee:=Top); eauto using update_rho, update_inc, extended_rho; 
            induction eff; 
            try (solve [ constructor ]); inversion HEff.
            subst. econstructor. reflexivity.
          }
     }
     exact HSOUND.
  Case "eff_app".
    inversion HExp as  [ | | | | | | | 
                         ? ? ? ? ? ? ? ? ? ? HExp_ef HExp_ea 
                         | | | | | | | | | | | | | | | | | ]; subst.
    assert (clsTcVal :
             exists stty',
               (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
               /\ TcHeap (h', stty')
               /\ TcVal (stty', Cls (env', rho', Mu f x ec' ee'),
                      subst_rho rho (Ty_Arrow tya effc tyc  effe Ty_Effect))) 
      by (eapply ty_sound; eauto).
    destruct clsTcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
    
    assert (argTcVal :
             exists stty',
               (forall l t', find_ST l sttyb = Some t' -> find_ST l stty' = Some t')
               /\ TcHeap (h', stty')
               /\ TcVal (stty', v', subst_rho rho tya))
      by (eapply ty_sound; eauto using update_env, ext_stores__env).
    destruct argTcVal as [sttya [Weaka [TcHeapa TcVal_v']]]; eauto.
    
    inversion TcVal_cls as [ | | | 
                             ? ? ? ? ? ? ? TcRho_rho' TcInc' TcEnv_env' TcExp_abs [A B C D HSubst] 
                             | | |]; subst. 
    inversion TcExp_abs as [ | | | 
                             ? ? ? ? ? ? ? ? ? ? HBt_ec_ee TcExp_ec' TcExp_ee' 
                             | | | | | | | | | | | | | | | | | | | | |]; subst.
    rewrite <- HSubst in TcVal_cls.
    do 2 rewrite subst_rho_arrow in HSubst. 
    inversion HSubst as [[H_tyx_tya A C D E]]; clear A C D E.
    rewrite <- H_tyx_tya in TcVal_v'.
    
    (* goal *)
    assert (HSOUND : Phi_Seq (Phi_Seq facts aacts) bacts ⋞ eff).
    
    { inversion HBt; subst.   
      apply PTS_Seq.
      - apply PTS_Seq. 
        + inversion HEff; subst.
          apply PhiInThetaTop.
        +  inversion HEff; subst.
           apply PhiInThetaTop.
      - inversion HEff; subst.
        apply PhiInThetaTop. }   
    exact HSOUND.
  Case "par_pair".
    inversion HBt as [ | | | | |  
                       | ? ? ? ? ? ? ? ? ? ? ? ? ? ? A B C D HBt_a HBt_b HBt_c HBt_d 
                       | | | | | | | | | | | |]; subst; 
    inversion HEff; subst; [ | apply PhiInThetaTop]. 
    inversion HExp as  [ | | | | | ? ? ? ? ? ? ? ? ? ? HExp_ef HExp_ea 
                               | | | 
                               ? ? ? ? ? ? ? ? ? ? ? ?  HBt_1 HBt_2 HExp_mu1 HExp_mu2 HExp_eff1 HExp_eff2 
                               | | | | | | | | | | | | | | | | ]; subst. 
    inversion HEff; subst. inversion H14; subst. 
    inversion H7; subst. inversion H13; subst.  
 

    assert (H' : acts_eff1 ⋞ effa1). 
    { eapply IHBS1_1 with (h_:=h''); eauto.
      inversion HRonly as [ | | ? ? X Y | ]; inversion X; inversion Y. assumption. }
    assert (H'' : acts_eff2 ⋞ effb1). 
    { eapply IHBS1_2 with (h_:=h''); eauto.
      inversion HRonly as [ | | ? ? X Y | ]; inversion X; inversion Y; assumption. }
    assert (H''' : acts_mu1 ⋞ effa0).
    { eapply IHBS1_3 with (h_:=h''); eauto.
      inversion HRonly as [ | | ? ? X Y | ]; inversion X; inversion Y; assumption. }
    assert (H'''' : acts_mu2 ⋞ effb2).
    { eapply IHBS1_4  with (h_:=h''); eauto.
      inversion HRonly as [ | | ? ? X Y | ]; inversion X; inversion Y; assumption. }
    
    assert (H_ : (Phi_Par acts_eff1 acts_eff2) ⋞ (Union_Theta effa1 effb1)). 
    apply PTS_Par; [ apply Theta_introl | apply Theta_intror ]; eauto.

    assert (H__ : (Phi_Par acts_mu1 acts_mu2) ⋞ (Union_Theta effa0 effb2)). 
    apply PTS_Par; [ apply Theta_introl | apply Theta_intror ]; eauto.

    assert (_H__ :  ReadOnlyPhi acts_eff1).
    { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:= acts_eff1) in B; auto.
      assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ee_1, acts_eff1)) by
          (eapply eff_sound; eauto). 
      assumption. }
    
    assert (_H_ : acts_mu1 ⋞ theta1). 
    { induction theta1; [| apply PhiInThetaTop].
      eapply IHBS1_3 with (h_:=h''); eauto.
      inversion HExp_mu1; subst. auto.
    } 
    
    assert (_H____ :  ReadOnlyPhi acts_eff2).
    { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:= acts_eff2) in D; auto.
      assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_ee_2, acts_eff2)) by
          (eapply eff_sound; eauto). 
      assumption. }

    assert (_H___ : acts_mu2 ⋞ theta2).
    { induction theta2; [| apply PhiInThetaTop].
      eapply IHBS1_4 with (h_:=h''); eauto.
      inversion HExp_mu2; subst. auto.
    } 
    apply PTS_Seq. 
    apply Theta_introl. assumption.
    apply Theta_intror. assumption.
  Case "cond_true".
    (* goal *)
    assert (HSOUND :  Phi_Seq cacts tacts ⋞ eff).
    { inversion HBt as [ | | | | | | |   
                       | ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? 
                           TcExp_e TcExp_et TcExp_ef HBt_e HBt_et HBt_ef
                       | | | | | | | | | | ]; subst. 
      - assert (H' : cacts ⋞ Some empty_set).
        { eapply IHBS1_1 with (h_:=h) (p':=Phi_Nil); eauto. 
          - constructor. reflexivity.
          - constructor. } 
        
          apply EmptyUnionIsIdentity.
          apply PTS_Seq.
          + eapply EmptyInAnyTheta; eauto.

          + unfold equiv, heap_equiv in H. symmetry in H; subst.
            rewrite UnionEmptyWithEffIsEff.
 
            { assert (HBranch :
                        exists eff_tacts,
                          (h, env, rho, efft) ⇓ (h'', Eff eff, eff_tacts) /\
                          ReadOnlyPhi eff_tacts)
                by (eapply EvalTrueIsTrue_EmptySound
                      with (stty:=stty) (ctxt:=ctxt) (rgns:=rgns)
                           (ty:=ty_e) (static:=static_e); eauto).
              destruct HBranch as [eff_tacts [HEff_tacts HRonly_tacts]].
              eapply IHBS1_2 with (ee:=efft) (h_:=h) (p':=eff_tacts); eauto.
            }
      -  inversion HEff; subst.
         apply PhiInThetaTop. 
    }
    exact HSOUND.
  Case "cond_false".
    (* goal *)
    assert (HSOUND :  Phi_Seq cacts facts ⋞ eff).
    { inversion HBt as [ | | | | | | |   
                       | ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? 
                           TcExp_e TcExp_et TcExp_ef HBt_e HBt_et HBt_ef
                       | | | | | | | | | |]; subst. 
      - assert (H' : cacts ⋞ Some empty_set).
        { eapply IHBS1_1 with (h_:=h) (p':=Phi_Nil); eauto. 
          - constructor. reflexivity.
          - constructor. } 
        
          apply EmptyUnionIsIdentity.
          apply PTS_Seq.
          + eapply EmptyInAnyTheta; eauto.

          + unfold equiv, heap_equiv in H. symmetry in H; subst.
            rewrite UnionEmptyWithEffIsEff.
 
            { assert (HBranch :
                        exists eff_facts,
                          (h, env, rho, efff) ⇓ (h'', Eff eff, eff_facts) /\
                          ReadOnlyPhi eff_facts)
                by (eapply EvalFalseIsFalse_EmptySound
                      with (stty:=stty) (ctxt:=ctxt) (rgns:=rgns)
                           (ty:=ty_e) (static:=static_e); eauto).
              destruct HBranch as [eff_facts [HEff_facts HRonly_facts]].
              eapply IHBS1_2 with (ee:=efff) (h_:=h) (p':=eff_facts); eauto.
            }
      -  inversion HEff; subst.
         apply PhiInThetaTop. 
    }
    exact HSOUND.
  Case "new_ref e".
    (* goal *)
    assert (HSOUND : Phi_Seq vacts (Phi_Elem (DA_Alloc r (allocate_H heap' r) v0)) ⋞ eff).
    { inversion HEff; subst; 
      inversion HBt as [ | | | | | |   
                         | | | ? ?  ? ? ? ? ? ? TcExp_e HBt_e
                         | | | | | | | | | ]; subst.
      apply EnsembleUnionComp.    
      SCase "Ref w e << (a ⊕ AllocAbs w)". 
        eapply IHBS1 with (h_:=h''); eauto.
        inversion HRonly; assumption.
        inversion H8; subst.
        apply PTS_Elem. apply DAT_Alloc_Abs.
        rewrite H in H2. inversion H2.
        apply In_singleton.
      SCase "Ref w e << (⊤)". 
        apply PhiInThetaTop.  
    }
    exact HSOUND.
  Case "get_ref e". 
    (* goal *)
    assert (HSOUND : Phi_Seq aacts (Phi_Elem (DA_Read r l v)) ⋞ eff ).
    { inversion HBt as [ | | | | | | |   
                       | ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TcExp_e TcExp_et TcExp_ef HBt_e HBt_et HBt_ef | 
                       | ? ? ? ? ? ? ? ? TcExp_ea0 HBt_ea0 | 
                       | | | | | | | ]; subst. 
      - inversion HEff; subst. 
        apply EnsembleUnionComp.
        + eapply IHBS1 with (h_:=h''); eauto.
          inversion HRonly; subst. assumption.
        + apply PTS_Elem. inversion H10; subst.
          rewrite H in H3; inversion H3.
          apply DAT_Read_Abs. apply In_singleton.  
      - inversion HEff; subst.
        assert (aacts ⋞ Some empty_set). 
        eapply IHBS1 with (h_:=h); eauto. constructor. reflexivity.
        apply PTS_Seq.
        + apply EmptyInAnyTheta. assumption.
        + apply PTS_Elem.
          simpl in H; inversion H; subst.  
          apply DAT_Read_Conc. 
          assert (HD: h'' ≡@{Heap} h' /\  
                      Loc (Rgn_Const true false r1) l0 = Loc (Rgn_Const true false r) l /\ 
                      Phi_Nil = aacts). 
          eapply DeterminismReadOnlyRefs; eauto.
          destruct HD as [? [H_ ?]]; inversion H_; subst.
          apply In_singleton.
      - econstructor; inversion HEff; subst; apply PhiInThetaTop.
    }
    exact HSOUND.
  Case "set_ref e1 e2".
    (* goal *)
    assert (HSOUND : Phi_Seq (Phi_Seq aacts vacts) (Phi_Elem (DA_Write r l v0)) ⋞ eff ).
    { inversion HBt as [| | | | | | | | | | |
                      | ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                      | ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                      | | | | | ]; subst. 
      SCase "Assign w ea0 ev << (eff1 ⊕ (eff2 ⊕ WriteAbs w))".
        inversion HEff; subst.
        apply PTS_Seq. 
        SSCase "Phi_Seq aacts vacts ⊑ Union_Theta effa effb".
          apply EnsembleUnionComp.
          SSSCase "aacts ⋞ effa".
            inversion HExp; subst.
            eapply IHBS1_1 with (h_:=h''); eauto. 
            inversion HRonly; subst. assumption.
            SSSCase "vacts ⋞ effb".  
              inversion HEff; subst.
              inversion H11; subst.
              inversion HExp; subst. 

              assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e1, aacts))
              by(eapply eff_sound; eauto).

            assert (HEq_1 : heap' = h'').
            eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=aacts) in HR.
            unfold equiv, heap_equiv in H; symmetry in H; auto.
            exact facts_Eff. 

            assert (vacts ⋞ effa1).  
            { eapply IHBS1_2 with (p':= phia1); eauto. 
              - unfold equiv, heap_equiv in HEqual; subst. eassumption.
              - rewrite HEq_1. eassumption.
                - repeat match goal with
                  | Hro : ReadOnlyPhi (Phi_Seq _ _) |- _ =>
                      apply ReadOnlyPhi_Seq_inv in Hro; destruct Hro
                  end; assumption.
              - rewrite HEq_1. assumption. }
            apply Theta_introl. assumption.
          SSCase "Phi_Elem (DA_Write r l v0) ⊑ Union_Theta effa effb".    
            inversion H11; subst.
            assert (Phi_Elem (DA_Write r l v0) ⋞ effb0). 
            apply PTS_Elem.
            match goal with
            | Hwrite : (_, _, _, WriteAbs _) ⇓ (_, Eff _, _) |- _ =>
                inversion Hwrite; subst
            end.
            match goal with
            | Hdyn : find_R ?w ?rho = Some ?r,
              Heff : find_R ?w ?rho = Some ?r' |-
                  DA_in_Theta (DA_Write ?r _ _) (Some (singleton_set (CA_WriteAbs ?r'))) =>
                rewrite Hdyn in Heff; inversion Heff; subst
            end.
            apply DAT_Write_Abs; apply In_singleton.
          apply Theta_intror. apply Theta_intror. 
          assumption.
      SCase " Assign (Rgn2_Const true false r0) ea0 ev << (eff1 ⊕ (eff2 ⊕ WriteConc ea0))".
         inversion HEff; subst. 
         apply PTS_Seq.
         SSCase "Phi_Seq aacts vacts ⋞ Union_Theta effa effb".
           apply EnsembleUnionComp.
           SSSCase "aacts ⋞ effa".
             inversion HExp; subst.
             eapply IHBS1_1 with (h_:=h'');  eauto.
             inversion HRonly; subst. 
             assumption.
             SSSCase "vacts ⋞ effb". 
               inversion HExp; subst.  
               inversion H11; subst.

               assert (facts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e1, aacts)) by (eapply eff_sound; eauto).
             
             assert (HEq_1 : heap' = h''). 
             { eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=aacts) in HR.
               unfold equiv, heap_equiv in H; auto.
             - exact facts_Eff. }
             
             assert (vacts ⋞ effa0). 
             { eapply IHBS1_2 with (p':= phia0);  eauto.
               - unfold equiv, heap_equiv in HEqual; subst. eassumption.
               - rewrite HEq_1. eassumption.
                 - repeat match goal with
                   | Hro : ReadOnlyPhi (Phi_Seq _ _) |- _ =>
                       apply ReadOnlyPhi_Seq_inv in Hro; destruct Hro
                   end; assumption.
               - rewrite HEq_1. assumption. }
             apply Theta_introl. assumption. 
          SSCase "Phi_Elem (DA_Write r l v0) ⋞ Union_Theta effa effb".
            inversion H11; subst.
            assert (Phi_Elem (DA_Write r l v0) ⋞ effb0).
            apply PTS_Elem.
            match goal with
            | Hwrite : (_, _, _, WriteConc _) ⇓ (_, Eff _, _) |- _ =>
                inversion Hwrite; subst
            end.
            match goal with
            | Haddr : (h'', env, rho, ea0) ⇓
                          (_, Loc (Rgn_Const true false ?rw) ?lw, Phi_Nil) |- _ =>
                assert (HD: h'' ≡@{Heap} heap' /\
                            Loc (Rgn_Const true false rw) lw =
                              Loc (Rgn_Const true false r0) l /\
                            Phi_Nil = aacts)
                  by (eapply DeterminismReadOnlyRefs; eauto);
                destruct HD as [? [H_ ?]]; inversion H_; subst
            end.
            match goal with
            | Hfind : find_R (Rgn_Const true false _) _ = Some _ |- _ =>
                simpl in Hfind; inversion Hfind; subst
            end.
            apply DAT_Write_Conc; apply In_singleton.
            apply Theta_intror. apply Theta_intror. assumption.
      SCase "Assign w ea0 ev << (⊤)".
        inversion HEff; subst.   
        apply PhiInThetaTop.
    }
    exact HSOUND.
  Case "nat_plus x y". 
    (* goal *)
    assert (HSOUND : Phi_Seq lacts racts  ⋞ eff ).
    { inversion HBt as [| | | | | | | | | | |
                      | ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                      | ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                      | ? ? ? ? ? ? ? ? ? ? ? HTcExp_a HTcExp_b HR HBt_a HBt_b 
                      | | | | ]; subst;
      inversion HEff; subst;
      [apply EnsembleUnionComp | ]. 
 
      - eapply IHBS1_1 with (ee:=eff1) (h_:=h''); eauto.  
        inversion HRonly as [ | | ? ? X Y | ]; assumption.
      - assert (lacts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e1, lacts)) by
            (eapply eff_sound; eauto). 
        assert (HEq_1 : lheap = h'').   
        eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=lacts) in HR.
        unfold equiv, heap_equiv in H; auto. 
        exact lacts_Eff. 
        
        eapply IHBS1_2 with (ee:=eff2) (h_:=h'') (p':=phib); eauto.
        + rewrite <- HEq_1. eassumption. 
        + rewrite HEq_1. eassumption. 
        + inversion HRonly as [ | | ? ? X Y | ]; assumption.
        + rewrite HEq_1. assumption.
      - apply PhiInThetaTop.
    } 
    exact HSOUND. 
  Case "nat_minus x y".   
    (* goal *)
    assert (HSOUND : Phi_Seq lacts racts  ⋞ eff ).
    { inversion HBt as [| | | | | | | | | | |
                      | ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                      | ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                      |  
                      | ? ? ? ? ? ? ? ? ? ? ? HTcExp_a HTcExp_b HR HBt_a HBt_b
                      | | | ]; subst;
      inversion HEff; subst;
      [apply EnsembleUnionComp | ]. 
 
      - eapply IHBS1_1 with (ee:=eff1) (h_:=h''); eauto.  
        inversion HRonly as [ | | ? ? X Y | ]; assumption.
      - assert (lacts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e1, lacts)) by
            (eapply eff_sound; eauto). 
        assert (HEq_1 : lheap = h'').   
        eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=lacts) in HR.
        unfold equiv, heap_equiv in H; auto.
        exact lacts_Eff. 
        
        eapply IHBS1_2 with (ee:=eff2) (h_:=h'') (p':=phib); eauto.
        + rewrite <- HEq_1. eassumption. 
        + rewrite HEq_1. eassumption. 
        + inversion HRonly as [ | | ? ? X Y | ]; assumption.
        + rewrite HEq_1. assumption.
      - apply PhiInThetaTop.
    }  
    exact HSOUND.
  Case "nat_times x y".
    (* goal *)
    assert (HSOUND : Phi_Seq lacts racts ⋞ eff ).
    { inversion HBt as [| | | | | | | | | | |
                        | ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                        | ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                        | | 
                        | ? ? ? ? ? ? ? ? ? ? ? HTcExp_a HTcExp_b HR HBt_a HBt_b 
                        | | ]; subst;
      inversion HEff; subst;
      [apply EnsembleUnionComp | ]. 
 
      - eapply IHBS1_1 with (ee:=eff1) (h_:=h''); eauto.  
        inversion HRonly as [ | | ? ? X Y | ]; assumption.
      - assert (lacts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e1, lacts)) by
            (eapply eff_sound; eauto). 
        assert (HEq_1 : lheap = h'').   
        eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=lacts) in HR.
        unfold equiv, heap_equiv in H; auto.
        exact lacts_Eff. 
        
        eapply IHBS1_2 with (ee:=eff2) (h_:=h'') (p':=phib); eauto.
        + rewrite <- HEq_1. eassumption. 
        + rewrite HEq_1. eassumption. 
        + inversion HRonly as [ | | ? ? X Y | ]; assumption.
        + rewrite HEq_1. assumption.
      - apply PhiInThetaTop.
    }  
    exact HSOUND.
  Case "bool_eq x y".
    (* goal *)
    assert (HSOUND : Phi_Seq lacts racts ⋞ eff ).
    { inversion HBt as [| | | | | | | | | | |
                        | ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                        | ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                        | | |  
                        | ? ? ? ? ? ? ? ? ? ? ? HTcExp_a HTcExp_b HR HBt_a HBt_b 
                        | ]; subst;
      inversion HEff; subst;
      [apply EnsembleUnionComp | ]. 
 
      - eapply IHBS1_1 with (ee:=eff1) (h_:=h''); eauto.  
        inversion HRonly as [ | | ? ? X Y | ]; assumption.
      - assert (lacts_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e1, lacts)) by
            (eapply eff_sound; eauto). 
        assert (HEq_1 : lheap = h'').   
        eapply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=lacts) in HR.
        unfold equiv, heap_equiv in H; auto.
        exact lacts_Eff. 
        
        eapply IHBS1_2 with (ee:=eff2) (h_:=h'') (p':=phib); eauto.
        + rewrite <- HEq_1. eassumption. 
        + rewrite HEq_1. eassumption. 
        + inversion HRonly as [ | | ? ? X Y | ]; assumption.
        + rewrite HEq_1. assumption.
      - apply PhiInThetaTop.
    }  
    exact HSOUND.
  Case "alloc_abs".
    assert (Phi_Nil ⋞ eff) by (constructor).
    inversion H; subst.
    inversion BS2; subst; assumption.
  Case "read_abs".
    assert (Phi_Nil ⋞ eff) by (constructor).
    inversion H; subst.
    inversion BS2; subst; assumption.
  Case "write_abs".
    assert (Phi_Nil ⋞ eff) by (constructor).
    inversion H; subst.
    inversion BS2; subst; assumption.
  Case "read_conc".
    assert (Phi_Nil ⋞ eff) by (constructor).
    inversion H; subst.
    inversion BS2; subst; assumption.
  Case "write_conc".
    assert (Phi_Nil ⋞ eff) by (constructor).
    inversion H; subst.
    inversion BS2; subst; assumption.
  Case "eff_concat".
    (* goal *)
    assert (HSOUND : Phi_Seq phia phib ⋞ eff ).
    { inversion HBt as [| | | | | | | | | | |
                        | ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                        | ? ? ? ? ? ? ? ? ? ? HBt_ea0 HBt_ev TcExp_ea0 HR
                        | | |  
                        | ? ? ? ? ? ? ? ? ? ? ? HTcExp_a HTcExp_b HR HBt_a HBt_b 
                        | ]; subst;
      inversion HEff; subst.
      apply PhiInThetaTop.
    }
    exact HSOUND.
  Case "eff_top".
    assert (Phi_Nil ⋞ eff) by (constructor).
    inversion H; subst.
    inversion BS2; subst; assumption.
  Case "eff_empty".
    assert (Phi_Nil ⋞ eff) by (constructor).
    inversion H; subst.
    inversion BS2; subst; assumption.  
Qed.
