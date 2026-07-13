From stdpp Require Import gmap.
From stdpp Require Import strings.
From stdpp Require Import fin_maps.

Require Import Coq.Sets.Ensembles.
Require Import Coq.Program.Equality.

Require Import theories.Meta.Tactics.
Require Import theories.Meta.LocallyNameless.
Require Import theories.Runtime.Heap.
Require Import theories.Runtime.TraceSemantics.
Require Import theories.Runtime.HeapTyping.
Require Import theories.Determinism.Determinism.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Core.DynamicActions.
Require Import theories.Meta.EffectFacts.
Require Import theories.Meta.RegionFacts.
Require Import theories.Meta.MapFacts.
Require Import theories.Meta.TypingWeakeningFacts.
Require Import theories.Meta.TypeFacts.
Require Import theories.Meta.StoreFacts.
Require Import theories.Meta.HeapFacts.
Require Import theories.Meta.TraceFacts.
Require Import theories.Meta.TraceTypingFacts.


Module TypeSoundness.

  Import Regions.
  Import StaticActions.
  Import ComputedActions.
  Import Values.
  Import Expressions.
  Import Semantics.
  Import TypeFacts.
  Import Ensembles.

Lemma DisjointImpliesSomeOrNone:
  forall heap_1 heap_2,
    heap_1 ##ₘ heap_2 ->
    forall k v,
        (find_H k heap_1 = Some v -> find_H k heap_2 = None)
         /\ (find_H k heap_2 = Some v -> find_H k heap_1 = None).
Proof.
  intros.
  assert (H'' : forall i,
             heap_1 !! i = None ∨ heap_2 !! i = None).
  intro.
  eapply map_disjoint_alt. auto.
  destruct (H'' k).
  - split; intros.        
    unfold find_H in H1.
    replace (heap_1 !! k) with (None: option Val) in H1.
    inversion H1.
    + assumption.  
  -  split; intros.
     + assumption.
     + unfold find_H in H1.
      replace (heap_2 !! k) with (None: option Val) in H1.
      inversion H1.
Qed.


Lemma TcHeap_Extended_2:
  forall heap env rho ef1 ef2 ea1 ea2 v1 v2 ty1 ty2 acts_mu1 acts_mu2
         heap_mu1 heap_mu2 stty stty1 stty2 hp',
    heap_mu1 ∖ heap ##ₘ heap_mu2 ∖ heap ->
    (heap, env, rho, Mu_App ef1 ea1) ⇓ (heap_mu1, v1, acts_mu1) ->
    (heap, env, rho, Mu_App ef2 ea2) ⇓ (heap_mu2, v2, acts_mu2) ->
    (Phi_Par acts_mu1 acts_mu2, heap) ==>* (Phi_Nil, hp') ->
    TcPhi stty1 acts_mu1 ->
    TcPhi stty2 acts_mu2 ->
    TcVal (stty1, v1, subst_rho rho ty1) ->
    TcVal (stty2, v2, subst_rho rho ty2) ->
    TcHeap (heap, stty) ->
    (forall l t, find_ST l stty = Some t -> find_ST l stty1 = Some t) ->
    (forall l t, find_ST l stty = Some t -> find_ST l stty2 = Some t) ->
    TcHeap (heap_mu1, stty1) ->
    TcHeap (heap_mu2, stty2) ->
    TcHeap (hp', stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty)).
Proof.
  intros heap env rho ef1 ef2 ea1 ea2 v1 v2 ty1 ty2 acts_mu1 acts_mu2
    heap_mu1 heap_mu2 stty stty1 stty2 hp'
    HheapDisj Hstep1 Hstep2 Hpar HTcPhi1 HTcPhi2 _ _
    HTcHeap Hext1 Hext2 HTcHeap1 HTcHeap2.
  eapply
    (TcHeap_Extended_PhiPar
      heap acts_mu1 acts_mu2 heap_mu1 heap_mu2 stty stty1 stty2 hp');
    eauto.
  - eapply BigStep_replays_trace; eauto.
  - eapply BigStep_replays_trace; eauto.
Qed.

      
Lemma ty_sound_var :   
  forall x v stty rho env ctxt t,
  TcEnv (stty, rho, env, ctxt) ->
  find_E x env = Some v -> find_T x ctxt = Some t -> 
  TcVal (stty, v, subst_rho rho t).
Proof.
  intros x v stty rho env ctxt t HTcEnv FindEnv FindCtxt. (* Hclosed. *)
  inversion_clear HTcEnv as [? ? ?  HBst HFwd HBack HTc].
  destruct (HFwd x v FindEnv) as [y FindEnv']. 
  rewrite FindEnv' in FindCtxt. inversion FindCtxt; subst. 
  eapply HTc; [eexact FindEnv | eexact FindEnv' ]. (*| assumption]. *)
Qed.
 
Lemma ty_sound_closure:  
  forall stty rgns env rho ctxt f x ec ee tyx tyc effc effe, 
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns)->
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns,  Mu f x ec ee, Ty_Arrow tyx effc tyc effe Ty_Effect,
        Empty_Static_Action) -> 
    TcVal (stty, Cls (env, rho,  Mu f x ec ee),
        subst_rho rho (Ty_Arrow tyx effc tyc effe Ty_Effect)).   
Proof.
  intros; econstructor; eauto.
Qed.

Lemma ty_sound_region_closure:
  forall stty rgns env rho ctxt x er tyr effr, 
    TcRho (rho, rgns) -> 
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns, Lambda x er, Ty_ForallRgn (close_var_eff x effr) (close_var x tyr),
        Empty_Static_Action) ->
    TcVal (stty, Cls (env, rho, Lambda x er),
        subst_rho rho (Ty_ForallRgn (close_var_eff x effr) (close_var x tyr))).
Proof.
  intros. econstructor; eauto.
Qed.  
  
Lemma weakening_trans :
   forall stty stty' stty'', 
     (forall (l : SigmaKey) (t : Tau),
        find_ST l stty = Some t -> find_ST l stty' = Some t) ->
     (forall (l : SigmaKey) (t : Tau),
        find_ST l stty' = Some t -> find_ST l stty'' = Some t) ->
     (forall (l : SigmaKey) (t : Tau),
        find_ST l stty = Some t -> find_ST l stty'' = Some t).
Proof.
  intros stty stty' stty'' Weak Weak'.
  intros l t ?. apply Weak'. now apply Weak. 
Qed.

Lemma bound_var_is_fresh :
  forall rho rgns  x,
    TcRho (rho, rgns) ->
    not_set_elem rgns x ->
    x ∉ dom rho.
Proof.
  intros rho rgns x H1 H2.
  inversion H1; subst.
  unfold not_set_elem in H2. unfold Ensembles.Complement in H2. 
  unfold not. intro.
  apply H2. apply H0.
  contradict H. apply not_elem_of_dom. assumption.
Qed.
 
Lemma update_inc:
  forall rgns ctxt x,
    TcInc (ctxt, rgns) ->
    TcInc (ctxt, set_union rgns (singleton_set x)).
Proof.
  intros.
  econstructor. inversion H; subst.
  intros. apply H1 in H0.
  unfold included, set_union, Included in *.
  intros. apply H0 in H2.
  now apply Union_introl.
Qed.

  

Lemma ty_sound_strong:
  forall e env rho hp hp' v dynamic_eff,
    (hp, env, rho, e) ⇓ (hp', v, dynamic_eff) ->
    forall stty ctxt rgns t static_eff,
      TcHeap (hp, stty) ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns)->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e, t, static_eff) ->
      exists stty',
        (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
         /\ TcHeap (hp', stty')
         /\ TcVal (stty', v, subst_rho rho t)
         /\ TcPhi stty' dynamic_eff.
Proof.
  intros e env rho hp hp'  v dynamic_eff D. 
  dynamic_cases (dependent induction D) Case;
  intros stty ctxt rgns t static_eff Hhp Hrho Hinc Henv Hexp; 
  inversion Hexp; subst.    
  Case "cnt n"%string.
    exists stty; split; [auto |]; split; [auto |]; split;
      [try rewrite subst_rho_natural; apply TC_Num | apply TcPhi_nil].
  Case "bool b".
    exists stty; split; [auto |]; split; [auto |]; split;
      [try rewrite subst_rho_boolean; apply TC_Bit | apply TcPhi_nil].
  Case "var x".
    exists stty; split; [auto |]; split; [auto |]; split;
      [eapply ty_sound_var; eassumption | apply TcPhi_nil].
  Case "mu_abs".
    exists stty; split; [auto |]; split; [auto |]; split;
      [eapply ty_sound_closure; try (solve [eassumption]); auto | apply TcPhi_nil].
  Case "rgn_abs".
    exists stty; split; [auto |]; split; [auto |]; split;
      [eapply ty_sound_region_closure; try (solve [eassumption]) | apply TcPhi_nil].
  Case "mu_app".
    edestruct IHD1 as [sttym [Weak1 [TcHeap1 [TcVal_mu TcPhi_mu]]]]; eauto. 
    edestruct IHD2 as [sttya [Weaka [TcHeapa [TcVal_arg TcPhi_arg]]]]; eauto.  
    eapply ext_stores__env; eauto.
    inversion TcVal_mu as [ | | | ? ? ? ? ? ? ? TcRho_rho' TcRho_Inc' TcEnv_env' TcExp_abs | | |] ; subst.    
    inversion TcExp_abs as [ | |  | ? ? ? ? ? ? ? ? ? ? ? ? ? TcExp_ec TcExp_ee | | | | | | | | | | | | | | | | | | | | | ]; subst.   
    rewrite <- H5 in TcVal_mu.   
    do 2 rewrite subst_rho_arrow in H5. inversion H5.  
    assert (SubstEq1: subst_rho rho' tyx = subst_rho rho tya) by assumption. 
    assert (SubstEq2: subst_rho rho' tyc = subst_rho rho t) by assumption. 
    rewrite <- SubstEq1 in TcVal_arg.
    unfold update_rec_E, update_rec_T in *.     
    edestruct IHD3 with (ctxt:=update_T (x, tyx)
                                 (update_T (f, Ty_Arrow tyx effc0 tyc effe0 Ty_Effect) ctxt0))
      as [sttyb [Weakb [TcHeapb [TcVal_res TcPhi_res]]]]; eauto. simpl in *.
    SCase "TcInc".
    {apply ExtendedTcInv_2. 
     - assumption.
     - inversion_clear TcRho_Inc' as [? ? HInc].
       now apply HInc in H1.
     - inversion_clear TcRho_Inc' as [? ? HInc].
       now apply HInc in H2.  }
    SCase "TcEnv".
      apply update_env. apply update_env. eapply ext_stores__env; eauto.  
      eapply ext_stores__val; eauto. eassumption.
    SCase "TcHeap".
      exists sttyb. split.
      { intros l t' Hfind. apply Weakb. apply Weaka. now apply Weak1. }
      split; [assumption |].
      split; [assumption |].
      assert (HTcPhi_fun_arg : TcPhi sttyb (Phi_Seq facts aacts)).
      { apply TcPhi_seq;
        [ eapply TcPhi_weaken with (stty:=sttym);
          [intros l t' Hfind; apply Weakb; now apply Weaka | exact TcPhi_mu]
        | eapply TcPhi_weaken with (stty:=sttya);
          [exact Weakb | exact TcPhi_arg] ]. }
      apply TcPhi_seq; assumption.
    SCase "TcVal".
      edestruct IHD1 as [sttyl [Weak1 [TcHeap1 [TcVal_lam TcPhi_lam]]]]; eauto. 
      inversion TcVal_lam as  [ | | | ? ? ? ? ? ? ?  TcRho_rho' TcInc'  TcEnv_env' TcExp_lam | | |]; subst.   
      inversion TcExp_lam as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | | | | | | | | | | | | | |  ]; subst.   
      { edestruct IHD2 with (rgns:=set_union rgns0 (singleton_set x))
        as [sttyr [Weak2 [TcHeap2 [TcVal_res TcPhi_res]]]]; eauto using update_env, ext_stores__env.
        - { apply update_rho; [ assumption | assumption]. }
        - apply update_inc. assumption.
        - eapply extended_rho; eauto.
        - exists sttyr. split.
          { intros l t' Hfind. apply Weak2. now apply Weak1. }
          split; [assumption |].
          split.
          + rewrite subst_rho_forallrgn in H5.
            rewrite subst_rho_forallrgn in H5.
            inversion H5.  
            unfold update_R in TcVal_res. 
            simpl in TcVal_res. rewrite subst_add_comm in TcVal_res.
            * unfold subst_in_type in TcVal_res.
              rewrite SUBST_AS_CLOSE_OPEN in TcVal_res; auto.
              erewrite subst_rho_open_close in TcVal_res; eauto.
            * eapply map_to_list_unique with (m:=<[x:=v']> rho'); eauto.
            * apply not_elem_of_dom.
              eapply bound_var_is_fresh; eauto.
          + apply TcPhi_seq.
            * eapply TcPhi_weaken with (stty:=sttyl);
                [exact Weak2 | exact TcPhi_lam].
            * exact TcPhi_res. }
  Case "eff_app". 
    edestruct IHD1 as [sttym [Weak1 [TcHeap1 [TcVal_mu TcPhi_mu]]]]; eauto.
    edestruct IHD2 as [sttya [Weaka [TcHeapa [TcVal_arg TcPhi_arg]]]]; eauto using ext_stores__env.
    inversion TcVal_mu as  [ | | | ? ? ? ? ? ? ? TcRho_rho' TcInc' TcEnv_env' TcExp_abs | | |]; subst. 
    inversion TcExp_abs as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | | | | | | | | | | | | | |  ]; subst. 
    edestruct IHD3 with (ctxt:=update_T (x, tyx)
                                 (update_T (f, Ty_Arrow tyx effc0 tyc0 effe0 Ty_Effect) ctxt0))
      as [sttyb [Weakb [TcHeapb [TcVal_res TcPhi_res]]]]; eauto. simpl in *.
    SCase "Extended Inc". 
    {apply ExtendedTcInv_2. 
     - assumption.
     - inversion_clear TcInc' as [? ? HInc].
       now apply HInc in H0.
     - inversion_clear TcInc' as [? ? HInc].
       now apply HInc in H1.  }
    SCase "Extended Env". 
      apply update_env. 
      SSCase "TcEnv". 
      { apply update_env. 
        - eapply ext_stores__env; eauto.
        - rewrite <- H4 in TcVal_mu.  eapply ext_stores__val; eauto. }
      SSCase "TcVal".
        do 2 rewrite subst_rho_arrow in H4.
        inversion H4. 
        assert (SubstEq: subst_rho rho' tyx = subst_rho rho tya) by assumption.
        rewrite <- SubstEq in TcVal_arg.  eassumption. 
        exists sttyb. split.
        { intros l t' Hfind. apply Weakb. apply Weaka. now apply Weak1. }
        split; [assumption |].
        split.
        { rewrite subst_rho_effect. rewrite subst_rho_effect in TcVal_res.
          assumption. }
        assert (HTcPhi_fun_arg : TcPhi sttyb (Phi_Seq facts aacts)).
        { apply TcPhi_seq;
          [ eapply TcPhi_weaken with (stty:=sttym);
            [intros l t' Hfind; apply Weakb; now apply Weaka | exact TcPhi_mu]
          | eapply TcPhi_weaken with (stty:=sttya);
            [exact Weakb | exact TcPhi_arg] ]. }
        apply TcPhi_seq; assumption.
  Case "par_pair".
    edestruct IHD3 as [sttym [Weak1 [TcHeap1 [TcVal_app1 TcPhi_app1]]]]; eauto.  
    edestruct IHD4 as [sttya [Weaka [TcHeapa [TcVal_app2 TcPhi_app2]]]]; eauto. 
    assert (exists stty' : Sigma,
           (forall (l : SigmaKey) (t' : Tau),
            find_ST l stty = Some t' -> find_ST l stty' = Some t') /\
             TcHeap (heap_eff1, stty') /\
             TcVal (stty', Eff theta1, subst_rho rho ty3) /\
             TcPhi stty' acts_eff1)
      as HTyped3.
    eapply IHD1; eauto.
    assert (exists stty' : Sigma,
           (forall (l : SigmaKey) (t' : Tau),
            find_ST l stty = Some t' -> find_ST l stty' = Some t') /\
             TcHeap (heap_eff2, stty') /\
             TcVal (stty', Eff theta2, subst_rho rho ty4) /\
             TcPhi stty' acts_eff2)
      as HTyped4.
    eapply IHD2; eauto.
    assert (exists stty' : Sigma,
           (forall (l : SigmaKey) (t' : Tau),
            find_ST l stty = Some t' -> find_ST l stty' = Some t') /\
             TcHeap (heap_mu1, stty') /\
             TcVal (stty', v1, subst_rho rho ty1) /\
             TcPhi stty' acts_mu1)
      as HTyped1.
    eapply IHD3; eauto.
    assert (exists stty' : Sigma,
           (forall (l : SigmaKey) (t' : Tau),
            find_ST l stty = Some t' -> find_ST l stty' = Some t') /\
             TcHeap (heap_mu2, stty') /\
             TcVal (stty', v2, subst_rho rho ty2) /\
             TcPhi stty' acts_mu2)
      as HTyped2.
    eapply IHD4; eauto.
    destruct HTyped1 as[ stty1 [HA1  [HA2 [HA3 HA4]]]].
    destruct HTyped2 as[ stty2 [HB1  [HB2 [HB3 HB4]]]].
    destruct HTyped3 as[ stty3 [HC1  [HC2 [HC3 HC4]]]].
    destruct HTyped4 as[ stty4 [HD1  [HD2 [HD3 HD4]]]].  
    { exists (stty ∪ ((stty1 ∖ stty) ∪ (stty2 ∖ stty))).
      destruct H0 as [HEff1 HEff2].
      split.  
      + assert (stty1 ∖ stty ##ₘ stty2 ∖ stty)
          by (eapply djt_heap_implies_djt_stty; eauto).
        intros.
        assert (find_ST l stty1 = Some t') by (apply HA1; auto).
        assert (find_ST l stty2 = Some t') by (apply HB1; auto).
        intros. eapply StoreTyping_Union_2; eauto.
      + split.
          * eapply TcHeap_Extended_2
              with (acts_mu1:=acts_mu1) (acts_mu2:=acts_mu2); eauto.
        * split.
          -- eapply TcValExtended_2; eauto.
             eapply djt_heap_implies_djt_stty; eauto.
          -- assert (HsttyDisj : stty1 ∖ stty ##ₘ stty2 ∖ stty)
               by (eapply djt_heap_implies_djt_stty; eauto).
             assert (HCto :
                       forall l t',
                         find_ST l stty3 = Some t' ->
                         find_ST l (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty)) = Some t').
             { intros l t' Hfind3.
               inversion HC2 as [? ? _ HStoreHeap3 _]; subst.
               destruct (HStoreHeap3 l t' Hfind3) as [v HfindEff].
               unfold equiv, heap_equiv in HEff1; subst heap_eff1.
               inversion Hhp as [? ? HHeapStore _ _]; subst.
               destruct (HHeapStore l v HfindEff) as [t0 HfindBase].
               assert (Hfind3base : find_ST l stty3 = Some t0)
                 by (apply HC1; assumption).
               assert (t' = t0) by (eapply PairType_unique_type; eauto).
               subst. eapply StoreTyping_Extended_Base; eauto. }
             assert (HDto :
                       forall l t',
                         find_ST l stty4 = Some t' ->
                         find_ST l (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty)) = Some t').
             { intros l t' Hfind4.
               inversion HD2 as [? ? _ HStoreHeap4 _]; subst.
               destruct (HStoreHeap4 l t' Hfind4) as [v HfindEff].
               unfold equiv, heap_equiv in HEff2; subst heap_eff2.
               inversion Hhp as [? ? HHeapStore _ _]; subst.
               destruct (HHeapStore l v HfindEff) as [t0 HfindBase].
               assert (Hfind4base : find_ST l stty4 = Some t0)
                 by (apply HD1; assumption).
               assert (t' = t0) by (eapply PairType_unique_type; eauto).
               subst. eapply StoreTyping_Extended_Base; eauto. }
             assert (HTcPhi_eff :
                       TcPhi (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty))
                         (Phi_Par acts_eff1 acts_eff2)).
             { apply TcPhi_par.
               - eapply TcPhi_weaken with (stty:=stty3); eauto.
               - eapply TcPhi_weaken with (stty:=stty4); eauto. }
             assert (HTcPhi_mu :
                       TcPhi (stty ∪ (stty1 ∖ stty ∪ stty2 ∖ stty))
                         (Phi_Par acts_mu1 acts_mu2)).
             { apply TcPhi_par.
               - eapply TcPhi_weaken with (stty:=stty1); eauto.
                 intros l t' Hfind. eapply StoreTyping_Extended_Left; eauto.
               - eapply TcPhi_weaken with (stty:=stty2); eauto.
                 intros l t' Hfind. eapply StoreTyping_Extended_Right; eauto. }
             apply TcPhi_seq; assumption.
    }
  Case "cond_true".
    edestruct IHD1 as [sttyb [Weakb [TcHeapvb [TcVal_e0 TcPhi_e0]]]]; eauto. 
    edestruct IHD2 as [stty1 [Weak1 [TcHeapv1 [TcVal_e1 TcPhi_e1]]]]; 
      eauto using ext_stores__env.
    exists stty1. split.
    { intros l t' Hfind. apply Weak1. now apply Weakb. }
    split; [assumption |].
    split; [assumption |].
    apply TcPhi_seq; [eapply TcPhi_weaken; eauto | assumption].
  Case "cond_false".
    edestruct IHD1 as [sttyb [Weakb [TcHeapvb [TcVal_e0 TcPhi_e0]]]]; eauto. 
    edestruct IHD2 as [stty2 [Weak2 [TcHeapv2 [TcVal_e2 TcPhi_e2]]]]; 
      eauto using ext_stores__env.
    exists stty2. split.
    { intros l t' Hfind. apply Weak2. now apply Weakb. }
    split; [assumption |].
    split; [assumption |].
    apply TcPhi_seq; [eapply TcPhi_weaken; eauto | assumption].
  Case "new_ref e".
    edestruct IHD with (stty := stty)
                      (ctxt := ctxt)
                      (rgns := rgns)  
                      (t := t0)
                      (static_eff := veff)
      as [sttyv [Weakv [TcHeapv [TcVal_v TcPhi_v]]]]; eauto.
    assert (find_H (r, allocate_H heap' r) heap' = None)
      by (apply allocate_H_fresh).
    assert (HfreshST : find_ST (r, allocate_H heap' r) sttyv = None).
    { destruct (find_ST (r, allocate_H heap' r) sttyv) as [t |] eqn:Hfind; auto.
      inversion_clear TcHeapv as [? ? ? STfind_Hfind ?].
      destruct (STfind_Hfind (r, allocate_H heap' r) t Hfind) as [? ex].
      rewrite H0 in ex. discriminate. }
    assert (Weakv_update :
              forall k' t',
                find_ST k' sttyv = Some t' ->
                find_ST k'
                  (update_ST (r, allocate_H heap' r)
                     (subst_rho rho t0) sttyv) = Some t').
    { intros k' t' STfind.
      destruct (decide (k' = (r, allocate_H heap' r))) as [Heq | Hneq].
      - subst. rewrite HfreshST in STfind. discriminate.
      - apply G_diff_keys_2;
          [ intro Heq; apply Hneq; now symmetry | assumption ]. }
    exists (update_ST (r, allocate_H heap' r) (subst_rho rho t0) sttyv);
      split; [ | split; [ | split]].
    SCase "Extended stores".
      intros k' t' STfind. apply Weakv_update. now apply Weakv.
    SCase "Heap typeness".
      apply H_update_heap_fresh; eauto.
    SCase "Loc is well-typed".
      simpl in H; inversion H; subst. 
      rewrite subst_rho_tyref. unfold mk_rgn_type. rewrite subst_rho_rgn_const.
      econstructor;
        [ unfold find_ST, update_ST; apply lookup_insert
        | intro; eapply TcVal_implies_closed in TcVal_v; eauto ].
    SCase "Trace is well-typed".
      apply TcPhi_seq;
        [ eapply TcPhi_weaken; eauto
        | unfold TcPhi; intros k' v' HUpdate;
          inversion HUpdate; subst;
          exists (subst_rho rho t0); split;
          [ unfold find_ST, update_ST; apply lookup_insert
          | eapply ext_stores__val; eauto ] ].
  Case "get_ref e".
    edestruct IHD with (hp' := hp')
                      (v := Loc (Rgn_Const true false s) l) 
                      (stty := stty)
                      (rgns := rgns)
                      (ctxt := ctxt)
                      (t := Ty_Ref (mk_rgn_type ((Rgn_Const true false s))) t)
                      (static_eff := aeff)
                      (dynamic_eff := aacts)
    as [sttyv [Weakv [TcHeapv [TcVal_v TcPhi_v]]]]; eauto.
    exists sttyv. split; [ | split; [ | split]].
    SCase "HeapTyping extends".
      apply Weakv.
    SCase "Heap is well typed".
      apply TcHeapv.
    SCase "Value is well-typed".
      inversion_clear TcHeapv as [? ? ? ? HeapTcVal]. eapply HeapTcVal; eauto. 
      inversion TcVal_v; subst; simpl in H; inversion H; subst.
      rewrite subst_rho_tyref in H7. inversion H7. subst.
      assumption.
    SCase "Trace is well-typed".
      apply TcPhi_seq;
        [ assumption
        | unfold TcPhi; intros k' v' HUpdate; inversion HUpdate ].
  Case "set_ref e1 e2".
    edestruct IHD1 with (hp' := heap')
                       (v := Loc (Rgn_Const true false s) l) 
                       (stty := stty)
                       (ctxt := ctxt)
                       (rgns := rgns)
                       (t := Ty_Ref (mk_rgn_type ((Rgn_Const true false s))) t0)
                       (static_eff := aeff)
                       (dynamic_eff := aacts)
       as [sttya [Weaka [TcHeapa [TcVal_a TcPhi_a]]]]; eauto.
    edestruct IHD2 with (stty := sttya)
                       (ctxt := ctxt)
                       (rgns := rgns)  
                       (t := t0)
                       (static_eff := veff)
      as [sttyv [Weakv [TcHeapv [TcVal_v TcPhi_v]]]]; eauto using ext_stores__env.
    assert (HwriteST : find_ST (r, l) sttyv = Some (subst_rho rho t0)).
    { apply Weakv. inversion TcVal_a; subst.
      simpl in H0; inversion H0; subst.
      match goal with
      | Hty : _ = subst_rho _ (Ty_Ref _ _) |- _ =>
          rewrite subst_rho_tyref in Hty; inversion Hty; subst
      | Hty : subst_rho _ (Ty_Ref _ _) = _ |- _ =>
          rewrite subst_rho_tyref in Hty; inversion Hty; subst
      end.
      assumption. }
    exists sttyv. split; [ | split; [ | split]].
    SCase "HeapTyping extends".
      eapply weakening_trans; eauto.
    SCase "New heap is well typed".
      apply H_update_heap_exists with (t:= subst_rho rho t0).   
      { assumption. }
      { assumption. }
      { assumption. }
    SCase "Result value is well-typed".
      rewrite subst_rho_unit. constructor.
    SCase "Trace is well-typed".
      assert (HTcPhi_av : TcPhi sttyv (Phi_Seq aacts vacts)).
      { apply TcPhi_seq;
          [ eapply TcPhi_weaken with (stty:=sttya); eauto
          | exact TcPhi_v ]. }
      apply TcPhi_seq;
        [ exact HTcPhi_av
        | unfold TcPhi; intros k' v' HUpdate; inversion HUpdate; subst;
          exists (subst_rho rho t0); split; [ exact HwriteST | exact TcVal_v ] ].
  Case "nat_plus x y".
    edestruct IHD1 as [sttyx [Weakx [TcHeapvx [TcVal_x TcPhi_x]]]]; eauto. 
    edestruct IHD2 as [sttyy [Weaky [TcHeapvy [TcVal_y TcPhi_y]]]]; 
      eauto using ext_stores__env. 
    exists sttyy. split.
    { intros l t' Hfind. apply Weaky. now apply Weakx. }
    split; [assumption |].
    split; [rewrite subst_rho_natural; constructor |].
    apply TcPhi_seq;
      [ eapply TcPhi_weaken with (stty:=sttyx); eauto
      | assumption ].
  Case "nat_minus x y".
    edestruct IHD1 as [sttyx [Weakx [TcHeapvx [TcVal_x TcPhi_x]]]]; eauto. 
    edestruct IHD2 as [sttyy [Weaky [TcHeapvy [TcVal_y TcPhi_y]]]]; 
      eauto using ext_stores__env.
    exists sttyy. split.
    { intros l t' Hfind. apply Weaky. now apply Weakx. }
    split; [assumption |].
    split; [rewrite subst_rho_natural; constructor |].
    apply TcPhi_seq;
      [ eapply TcPhi_weaken with (stty:=sttyx); eauto
      | assumption ].
  Case "nat_times x y".
    edestruct IHD1 as [sttyx [Weakx [TcHeapvx [TcVal_x TcPhi_x]]]]; eauto. 
    edestruct IHD2 as [sttyy [Weaky [TcHeapvy [TcVal_y TcPhi_y]]]]; 
      eauto using ext_stores__env.
    exists sttyy. split.
    { intros l t' Hfind. apply Weaky. now apply Weakx. }
    split; [assumption |].
    split; [rewrite subst_rho_natural; constructor |].
    apply TcPhi_seq;
      [ eapply TcPhi_weaken with (stty:=sttyx); eauto
      | assumption ].
  Case "bool_eq x y".
    edestruct IHD1 as [sttyx [Weakx [TcHeapvx [TcVal_x TcPhi_x]]]]; eauto. 
    edestruct IHD2 as [sttyy [Weaky [TcHeapvy [TcVal_y TcPhi_y]]]]; 
      eauto using ext_stores__env.
    exists sttyy. split.
    { intros l t' Hfind. apply Weaky. now apply Weakx. }
    split; [assumption |].
    split; [rewrite subst_rho_boolean; constructor |].
    apply TcPhi_seq;
      [ eapply TcPhi_weaken with (stty:=sttyx); eauto
      | assumption ].
  Case "alloc_abs".
    exists stty; split; [auto |]; split; [auto |]; split;
      [rewrite subst_rho_effect; constructor | subst; apply TcPhi_nil].
  Case "read_abs".
    exists stty; split; [auto |]; split; [auto |]; split;
      [rewrite subst_rho_effect; constructor | subst; apply TcPhi_nil].
  Case "write_abs".
    exists stty; split; [auto |]; split; [auto |]; split;
      [rewrite subst_rho_effect; constructor | subst; apply TcPhi_nil].
  Case "read_conc".
    exists stty. split; [auto |].
    split.
    { assert (hp = hp') by (eapply EmptyTracePreservesHeap_1; eauto; reflexivity);
      now subst. }
    split; [rewrite subst_rho_effect; constructor | subst; apply TcPhi_nil].
  Case "write_conc".
    exists stty. split; [auto |].
    split.
    { assert (hp = hp') by (eapply EmptyTracePreservesHeap_1; eauto; reflexivity);
      now subst. }
    split; [rewrite subst_rho_effect; constructor | subst; apply TcPhi_nil].
  Case "eff_concat".
    edestruct IHD1 as [sttya [Weaka [TcHeapa [TcVal_a TcPhi_a]]]]; eauto.
    edestruct IHD2 with (stty := sttya)
      as [sttyb [Weakb [TcHeapb [TcVal_b TcPhi_b]]]];
      eauto using ext_stores__env.
    exists sttyb. split.
    { intros l t' Hfind. apply Weakb. now apply Weaka. }
    split; [assumption |].
    split; [rewrite subst_rho_effect; constructor |].
    apply TcPhi_seq;
      [ eapply TcPhi_weaken with (stty:=sttya); eauto
      | assumption ].
  Case "eff_top".
    exists stty; split; [auto |]; split; [auto |]; split;
      [rewrite subst_rho_effect; constructor | subst; apply TcPhi_nil].
  Case "eff_empty".
    exists stty; split; [auto |]; split; [auto |]; split;
      [rewrite subst_rho_effect; constructor | subst; apply TcPhi_nil].
Qed.

Lemma ty_sound:
  forall e env rho hp hp' v dynamic_eff,
    (hp, env, rho, e) ⇓ (hp', v, dynamic_eff) ->
    forall stty ctxt rgns t static_eff,
      TcHeap (hp, stty) ->
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns)->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e, t, static_eff) ->
      exists stty',
        (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
         /\ TcHeap (hp', stty')
         /\ TcVal (stty', v, subst_rho rho t).
Proof.
  intros e env rho hp hp' v dynamic_eff HD
         stty ctxt rgns t static_eff Hhp Hrho Hinc Henv Hexp.
  destruct (ty_sound_strong e env rho hp hp' v dynamic_eff HD
              stty ctxt rgns t static_eff Hhp Hrho Hinc Henv Hexp)
    as [stty' [Hweak [HTcHeap [HTcVal _]]]].
  exists stty'. intuition.
Qed.

End TypeSoundness.
