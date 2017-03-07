Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.

Add LoadPath "." as Top0.
Require Import Top0.Tactics.
Require Import Top0.Keys.
Require Import Top0.Definitions.
Require Import Top0.Environment.
Require Import Top0.TypeSystem.
Require Import Top0.Heap.
Require Import Top0.CorrectnessLemmas.
Require Import Top0.AdditionalLemmas.
Require Import Top0.Axioms.

Module EffectSoundness.

Import TypeSoundness.

Lemma EmptyInNil:
  forall st, Epsilon_Phi_Soundness (st, Phi_Nil).
Proof.
  intros st. apply EPS. intros da HIn.
  inversion  HIn.
Qed.
  
Lemma sound_approx_inj :
  forall (st1 st2 : Epsilon) (dy : Phi),
    Epsilon_Phi_Soundness (st1, dy) ->
    Epsilon_Phi_Soundness (Union StaticAction st1 st2, dy) /\ Epsilon_Phi_Soundness (Union StaticAction st2 st1, dy).
Proof. 
  intros st1 st2 dy HSound; split; inversion HSound as [ ? ? H' ]; subst; constructor;
  intros da HIn; apply H' in HIn; destruct HIn as [ca HIn]; exists ca; intuition.
Qed.

Lemma sound_comp :
  forall (st1 st2 : Epsilon) (dy1 dy2 : Phi),
    Epsilon_Phi_Soundness (st1, dy1) -> Epsilon_Phi_Soundness (st2, dy2) ->
    Epsilon_Phi_Soundness (Union StaticAction st1 st2, Phi_Seq dy1 dy2). 
Proof.
  intros st1 st2 dy1 dy2 H1 H2.
  inversion H1 as [? ? HEps1]; inversion H2 as [? ? HEps2]; subst; constructor;
  intros eff HIn.
  inversion HIn; subst.
  destruct H3 as [HIn_1 | HIn_2].
  - apply HEps1 in HIn_1; destruct HIn_1 as [ca HIn']; exists ca; intuition.
  - apply HEps2 in HIn_2; destruct HIn_2 as [ca HIn']; exists ca; intuition.
Qed. 

Lemma sound_comp_par :
  forall (st1 st2 : Epsilon) (dy1 dy2 : Phi),
    Epsilon_Phi_Soundness (st1, dy1) -> Epsilon_Phi_Soundness (st2, dy2) ->
    Epsilon_Phi_Soundness (Union StaticAction st1 st2, Phi_Par dy1 dy2). 
Proof.
  intros st1 st2 dy1 dy2 H1 H2.
  inversion H1 as [? ? HEps1]; inversion H2 as [? ? HEps2]; subst; constructor;
  intros eff HIn. 
  inversion HIn; subst.
  destruct H3 as [HIn_1 | HIn_2].
  - apply HEps1 in HIn_1; destruct HIn_1 as [ca HIn']; exists ca; intuition.
  - apply HEps2 in HIn_2; destruct HIn_2 as [ca HIn']; exists ca; intuition.
Qed.

Lemma fold_dist_union : forall rho (eff1 eff2 : Epsilon),
                          fold_subst_eps rho (Union_Static_Action eff1 eff2) =
                          Union_Static_Action (fold_subst_eps rho eff1) (fold_subst_eps rho eff2).
Proof.  
  intros rho eff1 eff2.
  unfold fold_subst_eps.
  apply Extensionality_Ensembles. 
  unfold Same_set, Included. split. 
  - intros x H. unfold In in *. unfold Union_Static_Action.
    destruct H as [sa [H1 H2]]. subst.
    destruct H1.
    + apply Union_introl. unfold In in *.
      exists x. intuition.
    +  apply Union_intror. unfold In in *.
      exists x. intuition.   
  - intros x H. unfold In in *. destruct H.
    + unfold In in H. destruct H as [sa ?].
      exists sa. intuition. apply Union_introl. auto.
    + unfold In in H. destruct H as [sa ?].
      exists sa. intuition. apply Union_intror. auto.
Qed.

Lemma eff_sound : 
  forall e hp hp' env rho v dynamic_eff,
    (hp, env, rho, e) ⇓ (hp', v, dynamic_eff) ->
    forall stty ctxt rgns ty static_eff,
      TcEnv (stty, rho, env, ctxt) -> 
      TcExp (ctxt, rgns, e, ty, static_eff) ->     
      TcHeap (hp, stty) ->
      TcRho (rho, rgns) ->
      Epsilon_Phi_Soundness (fold_subst_eps rho static_eff, dynamic_eff).
Proof.
  intros e hp hp' env rho v dynamic_eff D. 
  intros stty ctxt rgns ty static_eff HTcEnv HTcExp HTcHeap HTcRho. 
  dynamic_cases (dependent induction D) Case; inversion HTcExp; subst.
  Case "cnt n". apply EmptyInNil.
  Case "bool b". apply EmptyInNil.
  Case "var x". apply EmptyInNil.
  Case "mu_abs". apply EmptyInNil.
  Case "rgn_abs". apply EmptyInNil.
  Case "mu_app".  
    assert (clsTcVal : exists stty', 
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
             /\ TcHeap (fheap, stty')
             /\ TcVal (stty', Cls (env', rho', Mu f x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect)))
       by (eapply ty_sound; eauto). 
     
    destruct clsTcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto. 
    assert (argTcVal : exists stty',
             (forall l t', ST.find l sttyb = Some t' -> ST.find l stty' = Some t')
             /\ TcHeap (aheap, stty')
             /\ TcVal (stty', v0, subst_rho rho tya)) by
        (eapply ty_sound; eauto using update_env, ext_stores__env).
    destruct argTcVal as [sttya [Weaka [TcHeapa TcVal_v']]]; eauto.
 
    assert (Sf : Epsilon_Phi_Soundness (fold_subst_eps rho efff, facts)) by (eapply IHD1; eauto). 
    assert (Sa : Epsilon_Phi_Soundness (fold_subst_eps rho effa, aacts)) by
        (eapply IHD2 with (stty := sttyb);
         eauto using update_env, ext_stores__env).


    inversion TcVal_cls as  [ | | | ? ? ? ? ? ? ? TcRho_rho' TcEnv_env' TcExp_abs | | |]; subst. 
    inversion TcExp_abs as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | | | | | | | | | | | | | | ]; subst.  

    rewrite <- H4 in TcVal_cls. 
    do 2 rewrite subst_rho_arrow in H4. inversion H4. 
    rewrite <- H5 in TcVal_v'.
    
    assert (Sb : Epsilon_Phi_Soundness (fold_subst_eps rho effc, bacts)).
    rewrite <- H8; eapply IHD3 with (stty := sttya) (rho:=rho'); eauto.
    SCase "Extended Env".
      apply update_env.
      SSCase "TcEnv". apply update_env.
        SSSCase "Extended". eapply ext_stores__env; eauto.
        SSSCase "Extended TcVal". eapply ext_stores__val; eauto.
      SSCase "TcVal".  eassumption. 

    do 2 rewrite fold_dist_union.
    apply sound_comp; [| assumption].
    apply sound_comp; [|assumption].
    assumption.
  Case "rgn_app".
    assert (cls_TcVal : exists stty', 
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
             /\ TcHeap (fheap, stty')
             /\ TcVal (stty', Cls (env', rho', Lambda x eb),  subst_rho rho (Ty2_ForallRgn effr tyr)))
    by (eapply ty_sound; eauto). 
    destruct cls_TcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
    rewrite fold_dist_union. 
    apply sound_comp.
    
    eapply IHD1; eauto.
    inversion TcVal_cls as  [ | | | ? ? ? ? ? ? ? TcRho_rho' TcEnv_env' TcExp_abs | | |]; subst. 
    inversion TcExp_abs as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | | | | | | | | | | | | | | ]; subst. 
    do 2 rewrite subst_rho_forallrgn in H5. inversion H5. clear H5.
    unfold open_rgn_eff.
    erewrite <- subst_rho_open_close_eps; eauto. 
    replace (Rgn2_Const true true v') with  (mk_rgn_type (Rgn2_Const true false v')) by (simpl; reflexivity).
    rewrite <- subst_as_close_open_eps.
    replace (subst_eps x (Rgn2_Const true false v') effr0) with (subst_in_eff x v' effr0) by (unfold subst_in_eff; reflexivity).
    rewrite <- subst_add_comm_eff; eauto.
    eapply IHD2; eauto.
    eapply extended_rho; eauto. apply update_rho; auto.  eapply not_set_elem_not_in_rho; eauto. assumption.
  Case "eff_app".   
    assert (cls_TcVal : exists stty', 
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
             /\ TcHeap (hp', stty')
             /\ TcVal (stty', Cls (env', rho', Mu f x ec' ee'),  subst_rho rho (Ty2_Arrow tya effc tyc effe Ty2_Effect)))
    by (eapply ty_sound; eauto).

    destruct cls_TcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto. 
    assert (argTcVal : exists stty',
             (forall l t', ST.find l sttyb = Some t' -> ST.find l stty' = Some t')
             /\ TcHeap (hp', stty')
             /\ TcVal (stty', v', subst_rho rho tya)) by
        (eapply ty_sound; eauto using update_env, ext_stores__env).
    destruct argTcVal as [sttya [Weaka [TcHeapa TcVal_v']]]; eauto.

    assert (Sf : Epsilon_Phi_Soundness (fold_subst_eps rho efff, facts)) by (eapply IHD1; eauto). 
    assert (Sa : Epsilon_Phi_Soundness (fold_subst_eps rho effa, aacts)) by
        (eapply IHD2 with (stty := sttyb);
         eauto using update_env, ext_stores__env).

    inversion TcVal_cls as  [ | | | ? ? ? ? ? ? ? TcRho_rho' TcEnv_env' TcExp_abs | | | ]; subst. 
    inversion TcExp_abs as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | | | | | | | | | | | | | |]; subst.

    rewrite <- H4 in TcVal_cls. 
    do 2 rewrite subst_rho_arrow in H4. inversion H4. 
    rewrite <- H5 in TcVal_v'.
    
    assert (Sb : Epsilon_Phi_Soundness (fold_subst_eps rho effe, bacts)).
    rewrite <- H9.
    eapply IHD3 with (stty := sttya); eauto.
    apply update_env.
    SCase "TcEnv". apply update_env.
       SSCase "Extended". eapply ext_stores__env; eauto.
       SSCase "Extended TcVal". eapply ext_stores__val; eauto. eassumption.
        
    do 2 rewrite fold_dist_union.
    apply sound_comp; [| assumption].
    apply sound_comp; [|assumption].
    assumption.
  Case "par_pair".
    assert (HA : Epsilon_Phi_Soundness (fold_subst_eps rho eff1, acts_mu1)).
    eapply IHD3; eauto.
    assert (HB : Epsilon_Phi_Soundness (fold_subst_eps rho eff2, acts_mu2)).
    eapply IHD4; eauto.
    assert (HC : Epsilon_Phi_Soundness (fold_subst_eps rho eff3, acts_eff1)).
    eapply IHD1; eauto.
    assert (HD : Epsilon_Phi_Soundness (fold_subst_eps rho eff4, acts_eff2)).
    eapply IHD2; eauto.  
    assert (H_ : Epsilon_Phi_Soundness (Union_Static_Action (fold_subst_eps rho eff1) (fold_subst_eps rho eff2), 
                                        Phi_Seq acts_mu1 acts_mu2))
     by (apply sound_comp; auto).
    assert (H__ : Epsilon_Phi_Soundness (Union_Static_Action (fold_subst_eps rho eff3) (fold_subst_eps rho eff4), 
                                         Phi_Seq acts_eff1 acts_eff2))
     by (apply sound_comp; auto).

    rewrite fold_dist_union.
    replace (fold_subst_eps rho (Union_Static_Action (Union_Static_Action eff3 eff4) eff2)) with
            (Union_Static_Action (fold_subst_eps rho (Union_Static_Action eff3 eff4)) (fold_subst_eps rho eff2))
      by (rewrite <- fold_dist_union; reflexivity).

    replace (Union_Static_Action (Union_Static_Action (fold_subst_eps rho (Union_Static_Action eff3 eff4))
                                                      (fold_subst_eps rho eff2)) (fold_subst_eps rho eff1)) with
     (Union_Static_Action (fold_subst_eps rho (Union_Static_Action eff3 eff4)) 
                                              (Union_Static_Action (fold_subst_eps rho eff1) (fold_subst_eps rho eff2))). 
    SCase "". 
     { apply sound_comp with (dy1:=Phi_Par acts_eff1 acts_eff2) (dy2:=Phi_Par acts_mu1 acts_mu2).
       - rewrite fold_dist_union. apply sound_comp_par; assumption.
       - apply sound_comp_par; assumption. } 
    SCase "replace proof". 
      rewrite fold_dist_union.
      unfold Union_Static_Action.
      { apply Extensionality_Ensembles;
        unfold Same_set, Included; split; intros x HUnion; unfold Ensembles.In in *.
        - inversion HUnion; subst; inversion H1; subst. 
          + apply Union_introl. apply Union_introl. apply Union_introl. assumption.
          + apply Union_introl. apply Union_introl. apply Union_intror. assumption.
          + apply Union_intror. assumption. 
          + apply Union_introl. apply Union_intror. assumption.
        - inversion HUnion; subst; inversion H1; subst. 
          + apply Union_introl. assumption.
          + apply Union_intror. apply Union_intror. assumption.
          + apply Union_intror. apply Union_introl. assumption. }
  Case "cond_true". 
    assert (boolTcVal : exists stty', 
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
             /\ TcHeap (cheap, stty')
             /\ TcVal (stty', Bit true, subst_rho rho Ty2_Boolean)) by (eapply ty_sound; eauto).
    destruct boolTcVal as [sttyb [Weakb [TcHeapb TcVal_bool]]]; eauto. 

    assert (Epsilon_Phi_Soundness (fold_subst_eps rho eff, cacts)) by (eapply IHD1; eauto).
    do 2 rewrite fold_dist_union.
    assert (Epsilon_Phi_Soundness (fold_subst_eps rho eff1, tacts)) by
      (eapply IHD2 with (stty := sttyb); eauto using ext_stores__env).

    eapply sound_comp; eauto.
    replace tacts with (Phi_Seq tacts (Phi_Nil)) by (apply Phi_Seq_Nil_R). 
    eapply sound_comp; [assumption | apply EmptyInNil].     
  Case "cond_false". 
    assert (bool_TcVal : exists stty', 
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
             /\ TcHeap (cheap, stty')
             /\ TcVal (stty', Bit false, subst_rho rho Ty2_Boolean)) by (eapply ty_sound; eauto). 
    destruct bool_TcVal as [sttyb [Weakb [TcHeapb TcVal_bool]]]; eauto.    
    
    assert (Epsilon_Phi_Soundness (fold_subst_eps rho eff, cacts)) by (eapply IHD1; eauto).
    do 2 rewrite fold_dist_union.
    assert (Epsilon_Phi_Soundness (fold_subst_eps rho eff2, facts)) by
      (eapply IHD2 with (stty := sttyb);  eauto using ext_stores__env).

    eapply sound_comp; eauto.
    replace facts with (Phi_Seq (Phi_Nil) facts) by (apply Phi_Seq_Nil_L).
    eapply sound_comp; [apply EmptyInNil | assumption].  
  Case "new_ref e".
    assert (Epsilon_Phi_Soundness (fold_subst_eps rho  veff, vacts)) by (eapply IHD; eauto).
    rewrite fold_dist_union.
    apply sound_comp; [assumption | ].
    econstructor. intros eff HIn.
    inversion HIn; subst.
    eexists. split. unfold In, fold_subst_eps, Singleton_Static_Action, fold_subst_sa.
    eexists. intuition.
    simpl. simpl in H; inversion H; subst. rewrite subst_rho_rgn_const. constructor.
  Case "get_ref e".
    assert (Epsilon_Phi_Soundness (fold_subst_eps rho aeff, aacts)) by (eapply IHD; eauto).
    rewrite fold_dist_union.
    apply sound_comp; [assumption | ]. 
    econstructor. intros eff HIn.
    inversion HIn.
    eexists. split. unfold In, fold_subst_eps, Singleton_Static_Action, fold_subst_sa.
    eexists. intuition.
    simpl. simpl in H; inversion H; subst. rewrite subst_rho_rgn_const. constructor.
  Case "set_ref e1 e2".
    assert (loc_TcVal : exists stty', 
             (forall k t', ST.find k stty = Some t' -> ST.find k stty' = Some t')
             /\ TcHeap (heap', stty')
             /\ TcVal (stty', Loc (Rgn2_Const true false s) l, subst_rho rho (Ty2_Ref (mk_rgn_type (Rgn2_Const true false s)) t)))
      by (eapply ty_sound; eauto).  
    destruct loc_TcVal as [sttyb [Weakb [TcHeapb TcVal_bool]]]; eauto.    

    assert (Epsilon_Phi_Soundness (fold_subst_eps rho aeff, aacts)) by (eapply IHD1; eauto).
    do 2 rewrite fold_dist_union.
    assert (Epsilon_Phi_Soundness (fold_subst_eps rho veff, vacts)).
      eapply IHD2 with (stty := sttyb); eauto using ext_stores__env.

    apply sound_comp. apply sound_comp. assumption. assumption.  
    econstructor. intros eff HIn.
    inversion HIn.
    eexists. split. unfold In, fold_subst_eps, Singleton_Static_Action, fold_subst_sa.
    eexists. intuition.
    simpl. simpl in H; inversion H; subst. rewrite subst_rho_rgn_const. constructor.
  Case "nat_plus x y".
    assert (H : exists stty', 
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
             /\ TcHeap (lheap, stty')
             /\ TcVal (stty', Num va, subst_rho rho Ty2_Natural)) by (eapply ty_sound; eauto).
    destruct H as [sttyx [Weakx [TcHeapx TcVal_x]]]; eauto.
    rewrite fold_dist_union.
    apply sound_comp; eauto.
    eapply IHD2 with (stty := sttyx); eauto using ext_stores__env.
  Case "nat_minus x y".
    assert (H : exists stty', 
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
             /\ TcHeap (lheap, stty')
             /\ TcVal (stty', Num va, subst_rho rho Ty2_Natural)) by (eapply ty_sound; eauto).
    destruct H as [sttyx [Weakx [TcHeapx TcVal_x]]]; eauto.
    rewrite fold_dist_union.
    apply sound_comp; eauto.
    eapply IHD2 with (stty := sttyx); eauto using ext_stores__env.
  Case "nat_times x y". 
    assert (H : exists stty', 
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
             /\ TcHeap (lheap, stty')
             /\ TcVal (stty', Num va, subst_rho rho Ty2_Natural)) by (eapply ty_sound; eauto).
    destruct H as [sttyx [Weakx [TcHeapx TcVal_x]]]; eauto.
    rewrite fold_dist_union.
    apply sound_comp; eauto.
    eapply IHD2 with (stty := sttyx); eauto using ext_stores__env.
  Case "bool_eq x y".
    assert (H : exists stty', 
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
             /\ TcHeap (lheap, stty')
             /\ TcVal (stty', Num va, subst_rho rho Ty2_Natural)) by (eapply ty_sound; eauto).
    destruct H as [sttyx [Weakx [TcHeapx TcVal_x]]]; eauto.
    rewrite fold_dist_union.
    apply sound_comp; eauto.
    eapply IHD2 with (stty := sttyx); eauto using ext_stores__env. 
  Case "alloc_abs". apply EmptyInNil.
  Case "read_abs". apply EmptyInNil.
  Case "write_abs". apply EmptyInNil.  
  Case "read_conc". apply EmptyInNil.
  Case "write_conc". apply EmptyInNil.
  Case "eff_concat".
     assert (H : exists stty', 
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
             /\ TcHeap (hp', stty')
             /\ TcVal (stty', Eff effa, subst_rho rho Ty2_Effect)) by (eapply ty_sound; eauto).
    destruct H as [sttyx [Weakx [TcHeapx TcVal_x]]]; eauto.
    rewrite fold_dist_union.
    apply sound_comp; eauto.
  Case "eff_top". apply EmptyInNil.
  Case "eff_empty". apply EmptyInNil.
Qed.


Lemma ReadOnlyTracePreservesHeap_2 : 
  forall e hp hp' env rho v dynamic_eff,
    (hp, env, rho, e) ⇓ (hp', v, dynamic_eff) ->
    forall stty ctxt rgns ty static_eff,
      TcEnv (stty, rho, env, ctxt) -> 
      TcExp (ctxt, rgns, e, ty, static_eff) ->     
      TcHeap (hp, stty) ->
      TcRho (rho, rgns) ->
      ReadOnlyStatic (static_eff) ->
      hp = hp'.
Proof.
  intros.
  eapply ReadOnlyTracePreservesHeap_1; [eassumption | ].
  eapply ReadOnlyStaticImpliesReadOnlyPhi; [eapply ReadOnlyStaticImpliesReadOnlySubstStatic; eassumption | ].
  eapply eff_sound; eassumption.
Qed.

End EffectSoundness.
