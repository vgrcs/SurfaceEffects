From stdpp Require Import gmap.
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

Require Import Definitions.Values.
Require Import Definitions.Expressions.
Require Import Definitions.Semantics.
Require Import Definitions.DynamicActions.
Require Import Definitions.ComputedActions.
Require Import Definitions.GHeap.
Require Import Definitions.GTypes.
Require Import Definitions.Regions.
Require Import Definitions.Axioms.
Require Import Proofs.EffectFacts.
Require Import Proofs.TypeFacts.
Require Import Proofs.HeapFacts.
Require Import Proofs.RegionFacts.
Require Import Proofs.EffectSystem.
Require Import Proofs.TypeSystem.
Require Import Proofs.Determinism.
Require Import Proofs.Correctness.

Import EffectSoundness.
Import TypeSoundness.
Import StaticActions.

Example PairParAux:
  forall h'' heap_mu theta env v rho ef ea 
         acts_eff acts_mu,
   (h'', env, rho, Mu_App ef ea) ⇓ (heap_mu, v, acts_mu) ->
   (h'', env, rho, Eff_App ef ea) ⇓ (h'', Eff theta, acts_eff) ->
   forall stty ctxt rgns ty_e static_e,
     TcHeap (h'', stty) ->
     TcRho (rho, rgns) ->
     TcEnv (stty, rho, env, ctxt) ->
     TcExp (ctxt, rgns, Mu_App ef ea, ty_e, static_e) ->
     acts_mu ⋞ theta /\ ReadOnlyPhi acts_eff.
Proof.
  intros.
  inversion H4; subst.
  assert (BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea)) by (eapply H9).  
  inversion H5; subst.
  split.
  - eapply Correctness_soundness_ext with (ea:=Mu_App ef ea); eauto.
    assert (Epsilon_Phi_Soundness (fold_subst_eps rho static_ee, acts_eff)) 
      by (eapply eff_sound; eauto). 
    eapply ReadOnlyStaticImpliesReadOnlyPhi in H19; eauto.
 -  assert (Epsilon_Phi_Soundness (fold_subst_eps rho static_ee, acts_eff)) 
      by (eapply eff_sound; eauto). 
    eapply ReadOnlyStaticImpliesReadOnlyPhi in H19; eauto.
Qed.

Theorem Dynamic_DetTrace :
  forall heap rho env exp heap' val' phi',
    forall stty ctxt rgns t static_eff,
      TcHeap (heap, stty) ->
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, exp, t, static_eff) ->
      (heap, env, rho, exp) ⇓ (heap', val', phi') ->
      Det_Trace phi'.
Proof.
  intros heap rho env exp heap' val' phi' stty ctxt rgns t static_eff HTcHeap HTcRho HTcEnv HTcExp HStep. 
  generalize dependent stty.
  generalize dependent rgns.
  generalize dependent t.
  generalize dependent ctxt.
  generalize dependent static_eff.
  dependent induction HStep; intros;
    try (solve [repeat constructor;
                try (eapply IHHStep; reflexivity);
                try (eapply IHHStep1; reflexivity);
                try (eapply IHHStep2; reflexivity);
                try (eapply IHHStep3; reflexivity);
                try assumption]).
  - constructor.  
    + constructor. 
      * inversion HTcExp; subst. eapply IHHStep1; eauto.
      * inversion HTcExp; subst.
        assert (clsTcVal :
                 exists stty',
                   (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
                   /\ TcHeap (fheap, stty')
                   /\ TcVal (stty', Cls (env', rho', Mu f x ec' ee'),
                          subst_rho rho (Ty_Arrow tya effc t effe Ty_Effect))) 
          by (eapply ty_sound; eauto).
        destruct clsTcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
        eapply IHHStep2; eauto using ext_stores__env.
     +  inversion HTcExp; subst. 
        assert (clsTcVal :
                 exists stty',
                   (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
                   /\ TcHeap (fheap, stty')
                   /\ TcVal (stty', Cls (env', rho', Mu f x ec' ee'),
                          subst_rho rho (Ty_Arrow tya effc t effe Ty_Effect))) 
          by (eapply ty_sound; eauto).
        destruct clsTcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
        assert (argTcVal :
                 exists stty',
                   (forall l t', find_ST l sttyb = Some t' -> find_ST l stty' = Some t')
                   /\ TcHeap (aheap, stty')
                   /\ TcVal (stty', v, subst_rho rho tya))
          by (eapply ty_sound; eauto using update_env, ext_stores__env).
        destruct argTcVal as [sttya [Weaka [TcHeapca TcVal_v']]]; eauto.
        inversion TcVal_cls as [ | | | 
                                 ? ? ? ? ? ? ? TcRho_rho' TcInc' 
                                   TcEnv_env' TcExp_abs [A B C D HSubst] 
                                 | | |]; subst. 
        inversion TcExp_abs as [ | | | 
                                 ? ? ? ? ? ? ? ? ? ?  HBt_ec_ee TcExp_ec' TcExp_ee' 
                                 | | | | | | | | | | | | | | | | | | | | |]; subst.
        rewrite <- HSubst in TcVal_cls.
        do 2 rewrite subst_rho_arrow in HSubst. 
        inversion HSubst as [[H_tyx_tya A C D E]]; clear A C D E.
        rewrite <- H_tyx_tya in TcVal_v'.
        { eapply IHHStep3; eauto using ext_stores__env.
          - apply update_env; simpl.  
            + eapply ext_stores__env ; eauto. 
              apply update_env.  
              * eassumption.
              * eapply ext_stores__val with (stty:=sttyb); eauto.
            + eapply ext_stores__val with (stty:=sttya); eauto. }
  - constructor; inversion HTcExp; subst.
    + eapply IHHStep1; eauto.
    + assert (tcVal :
               exists stty',
                 (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
                 /\ TcHeap (fheap, stty')
                 /\ TcVal (stty', Cls (env', rho', Lambda x eb),
                        subst_rho rho (Ty_ForallRgn effr tyr))). 
      eapply ty_sound;eauto. 
      destruct tcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
      
      inversion TcVal_cls as [ | | | 
                               ? ? ? ? ? ? ? TcRho_rho' TcInc'
                                 TcEnv_env' TcExp_abs [A B C D HSubst] 
                               | | |]; subst. 
      inversion TcExp_abs as [ | | | |
                               ? ? ? ? ? ? HNo HLc1 HLc2 HBt_eb HTExp_eb
                               | | | | | | | | | | | | | | | | | | | |]; subst.
      rewrite <- HSubst in TcVal_cls.
      do 2 rewrite subst_rho_forallrgn in HSubst.
      inversion HSubst as [[H_fold A]]; clear A.
      
      { eapply IHHStep2 with (heap:=fheap); eauto. 
       - apply update_rho; auto. 
       - eapply extended_rho; eauto. }   
  - inversion HTcExp; subst. 
    assert (clsTcVal :
             exists stty',
               (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
               /\ TcHeap (heap', stty')
               /\ TcVal (stty', Cls (env', rho', Mu f x ec' ee'),
                      subst_rho rho (Ty_Arrow tya effc tyc  effe Ty_Effect))) 
      by (eapply ty_sound; eauto).
     destruct clsTcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
     
     assert (argTcVal :
              exists stty',
                (forall l t', find_ST l sttyb = Some t' -> find_ST l stty' = Some t')
                /\ TcHeap (heap', stty')
                /\ TcVal (stty', v', subst_rho rho tya))
       by (eapply ty_sound; eauto using update_env, ext_stores__env).
     destruct argTcVal as [sttya [Weaka [TcHeapa TcVal_v']]]; eauto.
     
     inversion TcVal_cls as [ | | | 
                              ? ? ? ? ? ? ? TcRho_rho' TcInc'
                                TcEnv_env' TcExp_abs [A B C D HSubst] 
                              | | |]; subst. 
     inversion TcExp_abs as [ | | | 
                              ? ? ? ? ? ? ? ? ? ? HBt_ec_ee TcExp_ec' TcExp_ee' 
                              | | | | | | | | | | | | | | | | | | | | |]; subst.
     rewrite <- HSubst in TcVal_cls.
     do 2 rewrite subst_rho_arrow in HSubst. 
     inversion HSubst as [[H_tyx_tya A C D E]]; clear A C D E.
     rewrite <- H_tyx_tya in TcVal_v'.

     constructor.
     +  constructor.
        * eapply IHHStep1; eauto using ext_stores__env.
        * eapply IHHStep2; eauto using ext_stores__env.  
     +  { eapply IHHStep3; eauto using ext_stores__env.
          - apply update_env; simpl.  
            + eapply ext_stores__env ; eauto. 
              apply update_env.  
              * eassumption.
              * eapply ext_stores__val with (stty:=sttyb); eauto.
            + eapply ext_stores__val with (stty:=sttya); eauto. }
  - constructor; inversion HTcExp; subst.
    + assert (HS1 : acts_mu1 ⋞ theta1 /\ ReadOnlyPhi acts_eff1). 
      { eapply PairParAux; eauto.  
        - inversion H6; subst.
          assert (BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1))
            by (eapply H7).
          inversion H2; subst.
          
          assert (Epsilon_Phi_Soundness (fold_subst_eps rho static_ee, acts_eff1)) 
            by (eapply eff_sound; eauto). 
          eapply ReadOnlyStaticImpliesReadOnlyPhi in H20; eauto.
          assert (heap = heap_eff1)
            by (destruct H as [HA HB]; unfold equiv, heap_equiv in HA, HB; auto).
          now subst.
      }

      assert (HS2 : acts_mu2 ⋞ theta2 /\ ReadOnlyPhi acts_eff2).
      { eapply PairParAux; eauto.  
        - inversion H11; subst.
          assert (BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2))
            by (eapply H7). 
          inversion H2; subst.
          
          assert (Epsilon_Phi_Soundness (fold_subst_eps rho static_ee, acts_eff2)) 
            by (eapply eff_sound; eauto). 
          eapply ReadOnlyStaticImpliesReadOnlyPhi in H20; eauto.
          assert (heap =heap_eff2)
            by ( destruct H as [HA HB]; unfold equiv, heap_equiv in HA, HB; auto).          
          now subst. }

      destruct HS1, HS2. 
      eapply Det_par_trace_from_readonly; try eassumption.
    + eapply Det_trace_from_theta; try eassumption. 
      * assert (HS1 : acts_mu1 ⋞ theta1 /\ ReadOnlyPhi acts_eff1).
        { eapply PairParAux; eauto. 
          - inversion H6; subst.
            assert (BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1))
              by (eapply H7).
            inversion H2; subst.
            
            assert (Epsilon_Phi_Soundness (fold_subst_eps rho static_ee, acts_eff1)) 
              by (eapply eff_sound; eauto). 
            eapply ReadOnlyStaticImpliesReadOnlyPhi in H20; eauto.
            assert (heap = heap_eff1)
            by ( destruct H as [HA HB]; unfold equiv, heap_equiv in HA, HB; auto).
            now subst. }
        intuition.
      *  assert (HS2 : acts_mu2 ⋞ theta2 /\ ReadOnlyPhi acts_eff2).
         { eapply PairParAux; eauto.  
           - inversion H11; subst.
             assert (BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2))
               by (eapply H7). 
             inversion H2; subst.
             
             assert (Epsilon_Phi_Soundness (fold_subst_eps rho static_ee, acts_eff2)) 
               by (eapply eff_sound; eauto). 
             eapply ReadOnlyStaticImpliesReadOnlyPhi in H20; eauto.
             assert (heap =heap_eff2) by ( destruct H as [HA HB];
                 unfold equiv, heap_equiv in HA, HB; auto).
             now subst. }
         intuition.
      * eapply IHHStep3; eauto.
      * eapply IHHStep4; eauto.
  -  constructor; inversion HTcExp; subst.
     * eapply IHHStep1; eauto.
     * assert (firstVal :
                exists stty',
                  (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
                  /\ TcHeap (cheap, stty')
                  /\ TcVal (stty', Bit true, subst_rho rho Ty_Boolean)). 
       eapply ty_sound; eauto. 
       destruct firstVal as [sttyb [Weakb [TcHeapb TcVal_bit]]]; eauto.
       eapply IHHStep2; eauto using ext_stores__env.
  - constructor; inversion HTcExp; subst.
     * eapply IHHStep1; eauto.
     * assert (firstVal :
                exists stty',
                  (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
                  /\ TcHeap (cheap, stty')
                  /\ TcVal (stty', Bit false, subst_rho rho Ty_Boolean)). 
       eapply ty_sound; eauto. 
       destruct firstVal as [sttyb [Weakb [TcHeapb TcVal_bit]]]; eauto.
       eapply IHHStep2; eauto using ext_stores__env.
  - constructor; inversion HTcExp; subst.
    + eapply IHHStep; eauto.
    + constructor.
  - constructor; inversion HTcExp; subst.
    + eapply IHHStep; eauto.
    + constructor.
  - constructor; inversion HTcExp; subst.
    + constructor. 
      * eapply IHHStep1; eauto.
      * assert (argVal :
                 exists stty',
                   (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
                   /\ TcHeap (heap'0, stty')
                   /\ TcVal (stty', Loc (Rgn_Const true false s) l,
                          subst_rho rho (Ty_Ref (mk_rgn_type (Rgn_Const true false s)) t0))). 
        eapply ty_sound; eauto. 
        destruct argVal as [sttyb [Weakb [TcHeapb TcVal_ea]]]; eauto.
        eapply IHHStep2; eauto using ext_stores__env. 
    + constructor.
  - constructor; inversion HTcExp; subst.
    + eapply IHHStep1; eauto.
    + assert (argVal :
               exists stty',
                 (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
                 /\ TcHeap (lheap, stty')
                 /\ TcVal (stty', Num va, subst_rho rho Ty_Natural)). 
      eapply ty_sound; eauto. 
      destruct argVal as [sttyb [Weakb [TcHeapb TcVal_ea]]]; eauto.
      eapply IHHStep2; eauto using ext_stores__env.
  - constructor; inversion HTcExp; subst.
    + eapply IHHStep1; eauto.
    + assert (argVal :
               exists stty',
                 (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
                 /\ TcHeap (lheap, stty')
                 /\ TcVal (stty', Num va, subst_rho rho Ty_Natural)). 
      eapply ty_sound; eauto. 
      destruct argVal as [sttyb [Weakb [TcHeapb TcVal_ea]]]; eauto.
      eapply IHHStep2; eauto using ext_stores__env.
  - constructor; inversion HTcExp; subst.
    + eapply IHHStep1; eauto.
    + assert (argVal :
               exists stty',
                 (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
                 /\ TcHeap (lheap, stty')
                 /\ TcVal (stty', Num va, subst_rho rho Ty_Natural)). 
      eapply ty_sound; eauto. 
      destruct argVal as [sttyb [Weakb [TcHeapb TcVal_ea]]]; eauto.
      eapply IHHStep2; eauto using ext_stores__env.
  - constructor; inversion HTcExp; subst.
    + eapply IHHStep1; eauto.
    + assert (argVal :
               exists stty',
                 (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
                 /\ TcHeap (lheap, stty')
                 /\ TcVal (stty', Num va, subst_rho rho Ty_Natural)). 
      eapply ty_sound; eauto. 
      destruct argVal as [sttyb [Weakb [TcHeapb TcVal_ea]]]; eauto.
      eapply IHHStep2; eauto using ext_stores__env.
  - constructor; inversion HTcExp; subst.
    + eapply IHHStep1; eauto.
    + eapply IHHStep2; eauto.
Qed.


Theorem DynamicDeterminism_ext : 
  forall heap_a heap_b env rho exp heap1 heap2 val1 val2 acts1 acts2,
    heap_a ≡@{Heap} heap_b ->
    (heap_a, env, rho, exp) ⇓ (heap1, val1, acts1) ->
    (heap_b, env, rho, exp) ⇓ (heap2, val2, acts2) ->
    forall stty ctxt rgns ty static,
     TcHeap (heap_a, stty) ->
     TcRho (rho, rgns) ->
     TcEnv (stty, rho, env, ctxt) ->
     TcExp (ctxt, rgns, exp, ty, static) ->
     heap1 ≡@{Heap} heap2 /\ val1 = val2 /\ acts1 = acts2.
Proof.
  intros heap_a heap_b env rho exp heap1 heap2 val1 val2 acts1 acts2 Heq Dyn1.
  generalize dependent acts2; generalize dependent val2; generalize dependent heap2. 
  generalize dependent heap_b.
  dependent induction Dyn1; 
    intros heap_b Heq heap2 val2 acts2 Dyn2 stty ctxt rgns ty static
      HTcHeap HTcRho HTcEnv HTcExp;
  inversion Dyn2; subst;
  try (solve [intuition]).
  - intuition. rewrite H0 in H8. inversion H8; subst. reflexivity.
  - inversion HTcExp as  [ | | | | | 
                           ? ? ? ? ? ? ? ? ? ? HExp_ef HExp_ea 
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
               /\ TcVal (stty', v, subst_rho rho tya))
      by (eapply ty_sound; eauto using update_env, ext_stores__env).
    destruct argTcVal as [sttya [Weaka [TcHeapa TcVal_v']]]; eauto.
    
    inversion TcVal_cls as [ | | | 
                             ? ? ? ? ? ? ? TcRho_rho' TcInc' 
                               TcEnv_env' TcExp_abs [A B C D HSubst] 
                             | | |]; subst. 
    inversion TcExp_abs as [ | | | 
                             ? ? ? ? ? ? ? ? ? ? HBt_ec_ee TcExp_ec' TcExp_ee' 
                             | | | | | | | | | | | | | | | | | | | | |]; subst.
    rewrite <- HSubst in TcVal_cls.
    do 2 rewrite subst_rho_arrow in HSubst. 
    inversion HSubst as [[H_tyx_tya A C D E]]; clear A C D E.
    rewrite <- H_tyx_tya in TcVal_v'.

    assert ( RH1 : fheap ≡@{Heap} fheap0
                   /\ Cls (env', rho', Mu f x ec' ee')
                      = Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0)
                   /\ facts = facts0 ).
    eapply IHDyn1_1; eauto. 
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1; subst.
    assert ( RH2 : aheap ≡@{Heap} aheap0 /\ v = v0 /\ aacts = aacts0). 
    
    eapply IHDyn1_2; eauto using ext_stores__env.
    destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]; subst.
    
    assert ( RH3 : heap1 ≡@{Heap} heap2 /\ val1 = val2 /\ bacts = bacts0).
    { eapply IHDyn1_3; eauto. 
      - apply update_env; simpl.  
        + eapply ext_stores__env; eauto.  
          apply update_env.
          * eassumption.
          * eapply ext_stores__val with (stty:=sttyb); eauto.
        + eapply ext_stores__val with (stty:=sttya); eauto. }
    destruct RH3 as [h_eq_3 [v_eq_3 a_eq_3]]; subst.
    auto.
  -  inversion HTcExp as  [ | | | | | 
                           |  ? ? ? ? ? ? ? HTcExp_er HTcRgn_w 
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
                              ? ? ? ? ? ? ? TcRho_rho' TcInc'
                                TcEnv_env' TcExp_abs [A B C D HSubst] 
                              | | |]; subst. 
     inversion TcExp_abs as [ | | | |
                              ? ? ? ? ? ? HNo HLc1 HLc2 HBt_eb HTExp_eb
                              | | | | | | | | | | | | | | | | | | | |]; subst.
     rewrite <- HSubst in TcVal_cls.
     do 2 rewrite subst_rho_forallrgn in HSubst.
     inversion HSubst as [[H_fold A]]; clear A.
     
     
     assert ( RH1 : fheap ≡@{Heap} fheap0 /\
                      Cls (env', rho', Lambda x eb) = Cls (env'0, rho'0, Lambda x0 eb0) /\
                      facts = facts0 ).
     eapply IHDyn1_1; eauto.
     destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
     rewrite H in H9. inversion H9; subst.
    
     assert ( RH2 : heap1 ≡@{Heap} heap2 /\ val1 = val2 /\ bacts = bacts0).
     { eapply IHDyn1_2 with (heap_a:=fheap); eauto. 
       - apply update_rho; auto.
       - eapply extended_rho; eauto. }
     
     destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. subst.
     intuition.    
  -  inversion HTcExp as  [ | | | | | ? ? ? ? ? ? ? ? ? ? ? HExp_ef HExp_ea 
                            | | | 
                            ? ? ? ? ? ? ? ? ? ? ? ? ? ? HExp_mu1 HExp_mu2 HExp_eff1 HExp_eff2 
                            | | | | | | | | | | | | | | | | ]; subst.
     assert (clsTcVal :
              exists stty',
                (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
                /\ TcHeap (heap1, stty')
                /\ TcVal (stty', Cls (env', rho', Mu f x ec' ee'),
                       subst_rho rho (Ty_Arrow tya effc tyc  effe Ty_Effect))) 
       by (eapply ty_sound; eauto).
     destruct clsTcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
     
     assert (argTcVal :
              exists stty',
                (forall l t', find_ST l sttyb = Some t' -> find_ST l stty' = Some t')
                /\ TcHeap (heap1, stty')
                /\ TcVal (stty', v', subst_rho rho tya))
       by (eapply ty_sound; eauto using update_env, ext_stores__env).
     destruct argTcVal as [sttya [Weaka [TcHeapa TcVal_v']]]; eauto.
     
     inversion TcVal_cls as [ | | | 
                              ? ? ? ? ? ? ? TcRho_rho' TcInc'
                                TcEnv_env' TcExp_abs [A B C D HSubst] 
                              | | |]; subst. 
     inversion TcExp_abs as [ | | | 
                              ? ? ? ? ? ? ? ? ? ? HBt_ec_ee TcExp_ec' TcExp_ee' 
                              | | | | | | | | | | | | | | | | | | | | |]; subst. 
     rewrite <- HSubst in TcVal_cls. 
     do 2 rewrite subst_rho_arrow in HSubst.
     inversion HSubst as [[H_tyx_tya A C D E]]; clear A C D E.
     rewrite <- H_tyx_tya in TcVal_v'.
     
     assert ( RH1 : heap1 ≡@{Heap} heap2
                    /\  Cls (env', rho', Mu f x ec' ee')
                        = Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0)
                    /\ facts = facts0 ).
     eapply IHDyn1_1; eauto using ext_stores__env.
     destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
     
     assert ( RH2 : heap1 ≡@{Heap} heap2 /\  v' = v'0 /\ aacts = aacts0 ).
     eapply IHDyn1_2;  eauto using ext_stores__env.
     destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2. subst.
     
     assert ( RH3 : heap1 ≡@{Heap} heap2 /\  val1 = val2 /\ bacts = bacts0 ).  
     { eapply IHDyn1_3; eauto.
       - apply update_env; simpl.  
          + eapply ext_stores__env ; eauto. 
                  apply update_env.  
                  * eassumption.
                  * eapply ext_stores__val with (stty:=sttyb); eauto.
                + eapply ext_stores__val with (stty:=sttya); eauto. }
     destruct RH3 as [h_eq_3 [v_eq_3 a_eq_3]]. inversion v_eq_3. subst.
     intuition.
  - inversion HTcExp as  [ | | | | | ? ? ? ? ? ? ? ? ? ? ? HExp_ef HExp_ea 
                           | | | 
                           ? ? ? ? ? ? ? ? ? ? ? ? ? ? HExp_mu1 HExp_mu2 HExp_eff1 HExp_eff2 
                           | | | | | | | | | | | | | | | | ]; subst.
    
    inversion HExp_mu1; subst.
    assert (BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1))
      by (eapply H6).
    inversion HExp_mu2; subst.
    assert (BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2))
      by (eapply H8).
 
    inversion H2; inversion H3; subst.
          
    assert (Epsilon_Phi_Soundness (fold_subst_eps rho static_ee, acts_eff1)) 
      by (eapply eff_sound; eauto). 
    assert (Epsilon_Phi_Soundness (fold_subst_eps rho static_ee0,acts_eff2)) 
      by (eapply eff_sound; eauto). 
    assert (Epsilon_Phi_Soundness (fold_subst_eps rho static_ee0, acts_eff3)) 
      by (eapply eff_sound; eauto; eapply EqualHeaps; eauto).
    assert (Epsilon_Phi_Soundness (fold_subst_eps rho static_ee, acts_eff0)) 
      by (eapply eff_sound; eauto; eapply EqualHeaps; eauto).
 
    assert (ReadOnlyPhi acts_eff1 ) 
      by (eapply ReadOnlyStaticImpliesReadOnlyPhi
           with (eps:=fold_subst_eps rho static_ee); eauto).
    assert (ReadOnlyPhi acts_eff2 ) 
      by (eapply ReadOnlyStaticImpliesReadOnlyPhi
           with (eps:=fold_subst_eps rho static_ee0); eauto).
    assert (ReadOnlyPhi acts_eff0 ) 
      by (eapply ReadOnlyStaticImpliesReadOnlyPhi
           with (eps:=fold_subst_eps rho static_ee); eauto).
    assert (ReadOnlyPhi acts_eff3 ) 
      by (eapply ReadOnlyStaticImpliesReadOnlyPhi
           with (eps:=fold_subst_eps rho static_ee0); eauto).

    assert (HR1 : heap_a ≡@{Heap} heap_b /\
                    Eff theta1 = Eff theta0 /\
                    acts_eff1 = acts_eff0).
    
    { eapply IHDyn1_1; eauto.  
      - assert (heap_a =heap_eff1) by
          ( destruct H as [HA HB]; unfold equiv, heap_equiv in HA, HB; auto).
        rewrite H38; reflexivity.
      - assert (heap_b = heap_eff0).
        destruct H11 as [HA HB]; unfold equiv, heap_equiv in HA, HB; auto.
                         rewrite H38. rewrite H38 in H13. assumption. }
            
    destruct HR1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1.  subst.
    
    assert (HR2 : heap_eff2 ≡@{Heap} heap_eff3 /\
                    Eff theta2 = Eff theta3 /\
                    acts_eff2 = acts_eff3).
    
    eapply IHDyn1_2; eauto.    
    destruct HR2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2. subst.
    
    assert (HR3 : heap_mu1 ≡@{Heap} heap_mu0 /\ v1 = v0 /\ acts_mu1 = acts_mu0).  
    eapply IHDyn1_3; eauto.
    inversion HR3 as [h_eq_3 [v_eq_3 a_eq_3]]. inversion v_eq_3.
    
    assert (HR4 : heap_mu2 ≡@{Heap} heap_mu3 /\ v2 = v3 /\ acts_mu2 = acts_mu3).  
    eapply IHDyn1_4; eauto.
    inversion HR4 as [h_eq_4 [v_eq_4 a_eq_4]]. inversion v_eq_4.

    assert (HS1 : acts_mu0 ⋞ theta0 ). 
    { eapply PairParAux; eauto.
      - assert (heap_b =heap_eff0) by
          ( destruct H11 as [HA HB]; unfold equiv, heap_equiv in HA, HB; auto).
         rewrite H38. rewrite <- H51 in H13. eassumption.
      - eapply EqualHeaps; eauto.  
    } inversion HExp_mu1.
    
    assert (HS2 : acts_mu3 ⋞ theta3 ).
    { eapply PairParAux; eauto.  
      - assert (heap_b =heap_eff3) by
          ( destruct H11 as [HA HB]; unfold equiv, heap_equiv in HA, HB; auto).
        rewrite H61. rewrite H61 in H14. eassumption.
      - eapply EqualHeaps; eauto. 
    } inversion HExp_mu2. 
    
    intuition. 
    eapply unique_heap_new with (heapa := heap_a)
                                (heapb := heap_b)
                                (theta1:=theta0)
                                (theta2:=theta3); eauto.
    * assert (Det_Trace (Phi_Par acts_mu0 acts_mu3)).
      subst. eapply Det_trace_from_theta; eauto; 
        [ eapply Dynamic_DetTrace in Dyn1_3 |
          eapply Dynamic_DetTrace in Dyn1_4]; eassumption.  
      now inversion H78.
    * assert (Det_Trace (Phi_Par acts_mu0 acts_mu3))
        by (subst; eapply Det_trace_from_theta; eauto; 
            [ eapply Dynamic_DetTrace in Dyn1_3 |
              eapply Dynamic_DetTrace in Dyn1_4]; eassumption).
      now inversion H78.
    * rewrite <- H80. rewrite <- H81. eassumption.
    * rewrite <- H80. rewrite <- H81. reflexivity.
  - inversion HTcExp; subst;
    assert ( RH1 : cheap ≡@{Heap} cheap0 /\  Bit true = Bit true /\ cacts = cacts0 ).
    eapply IHDyn1_1; eauto.
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. subst.
    assert ( RH2 : heap1 ≡@{Heap} heap2 /\ val1 = val2 /\ tacts = tacts0 ).
    
    assert (firstVal :
             exists stty',
               (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
               /\ TcHeap (cheap, stty')
               /\ TcVal (stty', Bit true, subst_rho rho Ty_Boolean)). 
    eapply ty_sound; eauto. 
    destruct firstVal as [sttyb [Weakb [TcHeapb TcVal_bit]]]; eauto.

    eapply IHDyn1_2 with (stty:=sttyb); eauto using ext_stores__env. 
    destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. subst.
    intuition.
  - inversion HTcExp; subst;
    assert ( RH1: cheap ≡@{Heap} cheap0 /\ Bit true = Bit false /\ cacts = cacts0). 
    eapply IHDyn1_1; eauto.
    destruct RH1 as [? [D ?]]. discriminate D.
  - inversion HTcExp; subst.
    assert ( RH1: cheap ≡@{Heap} cheap0 /\ Bit false = Bit true /\ cacts = cacts0). 
    eapply IHDyn1_1; eauto.
    destruct RH1 as [? [D ?]]. discriminate D.
  - inversion HTcExp; subst.
    assert ( RH1 : cheap ≡@{Heap} cheap0 /\  Bit false = Bit false /\ cacts = cacts0 ).
    eapply IHDyn1_1; eauto.
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. subst.

    assert (firstVal :
             exists stty',
               (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
               /\ TcHeap (cheap, stty')
               /\ TcVal (stty', Bit false, subst_rho rho Ty_Boolean)). 
    eapply ty_sound; eauto. 
    destruct firstVal as [sttyb [Weakb [TcHeapb TcVal_bit]]]; eauto.

    assert ( RH2 : heap1 ≡@{Heap} heap2 /\ val1 = val2 /\ facts = facts0 ).
    
    eapply IHDyn1_2  with (stty:=sttyb); eauto using ext_stores__env. 
    destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. subst.
    intuition.
  - inversion HTcExp; subst.
    assert ( RH1 : heap' ≡@{Heap} heap'0 /\  v = v0 /\ vacts = vacts0 ).
    eapply IHDyn1; eauto. 
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. 
    inversion v_eq_1.
    rewrite H in H9. inversion H9; subst.
    
    { assert (HFind :  find_H (r0, allocate_H heap' r0) heap' = 
                       find_H (r0, allocate_H heap'0 r0) heap'0). 
      - unfold find_H, update_H; simpl; rewrite h_eq_1; reflexivity.
      - split.
        + rewrite h_eq_1; reflexivity.
        + rewrite h_eq_1. split; reflexivity. }    
  - inversion HTcExp; subst.
    assert ( RH1 : heap1 ≡@{Heap} heap2 /\  
                   Loc (Rgn_Const true false s) l = Loc (Rgn_Const true false s) l0 /\ 
                   aacts = aacts0 ).
    eapply IHDyn1; eauto. 
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. 
    inversion v_eq_1.
    rewrite H in H10. inversion H10; subst.
    assert (HFind : forall k, find_H k heap1 = find_H k heap2)
          by (rewrite h_eq_1; reflexivity).
    rewrite HFind in H0.
    rewrite H11 in H0; inversion H0; subst.
    intuition.
  - inversion HTcExp; subst.
    assert ( RH1 : heap' ≡@{Heap} heap'0 /\  
                   Loc (Rgn_Const true false s) l = Loc (Rgn_Const true false s) l0 /\ 
                   aacts = aacts0 ). 
    eapply IHDyn1_1; eauto. 
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1.
    
    assert (argVal :
             exists stty',
               (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
               /\ TcHeap (heap', stty')
               /\ TcVal (stty', Loc (Rgn_Const true false s) l,
                      subst_rho rho (Ty_Ref (mk_rgn_type (Rgn_Const true false s)) t))). 
    eapply ty_sound; eauto. 
    destruct argVal as [sttyb [Weakb [TcHeapb TcVal_ea]]]; eauto.

    assert ( RH2 : heap'' ≡@{Heap} heap''0 /\ v = v0 /\ vacts = vacts0 ). 
    eapply IHDyn1_2 with  (stty:=sttyb); eauto using ext_stores__env. 
    destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2.
    
    rewrite H0 in H13; inversion H13; subst. 
    intuition.
    unfold update_H; simpl.  now rewrite h_eq_2.
  - inversion HTcExp; subst.
    assert ( RH1 : lheap  ≡@{Heap} lheap0 /\  Num va = Num va0 /\ lacts = lacts0 ). 
    eapply IHDyn1_1; eauto.  
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
    assert ( RH2 : heap1 ≡@{Heap} heap2 /\ Num vb = Num vb0 /\ racts = racts0 ).  
    
    assert (argVal :
             exists stty',
               (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
               /\ TcHeap (lheap, stty')
               /\ TcVal (stty', Num va0, subst_rho rho Ty_Natural)). 
    eapply ty_sound; eauto. 
    destruct argVal as [sttyb [Weakb [TcHeapb TcVal_ea]]]; eauto.
    
    eapply IHDyn1_2;  eauto using ext_stores__env.
    destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2. subst.
    intuition.
  - inversion HTcExp; subst.
    assert ( RH1 : lheap ≡@{Heap} lheap0 /\  Num va = Num va0 /\ lacts = lacts0 ). 
    eapply IHDyn1_1; eauto.  
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
    assert ( RH2 : heap1 ≡@{Heap} heap2 /\ Num vb = Num vb0 /\ racts = racts0 ).  
    
    assert (argVal :
             exists stty',
               (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
               /\ TcHeap (lheap, stty')
               /\ TcVal (stty', Num va0, subst_rho rho Ty_Natural)). 
    eapply ty_sound; eauto. 
    destruct argVal as [sttyb [Weakb [TcHeapb TcVal_ea]]]; eauto.
    
    eapply IHDyn1_2;  eauto using ext_stores__env.
    destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2. subst.
    intuition.  
  - inversion HTcExp; subst.
    assert ( RH1 : lheap ≡@{Heap} lheap0 /\  Num va = Num va0 /\ lacts = lacts0 ). 
    eapply IHDyn1_1; eauto.  
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
    assert ( RH2 : heap1 ≡@{Heap} heap2 /\ Num vb = Num vb0 /\ racts = racts0 ).  
    
    assert (argVal :
             exists stty',
               (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
               /\ TcHeap (lheap, stty')
               /\ TcVal (stty', Num va0, subst_rho rho Ty_Natural)). 
    eapply ty_sound; eauto. 
    destruct argVal as [sttyb [Weakb [TcHeapb TcVal_ea]]]; eauto.
    
    eapply IHDyn1_2;  eauto using ext_stores__env.
    destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2. subst.
    intuition.
  - inversion HTcExp; subst.
    assert ( RH1 : lheap ≡@{Heap} lheap0 /\  Num va = Num va0 /\ lacts = lacts0 ). 
    eapply IHDyn1_1; eauto.  
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
    assert ( RH2 : heap1 ≡@{Heap} heap2 /\ Num vb = Num vb0 /\ racts = racts0 ).  
    
    assert (argVal :
             exists stty',
               (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
               /\ TcHeap (lheap, stty')
               /\ TcVal (stty', Num va0, subst_rho rho Ty_Natural)). 
    eapply ty_sound; eauto. 
    destruct argVal as [sttyb [Weakb [TcHeapb TcVal_ea]]]; eauto.
    
    eapply IHDyn1_2;  eauto using ext_stores__env.
    destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2. subst.
    intuition.
  - rewrite H in H2. inversion H2; subst. 
    intuition.
  - rewrite H in H2. inversion H2; subst. 
    intuition.
  - rewrite H in H2. inversion H2; subst. 
    intuition.  
  - inversion HTcExp; subst.
    assert ( RH1 : heap1 ≡@{Heap} heap2
                   /\  Loc (Rgn_Const true false r) l
                       = Loc (Rgn_Const true false r0) l0
                   /\ Phi_Nil = Phi_Nil ). 
    eapply IHDyn1; eauto.  
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
    intuition.
  - inversion HTcExp; subst.
    assert ( RH1 : heap1 ≡@{Heap} heap2
                   /\ Loc (Rgn_Const true false r) l
                      = Loc (Rgn_Const true false r0) l0 /\ Phi_Nil = Phi_Nil ). 
    eapply IHDyn1; eauto.  
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
    intuition. 
  - inversion HTcExp; subst.
    assert ( RH1 : heap1 ≡@{Heap} heap2 /\  Eff effa = Eff effa0 /\ phia = phia0 ). 
    eapply IHDyn1_1; eauto.  
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
    assert ( RH2 : heap1 ≡@{Heap} heap2 /\ Eff effb = Eff effb0 /\ phib = phib0 ). 
    eapply IHDyn1_2; eauto.
    destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2. subst.
    intuition.
Qed.


Lemma EmptyTcRho :
  TcRho (R.empty RgnId, Empty_set VarId).
Proof.
  econstructor. intro.
  split; intros.
  - apply RMapP.in_find_iff in H.
    apply RMapP.empty_in_iff in H.
    contradiction.
  - contradiction.
Qed.
 
Lemma EmptyTcEnv :
    TcEnv (∅, R.empty RgnId, ∅, ∅).
Proof.
  econstructor; intros; inversion H.
Qed.

Theorem Determinism : 
  forall exp heap1 heap2 val1 val2 acts1 acts2,
    (∅, ∅, R.empty RgnId, exp) ⇓ (heap1, val1, acts1) ->
    (∅, ∅, R.empty RgnId, exp) ⇓ (heap2, val2, acts2) ->
    forall ty eff,
      TcExp (∅, Empty_set VarId, exp, ty, eff) ->
       heap1 ≡@{Heap} heap2 /\ val1 = val2 /\ acts1 = acts2.
Proof.
  intros.
  eapply DynamicDeterminism_ext with (ctxt:=∅); eauto.
  - apply TcHeapEmpty.
    + reflexivity.
    + econstructor.
 - apply EmptyTcRho. 
 - apply EmptyTcEnv.
Qed.


Lemma Determinism_new:
  forall rho  stty (e : Expr) v1 v2 ty (env : Env)  (h1 h2 : Heap) phi_1 phi_2,
    TcVal (stty, v1, ty) ->
    TcVal(stty, v2, ty) ->
    rho = R.empty nat ->
    (∅, ∅, rho, e) ⇓ (h1, v1, phi_1) ->
    (∅, ∅, rho, e) ⇓ (h2, v2, phi_2) ->
    h1 ≡@{Heap} h2 /\ v1 = v2 /\ phi_1 = phi_2.
Proof.
  intros.
  generalize dependent h2. generalize dependent phi_2. generalize dependent v2.
  generalize dependent rho. generalize dependent phi_1. generalize dependent e.
  generalize dependent env. generalize dependent h1.
  dependent induction H; subst; intros; subst.
  - generalize dependent stty.
    generalize dependent h2.
    generalize dependent v2.
    generalize dependent phi_2.
    generalize dependent env.
    dependent induction H2; intros; inversion H3; subst.
    + intuition. 
    + inversion H0; subst.
Admitted.
