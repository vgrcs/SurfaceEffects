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

Lemma SameEvaluationDifferentEnvironment_2 :
   forall h env env' rho rho' ee eff static stty ctxt rgns s ty,
       (forall w, find_R w rho = find_R w rho') ->
       (forall v, find_E v env = find_E v env') ->
       ReadOnlyStatic static ->
       TcExp (stty, ctxt, rgns, ee, Ty2_Effect, static) 
       \/ 
       TcExp (stty, ctxt, rgns, ee, Ty2_Ref (Rgn2_Const true true s) ty, static) ->
       BigStep (h, env, rho, ee) (h, eff, Phi_Nil) ->
       BigStep (h, env', rho', ee) (h, eff, Phi_Nil).
Proof.
  intros.
  generalize dependent stty.
  generalize dependent s.
  generalize dependent ty.
  dependent induction H3; try (solve [constructor]).
  - intros. econstructor. rewrite H0 in H2. assumption.
  - intros. destruct H2 as [H_ | H__]. inversion H_. inversion H__.
  - intros. destruct H2 as [H_ | H__]. inversion H_. inversion H__.
  - intros. econstructor. rewrite H in H2. assumption.
  - intros. econstructor. rewrite H in H2. assumption.
  - intros. econstructor. rewrite H in H2. assumption.
  - econstructor; eauto.
    destruct H2 as [H_ | H__].
    + inversion H_; subst.
      eapply IHBigStep with (s:= r0) (ty := t); auto.
      right. eassumption.
    + inversion H__; subst.
  - econstructor; eauto.
    destruct H2 as [H_ | H__].
    + inversion H_; subst.
      eapply IHBigStep with (s:= r0) (ty := t); auto.
      right. eassumption.
    + inversion H__; subst.
Qed.

Axiom ReadOnlyEffectExpression :
  forall stty ctxt rgns ef ea ee,
    BackTriangle (stty, ctxt, rgns, Mu_App ef ea, ee) ->
    forall h fheap env env' rho rho' ec' ee' f x facts v,
      (h, env, rho, ef) ⇓ (fheap, Cls (env', rho', Mu f x ec' ee'), facts) ->
      forall p eff,
        (h, env, rho, ee) ⇓ (h, eff, p) ->
        ReadOnlyPhi p ->
        (h, update_rec_E (f, Cls (env', rho', Mu f x ec' ee')) (x, v) env', rho', ee) ⇓ (h, eff, p).

Axiom BackTriangle_intror : 
  forall stty ctxt rgns e effa effb,
    BackTriangle (stty, ctxt, rgns, e, effa) ->
    BackTriangle (stty, ctxt, rgns, e, effa ⊕ effb).

Axiom BackTriangle_introl : 
  forall stty ctxt rgns e effa effb,
    BackTriangle (stty, ctxt, rgns, e, effa) ->
    BackTriangle (stty, ctxt, rgns, e, effb ⊕ effa).

Definition Correctness_Z :
  forall h h' env rho p p' v eff stty ctxt rgns ea ee,
    (h, env, rho, ea) ⇓ (h', v, p) ->
    (h, env, rho, ee) ⇓ (h, Eff eff, p') ->
    BackTriangle (stty, ctxt, rgns, ea, ee) ->
    forall  ty static, 
      ReadOnlyPhi p' ->
      TcHeap (h, stty) ->
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) -> 
      TcExp (stty, ctxt, rgns, ea, ty, static) ->
      p ⊑ eff.
Proof.
  intros h h' env rho p p' v eff stty ctxt rgns ea ee BS1. 
  generalize dependent p'. 
  generalize dependent ee.
  generalize dependent stty.
  generalize dependent ctxt.
  generalize dependent rgns.
  generalize dependent eff.  
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
      rewrite <- H12 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H12. inversion H12. 
      rewrite <- H13 in TcVal_v'.
 
      assert (ef_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho efff, facts)).
      eapply eff_sound; eauto. 

      apply PTS_Seq. 
      + apply PTS_Seq.
        * { eapply IHBS1_1; eauto.
            inversion H0; subst.
            - now apply BackTriangle_intror.   
            - econstructor; eauto. }
        * { inversion H0; subst.
            - apply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts) in H28.
              apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1.
              eapply IHBS1_2; subst; eauto.
              + eapply ext_stores__bt; eauto.
                eapply BackTriangle_introl. 
                eapply BackTriangle_intror. 
                eassumption.
              + eapply ext_stores__env; eauto.
              + eapply ext_stores__exp; eauto.
              + assumption. 
              + admit. 
            - apply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts) in H8.
              apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1.
              eapply IHBS1_2; subst; eauto. 
              + econstructor.
                eapply ext_stores__exp; eauto.
              + eapply ext_stores__env; eauto.
              + eapply ext_stores__exp; eauto.
              + assumption.
              +  admit. }
      + eapply IHBS1_3 with (stty:=sttya); eauto.
        try (solve [inversion H6; subst; inversion_clear H0]).
        inversion H0; subst.
        * assert (HEq_1 : fheap = h). 
          apply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts) in H28.
          apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
          assumption. assumption. admit.
          assert (ea_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho effa, aacts)).
          eapply eff_sound; eauto. rewrite HEq_1. assumption.
          assert (HEq_2 : aheap = fheap).
          apply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=aacts) in H29.
          apply ReadOnlyTracePreservesHeap_1 in BS1_2. symmetry in BS1_2.
          assumption. assumption. admit.
          rewrite <- HEq_2 in HEq_1.
          rewrite HEq_1.
          eapply ReadOnlyEffectExpression; eauto.
        * assert (HEq_1 : fheap = h). 
          apply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts) in H8.
          apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
          assumption. assumption. admit.
          assert (ea_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho effa, aacts)).
          eapply eff_sound; eauto. rewrite HEq_1. assumption.
          assert (HEq_2 : aheap = fheap).
          apply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=aacts) in H8.
          apply ReadOnlyTracePreservesHeap_1 in BS1_2. symmetry in BS1_2.
          assumption. assumption. admit.
          rewrite <- HEq_2 in HEq_1.
          rewrite HEq_1.
          eapply ReadOnlyEffectExpression; eauto.
        * admit.
        * { apply update_env; simpl.  
            - eapply ext_stores__env; eauto. 
              apply update_env.  
              + eassumption.
              + eapply ext_stores__val with (stty:=sttyb); eauto.
            - eapply ext_stores__val with (stty:=sttya); eauto. }
         * eapply ext_stores__exp; eauto. 
  - 
Admitted.

