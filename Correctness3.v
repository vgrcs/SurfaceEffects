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
Require Import Effects.
Require Import Environment.
Require Import TypeSystem.
Require Import Determinism.
Require Import Definitions2.
Require Import CorrectnessLemmas.

Import TypeSoundness.
Import EffectSoundness.

Inductive EffEval : (Heap * Env * Rho * Expr) -> (Heap * Val * Phi) -> Prop:=
  | BS_Alloc_Abs   : 
      forall w r env rho heap,
        find_R w rho = Some r ->
        EffEval (heap, env, rho, AllocAbs w) (heap, Eff (Some (singleton_set (CA_AllocAbs r))), Phi_Nil)
  | BS_Read_Abs    : 
      forall w r env rho heap,
        find_R w rho = Some r ->  
        EffEval (heap, env, rho, ReadAbs w) (heap, Eff (Some (singleton_set (CA_ReadAbs r))), Phi_Nil)        
  | BS_Write_Abs   : 
      forall w r env rho heap,
        find_R w rho = Some r ->   
        EffEval (heap, env, rho, WriteAbs w) (heap, Eff (Some (singleton_set (CA_WriteAbs r))), Phi_Nil)
  | BS_Read_Conc   : 
      forall ea r l env rho (heap heap' : Heap) aacts,
        EffEval (heap, env, rho, ea) (heap', Loc (Rgn2_Const true false r) l, aacts) ->
        aacts = Phi_Nil->
        EffEval (heap, env, rho, ReadConc ea) (heap', Eff (Some (singleton_set (CA_ReadConc r l))), Phi_Nil) 
  | BS_Write_Conc  : 
      forall ea r l env rho (heap heap' : Heap) aacts,
        EffEval (heap, env, rho, ea) (heap', Loc (Rgn2_Const true false r) l, aacts) ->
        aacts = Phi_Nil ->
        EffEval (heap, env, rho, WriteConc ea) (heap', Eff (Some (singleton_set (CA_WriteConc r l))), Phi_Nil)
  | BS_Eff_Concat  : 
      forall a b env rho heap (effa effb : Theta) phia phib,
        EffEval (heap, env, rho, a) (heap, Eff effa, phia) ->
        EffEval (heap, env, rho, b) (heap, Eff effb, phib) ->
        EffEval (heap, env, rho, Concat a b) (heap, Eff (Union_Theta effa effb), Phi_Seq phia phib)
  | BS_Eff_Top     : 
      forall env rho heap,
        EffEval (heap, env, rho, Top) (heap, Eff None, Phi_Nil)
  | BS_Eff_Empty   : 
      forall  env rho heap,
        EffEval (heap, env, rho, Empty) (heap, Eff (Some empty_set), Phi_Nil).

Lemma SameEvaluationDifferentRho_1 :
   forall h env env' rho rho' p ee eff ,
       (forall w, find_R w rho = find_R w rho') ->
       EffEval (h, env, rho, ee) (h, eff, p) ->
       EffEval (h, env', rho', ee) (h, eff, p).
Proof.
  intros. 
  generalize dependent env'.
  generalize dependent rho'.
  dependent induction H0; intros. 
  - constructor. rewrite <- H0. assumption.
  - constructor. rewrite <- H0. assumption.
  - constructor. rewrite <- H0. assumption.
  - econstructor.
    + eapply IHEffEval; eauto.
    + reflexivity.
  - econstructor.
    + apply IHEffEval; auto.
    + reflexivity. 
  - econstructor.
    + apply IHEffEval1; auto.
    + apply IHEffEval2; auto.
  - constructor.
  - constructor.

Axiom RightUnionEffectTcExp :
  forall stty ctxt rgns a s ty eff1 eff2,
    TcExp (stty, ctxt, rgns, a, Ty2_Effect, eff1) ->
    TcExp (stty, ctxt, rgns, a, Ty2_Ref (Rgn2_Const true true s) ty, Union_Static_Action eff1 eff2).

Axiom LeftUnionEffectTcExp :
  forall stty ctxt rgns a eff1 eff2,
    TcExp (stty, ctxt, rgns, a, Ty2_Effect, eff2) ->
    TcExp (stty, ctxt, rgns, a, Ty2_Effect, Union_Static_Action eff1 eff2).


Lemma SameEvaluationDifferentEnvironment :
   forall h env env' rho rho' p ee eff static stty ctxt rgns s ty,
       (forall w, find_R w rho = find_R w rho') ->
       TcExp (stty, ctxt, rgns, ee, Ty2_Effect, static) 
       \/ 
       TcExp (stty, ctxt, rgns, ee, Ty2_Ref (Rgn2_Const true true s) ty, static) ->
       EffEval (h, env, rho, ee) (h, eff, p) ->
       EffEval (h, env', rho', ee) (h, eff, p).
Proof.
  intros.
  generalize dependent stty.
  generalize dependent s.
  generalize dependent ty.
  dependent induction H1. 
  - constructor. rewrite <- H. assumption.
  - constructor. rewrite <- H. assumption.
  - constructor. rewrite <- H. assumption.
  - econstructor; eauto.
    destruct H0 as [H2 | H3].
    + inversion H2; subst.
      eapply IHEffEval with (s:= r0) (ty := t); auto.
      right. eassumption.
    + inversion H3; subst.
  - econstructor; eauto.
    destruct H0 as [H2 | H3].
    + inversion H2; subst.
      eapply IHEffEval with (s:= r0) (ty := t); auto.
      right. eassumption.
    + inversion H3; subst.
  - econstructor; eauto; destruct H0 as [H2 | H3].
    + inversion H2; subst.
      eapply IHEffEval1; auto.
      right.  eapply RightUnionEffectTcExp; eauto. 
      Unshelve. assumption.
      Unshelve. assumption.
    + inversion H3.
    + inversion H2; subst.
      eapply IHEffEval2; auto.
      left.  apply LeftUnionEffectTcExp. eassumption.
      Unshelve. assumption.
      Unshelve. assumption.
    + inversion H3.
  - intros. constructor.
  - intros. constructor.
Qed.


Lemma SameEvaluationDifferentEnvironment_2 :
   forall h env env' rho rho' ee eff static stty ctxt rgns s ty,
       (forall w, find_R w rho = find_R w rho') ->
       (forall v, find_E v env = find_E v env') ->
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
  dependent induction H2; try (solve [constructor]).
  - econstructor.  rewrite H0 in H1. assumption.
  - intros. destruct H1 as [H_ | H__]. inversion H_. inversion H__.
  - intros. destruct H1 as [H_ | H__]. inversion H_. inversion H__.
  - econstructor. rewrite H in H1. assumption.
  - econstructor. rewrite H in H1. assumption.
  - econstructor. rewrite H in H1. assumption.
  - econstructor; eauto.
    destruct H1 as [H_ | H__].
    + inversion H_; subst.
      eapply IHBigStep with (s:= r0) (ty := t); auto.
      right. eassumption.
    + inversion H__; subst.
  - econstructor; eauto.
    destruct H1 as [H_ | H__].
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

Axiom ReadOnlyEffectExpression_1 :
  forall stty ctxt rgns ef ea ee,
    BackTriangle (stty, ctxt, rgns, Mu_App ef ea, ee) ->
    forall h fheap env env' rho rho' ec' ee' f x facts v,
      (h, env, rho, ef) ⇓ (fheap, Cls (env', rho', Mu f x ec' ee'), facts) ->
      forall eff,
        (h, env, rho, ee) ⇓ (h, eff, Phi_Nil) ->
        (h, update_rec_E (f, Cls (env', rho', Mu f x ec' ee')) (x, v) env', rho', ee) ⇓ (h, eff, Phi_Nil).
 
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

Definition Correctness_Y :
  forall h h' env rho p  v eff stty ctxt rgns ea ee,
    (h, env, rho, ea) ⇓ (h', v, p) ->
    (h, env, rho, ee) ⇓ (h, Eff eff, Phi_Nil) ->
    BackTriangle (stty, ctxt, rgns, ea, ee) ->
    forall  ty static, 
      TcHeap (h, stty) ->
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) -> 
      TcExp (stty, ctxt, rgns, ea, ty, static) ->
      p ⊑ eff.
Proof.
  intros h h' env rho p v eff stty ctxt rgns ea ee BS1.
  generalize dependent ee.
  generalize dependent stty.
  generalize dependent ctxt.
  generalize dependent rgns.
  generalize dependent eff.  
  dependent induction BS1;
  intros; try (solve [econstructor]).
  - try (solve [inversion H; subst; inversion_clear H0]).  
    inversion_clear H4.
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
            - apply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts) in ef_Eff.
              apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1.
              eapply IHBS1_2; subst; eauto. 
              + econstructor.
                eapply ext_stores__exp; eauto.
              + eapply ext_stores__env; eauto.
              + eapply ext_stores__exp; eauto.
              + assumption.
              +  admit. }
      + inversion H0; subst.
        * { eapply IHBS1_3 with (stty:=sttya) (ee:=ee'); eauto.  
            - induction eff; inversion H; subst.
            - eapply ext_stores__bt; eauto. 
            - { apply update_env; simpl.  
                - eapply ext_stores__env; eauto. 
                  apply update_env.  
                  + eassumption.
                  + eapply ext_stores__val with (stty:=sttyb); eauto.
                - eapply ext_stores__val with (stty:=sttya); eauto. }
            - eapply ext_stores__exp; eauto.
          }
        * { eapply IHBS1_3 with (stty:=sttya) (ee:=⊤); eauto.
            - induction eff. inversion H. econstructor.
            - econstructor.
              eapply ext_stores__exp; eauto.
            - { apply update_env; simpl.  
                - eapply ext_stores__env; eauto. 
                  apply update_env.  
                  + eassumption.
                  + eapply ext_stores__val with (stty:=sttyb); eauto.
                - eapply ext_stores__val with (stty:=sttya); eauto. }
            - eapply ext_stores__exp; eauto.
          } 
  - inversion_clear H5; subst.    
    assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Lambda x eb), 
                         subst_rho rho (Ty2_ForallRgn effr tyr))). 
    eapply ty_sound;eauto. 
    destruct clsTcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
    inversion TcVal_cls as  [ | | | ? ? ? ? ? ? ? TcRho_rho' TcEnv_env' TcExp_abs | | ]; subst.  
    inversion TcExp_abs as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | |  | | | | | | | | | | |  ]; subst.
    rewrite <- H11 in TcVal_cls.
    do 2 rewrite subst_rho_forallrgn in H11.
    inversion H11.
    
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
        induction eff. inversion H0. econstructor. econstructor.
        eassumption.
        apply update_rho; auto.
        eapply extended_rho; eauto. }
  - admit.
  - admit. 
  - inversion H0; subst. 
    + assert (cacts ⊑ Some empty_set) by (eapply IHBS1_1; eauto; constructor).
      apply EmptyUnionIsIdentity.
      apply EmptyIsNil in H5; subst.
      apply PTS_Seq; [apply PTS_Nil |].
      assert (ef_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e, Phi_Nil)).
      eapply eff_sound; eauto.
      assert (HEq_1 :  cheap = h). 
      apply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=Phi_Nil) in H15.
      apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
      assumption. constructor. admit.
      rewrite UnionEmptyWithEffIsEff.
      eapply IHBS1_2 with (ee:=efft); eauto.
      * eapply EvalTrueIsTrue; eauto; rewrite <- HEq_1 in H. 
        eassumption. 
        rewrite HEq_1. rewrite HEq_1 in BS1_1. assumption.
      * now rewrite <- HEq_1 in H1. 
    + inversion H; subst. constructor. apply PhiInThetaTop.  apply PhiInThetaTop.
-  inversion H0; subst. 
    + assert (cacts ⊑ Some empty_set) by (eapply IHBS1_1; eauto; constructor).
      apply EmptyUnionIsIdentity.
      apply EmptyIsNil in H5; subst.
      apply PTS_Seq; [apply PTS_Nil |].
      assert (ef_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e, Phi_Nil)).
      eapply eff_sound; eauto.
      assert (HEq_1 :  cheap = h). 
      apply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=Phi_Nil) in H15.
      apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
      assumption. constructor. admit.
      rewrite UnionEmptyWithEffIsEff.
      eapply IHBS1_2 with (ee:=efff); eauto.
      * eapply EvalFalseIsFalse; eauto; rewrite <- HEq_1 in H. 
        eassumption. 
        rewrite HEq_1. rewrite HEq_1 in BS1_1. assumption.
      * now rewrite <- HEq_1 in H1. 
    + inversion H; subst. constructor. apply PhiInThetaTop.  apply PhiInThetaTop.
  -
Admitted.

Axiom NonOverlappingUpdates:
 forall f x ef ea ec' ee' v v' (env env': Env) (rho rho' : Rho) (heap fheap aheap bheap : Heap) (facts aacts bacts : Phi),
   (heap, env, rho, ef) ⇓ (fheap, Cls (env', rho', Mu f x ec' ee'), facts) ->
   (fheap, env, rho, ea) ⇓ (aheap, v, aacts) ->
   (aheap, update_rec_E (f, Cls (env', rho', Mu f x ec' ee')) (x, v) env', rho', ec') 
     ⇓ (bheap, v', bacts) -> 
   (forall a b effa effb effe phia phib phie,
      facts ⊑ effa ->
      aacts ⊑ effb ->
      (heap, env, rho, a) ⇓ (heap, Eff effa, phia) ->
      (heap, env, rho, b) ⇓ (heap, Eff effb, phib) ->
      (heap, env, rho, Eff_App ef ea) ⇓ (heap, Eff effe, phie) ->
      (heap, update_rec_E (f, Cls (env', rho', Mu f x ec' ee')) (x, v) env', rho', ee') 
       ⇓ (heap, Eff (Union_Theta effa (Union_Theta effb effe)), Phi_Seq phia (Phi_Seq phib phie))).

Definition Correctness_NEW :
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
            - apply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts) in H29.
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
      + inversion H; subst; inversion H0; subst.
        * { inversion H24; subst. 
            eapply IHBS1_3 with 
                           (stty:=sttya) 
                           (ee:= ee') 
                           (p':= Phi_Seq phia (Phi_Seq phia0 phib0)); auto.  
            - 
              assert (HEq_1 : fheap = h). 
              apply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=facts) in H32.
              apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
              assumption. assumption. admit.
              assert (ea_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho effa, aacts)).
              eapply eff_sound; eauto. rewrite HEq_1. assumption.
              assert (HEq_2 : aheap = fheap).
              apply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=aacts) in H32.
              apply ReadOnlyTracePreservesHeap_1 in BS1_2. symmetry in BS1_2.
              assumption. assumption. admit. 
  

              assert (facts  ⊑ effa0) by
              (eapply IHBS1_1 with (ee:=a); eauto; inversion H1; subst; assumption).

              assert (aacts  ⊑ effa2) by
              ( eapply IHBS1_2 with (ee:=effa1) (p':=phia0); eauto;
                [rewrite HEq_1; assumption |
                 inversion H1; subst; inversion H23; subst; assumption | 
                 rewrite HEq_1; assumption]).

              rewrite <- HEq_2 in HEq_1. rewrite HEq_1. 
               
              assert (bacts  ⊑ (Union_Theta effa0 (Union_Theta effa2 effb0))). 
              { eapply IHBS1_3 with (ee:=ee') (stty:=sttya);eauto.
                - rewrite HEq_1. 
                  eapply NonOverlappingUpdates; eauto.  
                - eapply ext_stores__bt; eauto. 
                - { apply update_env; simpl.   
                    - eapply ext_stores__env; eauto. 
                      apply update_env.  
                      + eassumption.
                      + eapply ext_stores__val with (stty:=sttyb); eauto.
                    - eapply ext_stores__val with (stty:=sttya); eauto.
                  }
                - eapply ext_stores__exp; eauto.
              } 

              eapply NonOverlappingUpdates; eauto.
            - eapply ext_stores__bt; eauto. 
            - eassumption. 
            - { apply update_env; simpl.  
                - eapply ext_stores__env; eauto. 
                  apply update_env.  
                  + eassumption.
                  + eapply ext_stores__val with (stty:=sttyb); eauto.
                - eapply ext_stores__val with (stty:=sttya); eauto. }
            - eapply ext_stores__exp; eauto.
          }
        * { eapply IHBS1_3 with (stty:=sttya) (ee:=⊤); eauto.
            - econstructor.
            - econstructor.
              eapply ext_stores__exp; eauto.
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
          eassumption.
        - apply update_rho; auto.
        - eapply extended_rho; eauto. }
  - admit.
  - admit.
  - inversion H0; subst. 
    + assert (cacts ⊑ Some empty_set) by
          (eapply IHBS1_1 with (p':=Phi_Nil); eauto; constructor).
      apply EmptyUnionIsIdentity.
      apply EmptyIsNil in H6; subst.
      apply PTS_Seq; [apply PTS_Nil |].
      assert (ef_Eff : Epsilon_Phi_Soundness (fold_subst_eps rho static_e, Phi_Nil)).
      eapply eff_sound; eauto.
      assert (HEq_1 :  cheap = h). 
      apply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=Phi_Nil) in H16.
      apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
      assumption. constructor. admit.
      rewrite UnionEmptyWithEffIsEff.
      eapply IHBS1_2 with (ee:=efft); eauto.
      * eapply EvalTrueIsTrue; eauto; rewrite <- HEq_1 in H. 
        eassumption. 
        rewrite HEq_1. rewrite HEq_1 in BS1_1. assumption.
      * now rewrite HEq_1.  
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
      apply ReadOnlyStaticImpliesReadOnlyPhi with (phi:=Phi_Nil) in H16.
      apply ReadOnlyTracePreservesHeap_1 in BS1_1. symmetry in BS1_1. 
      assumption. constructor. admit.
      rewrite UnionEmptyWithEffIsEff.
      eapply IHBS1_2 with (ee:=efff); eauto.
      * eapply EvalFalseIsFalse; eauto; rewrite <- HEq_1 in H. 
        eassumption. 
        rewrite HEq_1. rewrite HEq_1 in BS1_1. assumption.
      * now rewrite HEq_1. 
    + inversion H; subst. constructor. apply PhiInThetaTop.  apply PhiInThetaTop.
  - inversion H1; subst; inversion H2; subst.
    apply EnsembleUnionComp.  
     + eapply IHBS1; eauto. inversion H3. assumption.
     + inversion H15; subst.
       apply PTS_Elem. apply DAT_Alloc_Abs.
       rewrite H in H9. inversion H9.
       apply In_singleton.
     + apply PhiInThetaTop.  
  - inversion H2; subst.
    + inversion H1; subst. 
      apply EnsembleUnionComp.
      * eapply IHBS1; eauto. 
        inversion H3; subst. assumption.
      * apply PTS_Elem. inversion H18; subst.
        rewrite H in H9; inversion H9.
        apply DAT_Read_Abs. apply In_singleton.
    + inversion H1; subst.
      assert (aacts ⊑ Some empty_set) by (eapply IHBS1; eauto; constructor).
      apply PTS_Seq.
      * apply EmptyInAnyTheta. assumption.
      * apply PTS_Elem.
        simpl in H; inversion H; subst.
        assert ( HD : (h, Loc (Rgn2_Const true false r1) l0, Phi_Nil) 
                      =  (h', Loc (Rgn2_Const true false r) l, aacts))
          by (eapply DynamicDeterminism; eauto). inversion HD; subst. 
        apply DAT_Read_Conc. apply In_singleton.
    + econstructor. 
      * inversion H9; subst.
        eapply IHBS1; eauto.  econstructor. 
        eassumption.
      * inversion H1; subst.    
        apply PTS_Elem. apply DAT_Top.
  - admit.  
  - admit. 
  - admit.  
  - admit.
  - admit.
  - admit. 
Admitted.

 
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
          { eapply SameEvaluationDifferentEnvironment_.
            - admit.
            - admit.
            - eauto.
          }
          (* eapply ReadOnlyEffectExpression. eauto. *)
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

