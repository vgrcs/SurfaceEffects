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

Add LoadPath "." as Top0.
Require Import Top0.Keys.
Require Import Top0.Heap.
Require Import Top0.Environment.
Require Import Top0.Definitions.
Require Import Top0.CorrectnessLemmas.
Require Import Top0.Determinism.
Require Import Top0.TypeSystem.


Axiom AllocAddressIsDeterministic:
  forall r0 l l0 heap,
    find_H (r0, l0) heap = find_H (r0, l) heap ->
    l = l0.

Theorem DynamicDeterminism_ext : 
  forall heap_a heap_b env rho exp heap1 heap2 val1 val2 acts1 acts2,
    H.Equal heap_a heap_b ->
    (heap_a, env, rho, exp) ⇓ (heap1, val1, acts1) ->
    (heap_b, env, rho, exp) ⇓ (heap2, val2, acts2) ->
    H.Equal heap1 heap2 /\ val1 = val2 /\ acts1 = acts2.
Proof.
  intros heap_a heap_b env rho exp heap1 heap2 val1 val2 acts1 acts2 Heq Dyn1. 
  generalize dependent acts2; generalize dependent val2; generalize dependent heap2. 
  generalize dependent heap_b. 
  dependent induction Dyn1; intros heap_b Heq heap2 val2 acts2 Dyn2; inversion Dyn2; subst;
  try (solve [intuition]).
  - intuition. rewrite H in H1. inversion H1; subst. reflexivity.
  - assert ( RH1 : H.Equal fheap fheap0 /\ Cls (env', rho', Mu f x ec' ee') = 
                                           Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0) /\ facts = facts0 ).
    eapply IHDyn1_1; eauto. 
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
    assert ( RH2 : H.Equal aheap aheap0 /\ v = v0 /\ aacts = aacts0) by (eapply IHDyn1_2; eauto).
    destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]; subst. 
    
    assert ( RH3 : H.Equal heap1 heap2 /\ val1 = val2 /\ bacts = bacts0).
    eapply IHDyn1_3; eauto. 
    destruct RH3 as [h_eq_3 [v_eq_3 a_eq_3]]; subst.
    auto.
  - assert ( RH1 : H.Equal fheap fheap0 /\  Cls (env', rho', Lambda x eb) =
                                            Cls (env'0, rho'0, Lambda x0 eb0) /\ facts = facts0 ).
    eapply IHDyn1_1; eauto.
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
    rewrite H in H9. inversion H9; subst.

    assert ( RH2 : H.Equal heap1 heap2 /\ val1 = val2 /\ bacts = bacts0).
    eapply IHDyn1_2; eauto.
    destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. subst.
    intuition.
  - assert ( RH1 : H.Equal heap1 heap2 /\  Cls (env', rho', Mu f x ec' ee') =
                                           Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0) /\ facts = facts0 ).
    eapply IHDyn1_1; eauto.
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
    
    assert ( RH2 : H.Equal heap1 heap2 /\  v' = v'0 /\ aacts = aacts0 ).
    eapply IHDyn1_2; eauto.
    destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2. subst.

    assert ( RH3 : H.Equal heap1 heap2 /\  val1 = val2 /\ bacts = bacts0 ).
    eapply IHDyn1_3; eauto.
    destruct RH3 as [h_eq_3 [v_eq_3 a_eq_3]]. inversion v_eq_3. subst.
    intuition.
  - assert (HR1 : H.Equal heap_a heap_b /\ Eff theta1 = Eff theta0 /\ acts_eff1 = acts_eff0) 
      by (eapply IHDyn1_1; eauto).
    destruct HR1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
    assert (HR2 : H.Equal heap_a heap_b /\ Eff theta2 = Eff theta3 /\ acts_eff2 = acts_eff3) 
      by (eapply IHDyn1_2; eauto).
    destruct HR2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2. subst.
    assert (HR3 : H.Equal heap_mu1 heap_mu0 /\ Num v1 = Num v0 /\ acts_mu1 = acts_mu0)  
      by (eapply IHDyn1_3; eauto). 
    inversion HR3 as [h_eq_3 [v_eq_3 a_eq_3]]. inversion v_eq_3. 
    assert (HR4 : H.Equal heap_mu2 heap_mu3 /\ Num v2 = Num v3 /\ acts_mu2 = acts_mu3)  
      by (eapply IHDyn1_4; eauto).  
    inversion HR4 as [h_eq_4 [v_eq_4 a_eq_4]]. inversion v_eq_4. subst.
    intuition. 
    eapply unique_heap_new with (heapa := heap_a) (heapb := heap_b) (theta1:=theta0) (theta2:=theta3). 
    + eauto. (* from correctness *)
    + eauto. (* from correctness *) 
    + eauto. (* from correctness *) 
    + assert (Det_Trace (Phi_Par acts_mu0 acts_mu3))
        by (eapply Det_trace_from_theta; eauto; 
            [ apply Dynamic_DetTrace in Dyn1_3 | apply Dynamic_DetTrace in Dyn1_4]; assumption).
      now inversion H12.
    + assert (Det_Trace (Phi_Par acts_mu0 acts_mu3))
        by (eapply Det_trace_from_theta; eauto; 
            [ apply Dynamic_DetTrace in Dyn1_3 | apply Dynamic_DetTrace in Dyn1_4]; assumption).
      now inversion H12.
    + assumption.
    + assumption.
    + assumption.  
  -  assert ( RH1 : H.Equal cheap cheap0 /\  Bit true = Bit true /\ cacts = cacts0 ).
     eapply IHDyn1_1; eauto.
     destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. subst.
     assert ( RH2 : H.Equal heap1 heap2 /\ val1 = val2 /\ tacts = tacts0 ).
     eapply IHDyn1_2; eauto.
     destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. subst.
     intuition.
   - assert ( RH1: H.Equal cheap cheap0 /\ Bit true = Bit false /\ cacts = cacts0). 
     eapply IHDyn1_1; eauto.
     destruct RH1 as [? [D ?]]. discriminate D.
   - assert ( RH1: H.Equal cheap cheap0 /\ Bit false = Bit true /\ cacts = cacts0). 
     eapply IHDyn1_1; eauto.
     destruct RH1 as [? [D ?]]. discriminate D.
   - assert ( RH1 : H.Equal cheap cheap0 /\  Bit false = Bit false /\ cacts = cacts0 ).
     eapply IHDyn1_1; eauto.
     destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. subst.
     assert ( RH2 : H.Equal heap1 heap2 /\ val1 = val2 /\ facts = facts0 ).
     eapply IHDyn1_2; eauto.
     destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. subst.
     intuition.
   - assert ( RH1 : H.Equal heap' heap'0 /\  v = v0 /\ vacts = vacts0 ).
     eapply IHDyn1; eauto. 
     destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. subst.
     rewrite H in H10. inversion H10; subst.
     assert (H5 : forall k, find_H k heap' = find_H k heap'0)
       by (unfold find_H, update_H; simpl; intro; apply HFacts.find_m; intuition).
     rewrite H5 in H0. 
     rewrite <-H11 in H0. symmetry in H0.
     apply AllocAddressIsDeterministic in H0; subst.
     intuition.
     unfold update_H; simpl. apply HMapP.add_m; auto.
   - assert ( RH1 : H.Equal heap1 heap2 /\  Loc w l = Loc w l0 /\ aacts = aacts0 ).
     eapply IHDyn1; eauto. 
     destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. 
     inversion v_eq_1.
     rewrite H in H10. inversion H10; subst.
     assert (H5 : forall k, find_H k heap1 = find_H k heap2)
       by (unfold find_H, update_H; simpl; intro; apply HFacts.find_m; intuition).
     rewrite H5 in H0.
     rewrite H11 in H0; inversion H0; subst.
     intuition.
   - assert ( RH1 : H.Equal heap' heap'0 /\  Loc w l = Loc w l0 /\ aacts = aacts0 ). 
     eapply IHDyn1_1; eauto. 
     destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1.
     assert ( RH2 : H.Equal heap'' heap''0 /\ v = v0 /\ vacts = vacts0 ). 
     eapply IHDyn1_2; eauto. 
     destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2.
     rewrite H in H11; inversion H11; subst. 
     intuition.
     unfold update_H; simpl. apply HMapP.add_m; auto. 
   - assert ( RH1 : H.Equal lheap lheap0 /\  Num va = Num va0 /\ lacts = lacts0 ). 
     eapply IHDyn1_1; eauto.  
     destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
     assert ( RH2 : H.Equal heap1 heap2 /\ Num vb = Num vb0 /\ racts = racts0 ). 
     eapply IHDyn1_2; eauto.
     destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2. subst.
     intuition.
   - assert ( RH1 : H.Equal lheap lheap0 /\  Num va = Num va0 /\ lacts = lacts0 ). 
     eapply IHDyn1_1; eauto.  
     destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
     assert ( RH2 : H.Equal heap1 heap2 /\ Num vb = Num vb0 /\ racts = racts0 ). 
     eapply IHDyn1_2; eauto.
     destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2. subst.
     intuition.
   - assert ( RH1 : H.Equal lheap lheap0 /\  Num va = Num va0 /\ lacts = lacts0 ). 
     eapply IHDyn1_1; eauto.  
     destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
     assert ( RH2 : H.Equal heap1 heap2 /\ Num vb = Num vb0 /\ racts = racts0 ). 
     eapply IHDyn1_2; eauto.
     destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2. subst.
     intuition.
   - assert ( RH1 : H.Equal lheap lheap0 /\  Num va = Num va0 /\ lacts = lacts0 ). 
     eapply IHDyn1_1; eauto.  
     destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
     assert ( RH2 : H.Equal heap1 heap2 /\ Num vb = Num vb0 /\ racts = racts0 ). 
     eapply IHDyn1_2; eauto.
     destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2. subst.
     intuition.
   - rewrite H in H1. inversion H1; subst. 
     intuition.
   - rewrite H in H1. inversion H1; subst. 
     intuition.
   - rewrite H in H1. inversion H1; subst. 
     intuition.
   - assert ( RH1 : H.Equal heap1 heap2 /\  Loc (Rgn2_Const true false r) l = 
                                            Loc (Rgn2_Const true false r0) l0 /\ Phi_Nil = Phi_Nil ). 
     eapply IHDyn1; eauto.  
     destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
     intuition.
   - assert ( RH1 : H.Equal heap1 heap2 /\  Loc (Rgn2_Const true false r) l = 
                                            Loc (Rgn2_Const true false r0) l0 /\ Phi_Nil = Phi_Nil ). 
     eapply IHDyn1; eauto.  
     destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
     intuition. 
   - assert ( RH1 : H.Equal heap1 heap2 /\  Eff effa = Eff effa0 /\ phia = phia0 ). 
     eapply IHDyn1_1; eauto.  
     destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
     assert ( RH2 : H.Equal heap1 heap2 /\ Eff effb = Eff effb0 /\ phib = phib0 ). 
     eapply IHDyn1_2; eauto.
     destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2. subst.
     intuition.
Qed.


