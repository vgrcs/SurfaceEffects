From stdpp Require Import gmap.
From stdpp Require Import strings.

From Stdlib Require Import Program.Equality.
From Stdlib Require Import Sets.Ensembles.

Require Import theories.Runtime.Heap.
Require Import theories.Runtime.Semantics.
Require Import theories.Core.Values.
Require Import theories.Core.Regions.
Require Import theories.Core.DynamicActions.
Require Import theories.Meta.EffectFacts.
Require Import theories.Meta.TraceFacts.

Import Expressions.
Import ComputedActions.
Import Semantics.

Ltac invert_readonly :=
  repeat match goal with
  | H : ReadOnlyPhi (Phi_Seq _ _) |- _ =>
      inversion H; subst; clear H
  | H : ReadOnlyPhi (Phi_Par _ _) |- _ =>
      inversion H; subst; clear H
  end.

Ltac heap_equiv_subst :=
  repeat match goal with
  | H : ?h1 ≡@{Heap} ?h2 |- _ =>
      unfold equiv, heap_equiv in H; subst
  end.

Lemma ReadOnlyEvalDeterminism:
  forall h env rho e h1 h2 v1 v2 p1 p2,
    (h, env, rho, e) ⇓ (h1, v1, p1) ->
    (h, env, rho, e) ⇓ (h2, v2, p2) ->
    ReadOnlyPhi p1 ->
    ReadOnlyPhi p2 ->
    h1 ≡@{Heap} h2 /\ v1 = v2.
Proof.
  intros h env rho e h1 h2 v1 v2 p1 p2 HEval1.
  revert h2 v2 p2.
  dependent induction HEval1; intros h2x v2x p2x HEval2 HRO1 HRO2;
    inversion HEval2; subst;
    try solve [split; [reflexivity | reflexivity]];
    try solve [inversion HRO1];
    try solve [inversion HRO2].
  - split; [reflexivity | congruence].
  - invert_readonly.
    assert (HRf : fheap ≡@{Heap} fheap0 /\
                    Cls (env', rho', Mu f x ec' ee') =
                    Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0))
      by (eapply IHHEval1_1; eauto).
    destruct HRf as [Hfheap Hcls]. inversion Hcls; subst.
    heap_equiv_subst.
    assert (HRa : aheap ≡@{Heap} aheap0 /\ v = v0)
      by (eapply IHHEval1_2; eauto).
    destruct HRa as [Haheap Hv]. subst.
    heap_equiv_subst.
    eapply IHHEval1_3; eauto.
  - invert_readonly.
    assert (HRf : fheap ≡@{Heap} fheap0 /\
                    Cls (env', rho', Lambda x eb) =
                    Cls (env'0, rho'0, Lambda x0 eb0))
      by (eapply IHHEval1_1; eauto).
    destruct HRf as [Hfheap Hcls]. inversion Hcls; subst.
    rewrite H in H9. inversion H9; subst.
    heap_equiv_subst.
    eapply IHHEval1_2; eauto.
  - invert_readonly.
    assert (HRf :
              h2x ≡@{Heap} h2x /\
              Cls (env', rho', Mu f x ec' ee') =
              Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0))
      by (eapply IHHEval1_1; eauto).
    destruct HRf as [_ Hcls]. inversion Hcls; subst.
    assert (HRa : h2x ≡@{Heap} h2x /\ v' = v'0)
      by (eapply IHHEval1_2; eauto).
    destruct HRa as [_ Hv]. subst.
    eapply IHHEval1_3; eauto.
  - invert_readonly.
    assert (Hheap1 : h ≡@{Heap} h1).
    { eapply ReadOnlyPhi_Heap_Steps_preserves_heap
        with (phi := Phi_Par acts_mu1 acts_mu2); eauto.
      constructor; assumption. }
    assert (Hheap2 : h ≡@{Heap} h2x).
    { eapply ReadOnlyPhi_Heap_Steps_preserves_heap
        with (phi := Phi_Par acts_mu0 acts_mu3); eauto.
      constructor; assumption. }
    pose proof
      (IHHEval1_3 h env rho (Mu_App ef1 ea1) heap_mu1 v0 acts_mu1
         eq_refl eq_refl heap_mu0 v1 acts_mu0 H18 H9 H7) as HRmu1.
    pose proof
      (IHHEval1_4 h env rho (Mu_App ef2 ea2) heap_mu2 v2 acts_mu2
         eq_refl eq_refl heap_mu3 v3 acts_mu3 H19 H10 H12) as HRmu2.
    destruct HRmu1 as [_ Hv1].
    destruct HRmu2 as [_ Hv2].
    subst.
    heap_equiv_subst.
    split; reflexivity.
  - invert_readonly.
    assert (HRc : cheap ≡@{Heap} cheap0 /\ Bit true = Bit true)
      by (eapply IHHEval1_1; eauto).
    destruct HRc as [Hcheap _].
    heap_equiv_subst.
    eapply IHHEval1_2; eauto.
  - invert_readonly.
    assert (HRc : cheap ≡@{Heap} cheap0 /\ Bit true = Bit false)
      by (eapply IHHEval1_1; eauto).
    destruct HRc as [_ Hcontra]. discriminate.
  - invert_readonly.
    assert (HRc : cheap ≡@{Heap} cheap0 /\ Bit false = Bit true)
      by (eapply IHHEval1_1; eauto).
    destruct HRc as [_ Hcontra]. discriminate.
  - invert_readonly.
    assert (HRc : cheap ≡@{Heap} cheap0 /\ Bit false = Bit false)
      by (eapply IHHEval1_1; eauto).
    destruct HRc as [Hcheap _].
    heap_equiv_subst.
    eapply IHHEval1_2; eauto.
  - invert_readonly.
    match goal with
    | H : ReadOnlyPhi (Phi_Elem (DA_Alloc _ _ _)) |- _ => inversion H
    end.
  - invert_readonly.
    pose proof
      (IHHEval1 h env rho ea h1 (Loc w l) aacts
         eq_refl eq_refl h2x (Loc w l0) aacts0 H5 H6 H3) as HRa.
    destruct HRa as [Hheap Hloc]. inversion Hloc; subst.
    rewrite H in H10. inversion H10; subst.
    heap_equiv_subst.
    rewrite H0 in H11. inversion H11; subst.
    split; [reflexivity | reflexivity].
  - invert_readonly.
    match goal with
    | H : ReadOnlyPhi (Phi_Elem (DA_Write _ _ _)) |- _ => inversion H
    end.
  - invert_readonly.
    assert (HRl : lheap ≡@{Heap} lheap0 /\ Num va = Num va0)
      by (eapply IHHEval1_1; eauto).
    destruct HRl as [Hlheap HvalL]. inversion HvalL; subst.
    heap_equiv_subst.
    assert (HRr : h1 ≡@{Heap} h2x /\ Num vb = Num vb0)
      by (eapply IHHEval1_2; eauto).
    destruct HRr as [Hheap HvalR]. inversion HvalR; subst.
    split; [assumption | reflexivity].
  - invert_readonly.
    assert (HRl : lheap ≡@{Heap} lheap0 /\ Num va = Num va0)
      by (eapply IHHEval1_1; eauto).
    destruct HRl as [Hlheap HvalL]. inversion HvalL; subst.
    heap_equiv_subst.
    assert (HRr : h1 ≡@{Heap} h2x /\ Num vb = Num vb0)
      by (eapply IHHEval1_2; eauto).
    destruct HRr as [Hheap HvalR]. inversion HvalR; subst.
    split; [assumption | reflexivity].
  - invert_readonly.
    assert (HRl : lheap ≡@{Heap} lheap0 /\ Num va = Num va0)
      by (eapply IHHEval1_1; eauto).
    destruct HRl as [Hlheap HvalL]. inversion HvalL; subst.
    heap_equiv_subst.
    assert (HRr : h1 ≡@{Heap} h2x /\ Num vb = Num vb0)
      by (eapply IHHEval1_2; eauto).
    destruct HRr as [Hheap HvalR]. inversion HvalR; subst.
    split; [assumption | reflexivity].
  - invert_readonly.
    assert (HRl : lheap ≡@{Heap} lheap0 /\ Num va = Num va0)
      by (eapply IHHEval1_1; eauto).
    destruct HRl as [Hlheap HvalL]. inversion HvalL; subst.
    heap_equiv_subst.
    assert (HRr : h1 ≡@{Heap} h2x /\ Num vb = Num vb0)
      by (eapply IHHEval1_2; eauto).
    destruct HRr as [Hheap HvalR]. inversion HvalR; subst.
    split; [assumption | reflexivity].
  - rewrite H in H2. inversion H2; subst.
    split; [reflexivity | reflexivity].
  - rewrite H in H2. inversion H2; subst.
    split; [reflexivity | reflexivity].
  - rewrite H in H2. inversion H2; subst.
    split; [reflexivity | reflexivity].
  - assert (HRa :
              h1 ≡@{Heap} h2x /\
              Loc (Rgn_Const true false r) l =
              Loc (Rgn_Const true false r0) l0)
      by (eapply IHHEval1; eauto; constructor).
    destruct HRa as [Hheap Hloc]. inversion Hloc; subst.
    split; [assumption | reflexivity].
  - assert (HRa :
              h1 ≡@{Heap} h2x /\
              Loc (Rgn_Const true false r) l =
              Loc (Rgn_Const true false r0) l0)
      by (eapply IHHEval1; eauto; constructor).
    destruct HRa as [Hheap Hloc]. inversion Hloc; subst.
    split; [assumption | reflexivity].
  - invert_readonly.
    assert (HRa : h2x ≡@{Heap} h2x /\ Eff effa = Eff effa0)
      by (eapply IHHEval1_1; eauto).
    destruct HRa as [_ Heffa]. inversion Heffa; subst.
    assert (HRb : h2x ≡@{Heap} h2x /\ Eff effb = Eff effb0)
      by (eapply IHHEval1_2; eauto).
    destruct HRb as [_ Heffb]. inversion Heffb; subst.
    split; [reflexivity | reflexivity].
Qed.

Lemma EmptySoundReadOnlyBitDeterminism:
  forall h env rho e h1 h2 b1 b2 p1 p2,
    (h, env, rho, e) ⇓ (h1, Bit b1, p1) ->
    p1 ⋞ Theta_Empty ->
    (h, env, rho, e) ⇓ (h2, Bit b2, p2) ->
    ReadOnlyPhi p2 ->
    b1 = b2.
Proof.
  intros h env rho e h1 h2 b1 b2 p1 p2 HEval1 HEmpty HEval2 HRO2.
  assert (HRO1 : ReadOnlyPhi p1) by (eapply EmptySoundReadOnlyPhi; eauto).
  destruct (ReadOnlyEvalDeterminism _ _ _ _ _ _ _ _ _ _
              HEval1 HEval2 HRO1 HRO2) as [_ Hbit].
  inversion Hbit; reflexivity.
Qed.
