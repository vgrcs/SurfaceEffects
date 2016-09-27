Require Import Coq.Arith.Peano_dec.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

Add LoadPath "." as Top.
Require Import Top.Tactics.
Require Import Top.Definitions.
Require Import Top.Keys.

Inductive TcHeap : (Heap * Sigma) -> Prop := 
  | TC_Heap_Equal : forall heap_a heap_b store,
                      TcHeap (heap_a, store) ->
                      H.Equal heap_a heap_b ->
                      TcHeap (heap_b, store)
  | TC_Heap : forall heap store,
                (forall k v,
                   (find_H k heap = Some v ->
                    exists t, find_ST k store = Some t)) ->
                (forall k t,
                   (find_ST k store = Some t ->
                    exists v, find_H k heap = Some v)) ->
                (forall k v t,
                   (find_H k heap = Some v ->
                    find_ST k store = Some t ->
                    TcVal (store, v, t))) ->
               TcHeap (heap, store).

Module HMapP := FMapFacts.Facts H.
Module HRaw := H.Raw.
Module HProofs := H.Raw.Proofs.

Module STMapP := FMapFacts.Facts ST.
Module STRaw := ST.Raw.
Module STProofs := ST.Raw.Proofs.


Lemma H_same_key_1: 
  forall t l v h, 
    H.find (elt := t) l (H.add l v h) = Some v.
Proof.
  intros; rewrite <- HMapP.find_mapsto_iff; rewrite -> HMapP.add_mapsto_iff; intuition. 
Qed. 
 
Lemma H_same_key_2:
  forall t l l0 v h,
    l = l0 -> 
    H.find (elt := t) l h = Some v ->
    H.find (elt := t) l (H.add l0 v h) = Some v.
Proof.
  intros t l l0 ty stty Heq Hfind. 
  apply HMapP.find_mapsto_iff. 
  apply HMapP.find_mapsto_iff in Hfind. 
  apply HProofs.add_1. intuition; now subst.
Qed.


Lemma ST_same_key_1:
  forall t l ty stty, 
    ST.find (elt := t) l (ST.add l ty stty) = Some ty.
Proof.
  intros; rewrite <- STMapP.find_mapsto_iff. now apply ST.add_1.
Qed. 

Lemma ST_same_key_2:
  forall t l l0 ty stty,
    l = l0 ->
    ST.find (elt := t) l stty = Some ty -> 
    ST.find (elt := t) l (ST.add l0 ty stty) = Some ty.
Proof.
  intros t l l0 ty stty Heq Hfind. 
  apply STMapP.find_mapsto_iff. 
  apply STMapP.find_mapsto_iff in Hfind. 
  apply STProofs.add_1.
  intuition; f_equal; now symmetry.
Qed.

Lemma H_diff_keys_1:
  forall t a b v v' e,   
    a <> b ->
    H.find (elt := t) a (H.add b v e) = Some v' -> 
    H.find (elt := t) a e = Some v'.
Proof.
  intros t a b v v' e Hneq Hfind. 
  rewrite <- HMapP.find_mapsto_iff in Hfind. rewrite -> HMapP.add_mapsto_iff in Hfind. intuition.
  - destruct a, b; simpl in *; subst; intuition.
  - now rewrite -> HMapP.find_mapsto_iff in H1. 
Qed.

Lemma H_diff_key_2:
  forall t a b v v' e,   
    b <> a ->
    H.find (elt := t) a e = Some v' ->
    H.find (elt := t) a (H.add b v e) = Some v'.
Proof.
  intros t a b v v' e H1 H2.  
  rewrite <- HMapP.find_mapsto_iff; rewrite -> HMapP.add_mapsto_iff.
  destruct a, b; simpl.
  right. intuition. now rewrite HMapP.find_mapsto_iff.
Qed.

Lemma ST_diff_keys_1:
  forall t a b v v' e,   
    a <> b ->
    ST.find (elt := t) a (ST.add b v e) = Some v' -> 
    ST.find (elt := t) a e = Some v'.
Proof.
  intros  t a b v v' e H1 H2. 
  rewrite <- STMapP.find_mapsto_iff in H2. rewrite -> STMapP.add_mapsto_iff in H2.
  intuition.
  - destruct a, b; simpl in *; subst; intuition.
  - now rewrite -> STMapP.find_mapsto_iff in H2.
Qed.

Lemma ST_diff_key_2:
  forall t a b v v' e,   
    b <> a ->
    ST.find (elt := t) a e = Some v' ->
    ST.find (elt := t) a (ST.add b v e) = Some v'.
Proof.
  intros. 
  rewrite <- STMapP.find_mapsto_iff. rewrite -> STMapP.add_mapsto_iff.
  destruct a, b; simpl.
  right. intuition. now rewrite STMapP.find_mapsto_iff.
Qed.

Lemma find_not_in:
  forall (x: nat * nat) (m: Heap),
    H.find x m = None -> ~ H.In x m.
Proof.
  intros; apply HMapP.not_find_in_iff in H; auto.
Qed.

Lemma stty_update_same_type:
  forall stty l0 t t0,
  ST.find (elt:=tau) l0 (ST.add l0 t stty) = Some t0 -> 
  t = t0.
Proof.
  intros stty l0 t t0 H. 
  rewrite ST_same_key_1 in H. inversion H. reflexivity.
Qed.

Lemma heap_update_same_value: 
  forall heap l0 v v0,
  H.find (elt:=Val) l0 (H.add l0 v heap) = Some v0 -> 
  v = v0.
Proof.
  intros stty l0 t t0 H. 
  rewrite H_same_key_1 in H. inversion H. reflexivity.
Qed.

Lemma heap_value_2:
  forall heap l0 v v0,
  v <> v0 ->
  H.find (elt:=Val) l0 (H.add l0 v heap) = Some v0 -> 
  H.find (elt:=Val) l0 heap = Some v0.
Proof.
  intros heap l0 v v0 H1 H2.
  rewrite H_same_key_1 in H2.
  inversion H2. contradiction.
Qed.
 
Module HFacts := FMapFacts.Facts H.
Module STFacts := FMapFacts.Facts ST.
Require Export Omega.

Lemma same_domain:
  forall stty heap, 
    TcHeap (heap, stty) ->
    (forall k v t,
       find_ST k stty = None -> 
       (forall (k0 : H.key) (v0 : Val),
          find_H k0 (update_H (k, v) heap) = Some v0 ->
          exists t0 : tau, find_ST k0 (update_ST (k, t) stty) = Some t0) /\
       (forall (k0 : ST.key) (t0 : tau),
          find_ST k0 (update_ST (k, t) stty) = Some t0 ->
          exists v0 : Val, find_H k0 (update_H (k, v) heap) = Some v0)) /\
    (forall k v t,
       find_ST k stty = Some t ->
       (forall (k0 : H.key) (v0 : Val),
          find_H k0 (update_H (k, v) heap) = Some v0 ->
          exists t0 : tau, find_ST k0 stty = Some t0) /\
       (forall (k0 : ST.key) (t0 : tau),
          find_ST k0 stty = Some t0 ->
          exists v0 : Val, find_H k0 (update_H (k, v) heap) = Some v0)).
Proof.
  intros stty heap Hhp.
  dependent induction Hhp.
  - destruct IHHhp as [TcHeap_STFind TcHeap_HFind].
    split. intros k v t HFind.
    + split; intros k0 v0 Hfind'; destruct (TcHeap_STFind k v t HFind). 
      * apply H0 with (v0:=v0). rewrite <- Hfind'.
        apply HFacts.find_m; auto. 
        apply HFacts.add_m; auto.
      * destruct (H1 k0 v0); auto. 
        { destruct k0 as [r0 l0]; destruct k as [r l]; 
          destruct (eq_nat_dec l l0); destruct (eq_nat_dec r r0); subst; 
          unfold find_H, update_H in *; simpl in *;
          try (solve [apply H_diff_keys_1 in H2; 
                       [exists x; apply H_diff_key_2; [contradict n; inversion n; reflexivity |
                                                      rewrite <- H2; apply HFacts.find_m; auto;
                                                      apply HFacts.Equal_sym; assumption] | 
                     contradict n; inversion n; reflexivity] ]).
          exists v.
            apply H_same_key_1. }
    + intros k v t STfind. 
      split; intros k0 v0 Hfind'; destruct (TcHeap_HFind k v t STfind). 
      * eapply H0. erewrite <- Hfind'. 
        apply HFacts.find_m; auto. 
        apply HFacts.add_m; auto.
      * destruct (H1 k0 v0); auto. 
        { destruct k0 as [r0 l0]; destruct k as [r l]; 
          destruct (eq_nat_dec l l0); destruct (eq_nat_dec r r0); subst; 
          unfold find_H, update_H in *; simpl in *;
          try (solve [apply H_diff_keys_1 in H2; 
                       [exists x; apply H_diff_key_2; [contradict n; inversion n; reflexivity |
                                                      rewrite <- H2; apply HFacts.find_m; auto;
                                                      apply HFacts.Equal_sym; assumption] | 
                     contradict n; inversion n; reflexivity] ]).
         exists x. rewrite Hfind' in STfind. inversion STfind; subst.  
         rewrite <- H2. 
         apply HFacts.find_m; auto. 
         apply HFacts.add_m; auto.
         apply HFacts.Equal_sym; assumption. }
  - rename H into TcHeap_STFind.
    rename H0 into TcHeap_HFind.
    rename H1 into TcHeap_tcVal.
    split.
    + intros k v t Hnone. 
      split.
      * intros k0 v0 Hfind'.
        destruct k0 as [r0 l0]; destruct k as [r l]; destruct (eq_nat_dec l l0); destruct (eq_nat_dec r r0); subst;
        try (apply H_diff_keys_1 in Hfind'; 
             [ destruct (TcHeap_STFind (r0, l0) v0 Hfind') as [t0 STfind']; exists t0; apply ST_diff_key_2 | ];
             simpl; intuition; apply n; now inversion H).
        exists t; apply ST_same_key_1.
      * intros k0 t0 STfind'.
        destruct k0 as [r0 l0]; destruct k as [r l]; destruct (eq_nat_dec l l0); destruct (eq_nat_dec r r0); subst;
        try (apply ST_diff_keys_1 in STfind';
             [ destruct (TcHeap_HFind (r0, l0) t0 STfind') as [v0 Hfind']; exists v0; apply H_diff_key_2 | ];
             simpl; intuition; apply n; now inversion H).
        exists v; apply H_same_key_1.
    + intros k v t STfind; split.
      * intros k0 v0 Hfind'.
        destruct k0 as [r0 l0]; destruct k as [r l]; destruct (eq_nat_dec l l0); destruct (eq_nat_dec r r0); subst;
        try (apply H_diff_keys_1 in Hfind';
             [destruct (TcHeap_STFind (r0, l0) v0 Hfind') as [t0 STfind']; now exists t0 |
              simpl; intuition; apply n; now inversion H]).        
        now exists t. 
      * intros k0 t0 STfind'.
        destruct k0 as [r0 l0]; destruct k as [r l]; destruct (eq_nat_dec l l0); destruct (eq_nat_dec r r0); subst;
        try (destruct (TcHeap_HFind (r0, l0) t0 STfind') as [v0 Hfind']; exists v0; apply H_diff_key_2;
             simpl; intuition; apply n; now inversion H).                                                                    
        exists v; apply H_same_key_1.
Qed.              


Lemma ExtendedEqualHeaps:
  forall l v heap_a heap_b stty,
    H.Equal heap_a heap_b ->
    TcHeap (update_H (l, v) heap_a, stty) ->
    TcHeap (update_H (l, v) heap_b, stty).
Proof.
  intros l v heap_a heap_b stty Hequal Hheap.
  assert (H : H.Equal (update_H (l, v) heap_b) (update_H (l, v) heap_a))
   by (apply HFacts.add_m; auto; apply HFacts.Equal_sym; assumption).
  dependent destruction Hheap.
  - apply HFacts.Equal_sym in H0.
    assert (H.Equal heap_a0 (update_H (l, v) heap_b)) by (eapply HFacts.Equal_trans; eauto). 
    econstructor; eauto.
  - econstructor.
    + assert (H4 : forall k, find_H k (update_H (l, v) heap_a) = find_H k (update_H (l, v) heap_b))
        by (unfold find_H, update_H; simpl; intro; apply HFacts.find_m; intuition).
      constructor.
      * intros. apply H with (v0:=v0). erewrite <- H3. 
        apply HFacts.find_m; intuition.
        eassumption. 
      * intros. rewrite <- H4. eapply H0. eassumption.
      * intros. eapply H1; [rewrite <- H3; apply HFacts.find_m; intuition | assumption ]. 
    + apply HFacts.Equal_refl. 
Qed.

Lemma update_heap_fresh:
  forall stty heap,
    TcHeap (heap, stty) ->
    (forall k v t,
       find_ST k stty = None ->
       TcVal (stty, v, t) ->
       TcHeap (update_H (k, v) heap, update_ST (k, t) stty)).
Proof.   
  intros stty heap Hhp l v t STfind' TcVal.
  generalize dependent v.
  generalize dependent l.
  generalize dependent t.
  dependent induction Hhp. 
  - intros t l STfind v tcVal. 
    eapply IHHhp in STfind; eauto.
    eapply ExtendedEqualHeaps; eauto.
  - rename H into TcHeap_STFind.
    rename H0 into TcHeap_HFind.
    rename H1 into TcHeap_tcVal.
    constructor.  
    + intros k v0 Hfind'. 
      destruct l as [r l]; destruct k as [r0 l0]. 
      destruct (eq_nat_dec l l0);  destruct (eq_nat_dec r r0); subst;
      try (solve [ unfold find_H, update_H in Hfind'; simpl in Hfind';
                   apply H_diff_keys_1 in Hfind'; [| congruence];
                   apply TcHeap_STFind in Hfind';
                   destruct Hfind';
                   exists x; unfold find_ST, update_ST; simpl;
                   apply ST_diff_key_2; [congruence | assumption]]).
      exists t; apply ST_same_key_1.
   + intros k v0 STfind''.
     destruct l as [r l]; destruct k as [r0 l0]. 
     destruct (eq_nat_dec l l0);  destruct (eq_nat_dec r r0); subst;
     try ( solve [ unfold find_ST, update_ST in STfind''; simpl in STfind'';
                   apply ST_diff_keys_1 in STfind''; [| congruence];
                   apply TcHeap_HFind in STfind'';
                   destruct STfind'';
                   exists x; unfold find_H, update_H; simpl;
                   apply H_diff_key_2; [congruence | assumption]] ).
     exists v; apply H_same_key_1. 
   + intros k v0 t0 Hfind'' STfind''.  
     apply ext_stores__val with (stty:=stty); auto.
     *  intros k1 t1 STfind'''.   
        destruct k1 as [r1 l1]; destruct l as [r0 l0].
        destruct (eq_nat_dec l0 l1);  destruct (eq_nat_dec r0 r1); subst;
        try (solve [ apply ST_diff_key_2; simpl; [congruence | assumption]]).
     *  destruct k as [r1 l1]; destruct l as [r0 l0];
        destruct (eq_nat_dec l0 l1);  destruct (eq_nat_dec r0 r1); subst;
        try (solve [       apply TcHeap_tcVal with (k:=(r1,l1));
                     [ apply H_diff_keys_1 in Hfind''; [assumption | simpl; congruence] |
                       apply ST_diff_keys_1 in STfind''; [assumption | simpl; congruence]]]). 
  
        apply heap_update_same_value in Hfind''; simpl in Hfind''; subst.
        apply stty_update_same_type in STfind''; simpl in STfind''; subst.
        assumption.
Qed.
  
Lemma update_heap_exists:
  forall stty heap,
    TcHeap (heap, stty) ->
    (forall k v t,
       find_ST k stty = Some t ->
       TcVal (stty, v, t) ->
       TcHeap (update_H (k, v) heap, stty)).
Proof. 
  intros stty heap Hhp l v t Htc STfind.
  generalize dependent t.
  generalize dependent v.
  generalize dependent l. 
  dependent induction Hhp.
  - intros. eapply IHHhp in Htc; eauto.
    eapply ExtendedEqualHeaps; eauto.
  - intros k0 v0 t0 STfind TCval.
    constructor. 
    * intros; destruct k as [r l]; destruct k0 as [r0 l0]; 
      destruct (eq_nat_dec l l0);  destruct (eq_nat_dec r r0); subst;
      try (solve [ eapply H0 in STfind;
                 destruct STfind;
                 eapply H; eauto;
                 eapply H_diff_keys_1 with (b:=(r0,l0)); eauto; congruence ] ).
    * intros; destruct k as [r l]; destruct k0 as [r0 l0]; 
      destruct (eq_nat_dec l l0);  destruct (eq_nat_dec r r0); subst;
      try (solve [ apply H0 in H2;
                   destruct H2;
                   exists x;
                   eapply H_diff_key_2 with (b:=(r0,l0)); eauto; congruence]).
      rewrite H2 in STfind.
      inversion STfind; subst.
      exists v0. apply H_same_key_1.
    * intros; destruct k as [r l]; destruct k0 as [r0 l0]; 
      destruct (eq_nat_dec l l0);  destruct (eq_nat_dec r r0); subst;
      try (solve [eapply H1;[ eapply H_diff_keys_1; eauto; simpl; congruence | assumption ]]).
      rewrite H3 in STfind. 
      inversion STfind; subst.
      apply heap_update_same_value in H2. 
      inversion H2; subst; simpl.
      assumption. 
Qed.
