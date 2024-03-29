Require Import Coq.Arith.Peano_dec.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sets.Ensembles.
Require Import Ascii.
Require Import String.
Require Import Coq.ZArith.Znat.
Require Import Coq.Program.Equality.

From stdpp Require Import gmap.
Require Import Definitions.Tactics.
Require Import Definitions.Keys.
Require Import Proofs.LocallyNameless.
Require Import Definitions.GHeap. 
Require Import Proofs.Determinism.
Require Import Definitions.Axioms.
Require Import Definitions.GTypes.
Require Import Definitions.DynamicActions.
Require Import Proofs.EffectFacts.
Require Import Proofs.RegionFacts.
Require Import Proofs.TypeFacts.
Require Import Proofs.HeapFacts.

Module TypeSoundness.

  Import GHeap.
  Import Regions.
  Import GTypes.
  Import StaticActions.
  Import ComputedActions.
  Import Values.
  Import Expressions.
  Import Semantics.
  Import TypeFacts.

Module RMapOrdProp := FMapFacts.OrdProperties R.

Lemma ST_find_Ext_1:
  forall k stty stty' x,
    find_ST k stty = Some x ->
    find_ST k (Functional_Map_Union_Sigma stty stty') = Some x.
Proof.
  intros.
  unfold find_ST, Functional_Map_Union_Sigma in *.
  replace (merge Merge_ST stty stty' !! k)
    with (diag_None Merge_ST (stty !! k) (stty' !! k)) by
    (rewrite lookup_merge; reflexivity).
  destruct (stty !! k).
  - inversion H; subst. unfold Merge_ST; simpl.
    destruct (stty' !! k); reflexivity.
  - inversion H.
Qed.

Lemma ST_find_Ext_2:
  forall k sttym sttya t,
    find_ST k (Functional_Map_Union_Sigma sttym sttya) = Some t ->
    find_ST k sttym = Some t.
Proof.
  intros.
  unfold find_ST, Functional_Map_Union_Sigma in *.
  assert (H1: diag_None Merge_ST (sttym !! k) (sttya !! k) = Some t) by
    (replace (diag_None Merge_ST (sttym !! k) (sttya !! k))
      with (merge Merge_ST sttym sttya !! k)
      by (rewrite lookup_merge; reflexivity); assumption).
  clear H.
  destruct (sttym !! k). 
  - destruct (sttya !! k).
    + inversion H1; subst. reflexivity.
    + inversion H1; subst. reflexivity. 
  - destruct (sttya !! k); inversion H1.
Qed.    

Lemma ST_find_Extend_Left:
  forall k stty stty' x,
    find_ST k stty = Some x <->
      find_ST k (Functional_Map_Union_Sigma stty stty') = Some x.
Proof.
  split; [apply ST_find_Ext_1 | apply ST_find_Ext_2].
Qed.
  


Lemma TcHeap_Extended:
  forall hp hp' ef1 ea1 ef2 ea2 v1 v2 env rho 
  	heap heap_mu1 heap_mu2 sttym sttya acts_mu1 acts_mu2,
    (heap, env, rho, Mu_App ef1 ea1) ⇓ (heap_mu1, v1, acts_mu1) ->
    (heap, env, rho, Mu_App ef2 ea2) ⇓ (heap_mu2, v2, acts_mu2) ->
    (Phi_Par acts_mu1 acts_mu2, hp) ==>* (Phi_Nil, hp') ->
    TcHeap (heap_mu1, sttym) ->
    TcHeap (heap_mu2, sttya) ->
    TcHeap (hp', Functional_Map_Union_Sigma sttym sttya).
Proof.
  intros hp hp' ef1 ea1 ef2 ea2 v1 v2 env rho 
  	heap heap_mu1 heap_mu2 sttym sttya acts_mu1 acts_mu2 Ha Hb Hc HTcHeap1 HTcHeap2.
  inversion HTcHeap1 as [? ? TcHeap_STFind_1 TcHeap_HFind_1 TcHeap_tcVal_1]; subst;
    inversion HTcHeap2 as [? ? TcHeap_STFind_2 TcHeap_HFind_2 TcHeap_tcVal_2]; subst;
    constructor.
  - apply H_Same_Domain in HTcHeap1. destruct HTcHeap1 as [HNone HSome].
    edestruct HSome; eauto.
    + admit.
    + admit.
  - apply H_Same_Domain in HTcHeap1. destruct HTcHeap1 as [HNone HSome].
    edestruct HSome; eauto.
    + admit.
    + admit.
  - admit.
Admitted.

Lemma ST_find_Ext_Right:
  forall (stty1 stty2 : Sigma) (k : SigmaKey) (t : Tau),
    find_ST k stty2 = Some t ->
    find_ST k (Functional_Map_Union_Sigma stty1 stty2) = Some t.
  Admitted.

Lemma TcValExtended:
  forall  stty1 stty2 v1 v2 rho ty1 ty2,
    TcVal (stty1, v1, subst_rho rho ty1) ->
    TcVal (stty2, v2, subst_rho rho ty2) ->
    TcVal (Functional_Map_Union_Sigma stty1 stty2,
        Pair (v1, v2), subst_rho rho (Ty_Pair ty1 ty2)).
Proof.
  intros.
  replace (subst_rho rho (Ty_Pair ty1 ty2))
    with (Ty_Pair (subst_rho rho ty1) (subst_rho rho ty2))
    by (now rewrite subst_rho_pair).
  econstructor. 
  - apply ext_stores__val with (stty:=stty1).
    intros.
    + now rewrite Functional_Map_Union_find.
    + assumption.
  - generalize dependent v1.
    generalize dependent ty1.
    generalize dependent stty1.
    dependent induction H0; rewrite <- x; intros.
    + constructor.
    + constructor.
    + constructor; auto. 
      apply ST_find_Ext_Right. assumption.
    + eapply TC_Cls; eauto.
      apply ext_stores__env with (stty:=stty2); eauto.
      apply ST_find_Ext_Right. 
    + constructor.  
    + constructor.
      * admit.
      * admit.
    + constructor.    
Admitted.


Lemma subst_rho_eps_aux_1 :
 forall rho rho' n x e e1 sa sa',
   lc_type_eps e ->
   lc_type_sa sa' ->
   (fold_subst_eps rho e1) = (fold_subst_eps rho' (closing_rgn_in_eps n x e)) ->
   fold_subst_sa rho sa = fold_subst_sa rho' (closing_rgn_in_sa n x sa') /\ e1 sa /\ e sa'.
Admitted.


Lemma subst_rho_open_close_rgn :
  forall rho n w v' rho' r r0 x,
    lc_type_rgn r0 ->
    find_R w rho = Some v' ->
    fold_subst_rgn rho r = fold_subst_rgn rho' (closing_rgn_in_rgn n x r0) ->
    fold_subst_rgn rho' (opening_rgn_in_rgn n (Rgn_Const true true v')
                           (closing_rgn_in_rgn n x r0))
    = fold_subst_rgn rho (opening_rgn_in_rgn n (mk_rgn_type w) r).
Proof. 
  intros rho n w v' rho' r r0 x Hlc1 HF H.
  unfold Region_in_Type in r.
  unfold Region_in_Type in r0. 
  unfold Region_in_Expr in w.
  dependent induction r; dependent induction Hlc1; simpl in *.
  - repeat rewrite subst_rho_rgn_const in *. auto.
  - destruct (RMapP.eq_dec r0 x); subst; simpl in *.
    + rewrite subst_rho_index in H. rewrite subst_rho_rgn_const in H. inversion H.
    + auto.
  - auto.
  - destruct (RMapP.eq_dec r x); subst; simpl in *.
    + rewrite subst_rho_index in H.
      destruct (subst_rho_fvar_1 rho v) as [[v0 H0] | H0];
      rewrite H0 in H; inversion H.
    + auto.
  - rewrite subst_rho_index in H. rewrite subst_rho_rgn_const in H. inversion H.
  - destruct (RMapP.eq_dec r x); subst; simpl in *.
    + repeat rewrite subst_rho_index in H. inversion H; subst.
      rewrite NPeano.Nat.eqb_refl.
      rewrite subst_rho_rgn_const.
      dependent induction w; simpl.
      * inversion HF; subst.
        rewrite subst_rho_rgn_const.
        reflexivity.
      * inversion HF. symmetry.
        apply subst_rho_fvar_2. now simpl.
    + rewrite subst_rho_index in H.
      destruct (subst_rho_fvar_1 rho' r) as [[v H0] | H0];
      rewrite H0 in H; inversion H.
Qed.

Lemma subst_rho_open_close_sa:
  forall rho n w v' rho' sa sa1 x,
    lc_type_sa sa ->
    find_R w rho = Some v' ->
    fold_subst_sa rho sa1 = fold_subst_sa rho' (closing_rgn_in_sa n x sa) ->
    fold_subst_sa rho' (opening_rgn_in_sa n (Rgn_Const true true v')
                          (closing_rgn_in_sa n x sa)) =
    fold_subst_sa rho (opening_rgn_in_sa n (mk_rgn_type w) sa1).
Proof.
  intros rho n w v' rho' sa sa1 x Hlc HF H.
  unfold fold_subst_sa.
  inversion Hlc; subst; induction sa1;
  unfold fold_subst_sa in H; inversion H; simpl in *;
  erewrite subst_rho_open_close_rgn; eauto.
Qed.    

Lemma subst_rho_open_close_eps:
  forall rho n w v' rho' e e1 x,
    lc_type_eps e ->
    find_R w rho = Some v' ->
    fold_subst_eps rho e1 = fold_subst_eps rho' (closing_rgn_in_eps n x e) ->
    fold_subst_eps rho' (opening_rgn_in_eps n (Rgn_Const true true v')
                           (closing_rgn_in_eps n x e)) =
    fold_subst_eps rho (opening_rgn_in_eps n (mk_rgn_type w) e1).
Proof.
  intros rho n w v' rho' e e1 x  Hcl1 HF H. 
  apply Extensionality_Ensembles.  
  unfold Same_set, Included.
  split; intros; unfold In in *.
  - unfold fold_subst_eps.  unfold fold_subst_eps in H0. 
    unfold opening_rgn_in_eps, closing_rgn_in_eps.
    unfold opening_rgn_in_eps, closing_rgn_in_eps in H0.
    destruct H0 as [sa [[sa' [[sa'' [H2 H3]] H4]] H5]].
    rewrite <- H5. rewrite <- H4. rewrite <- H3.
    inversion Hcl1. destruct (H0 sa'').

    assert (fold_subst_sa rho sa = fold_subst_sa rho' (closing_rgn_in_sa n x sa'')
            /\ e1 sa /\ e sa'') 
      by (eapply subst_rho_eps_aux_1; eauto).

    assert(H' : fold_subst_sa rho' (opening_rgn_in_sa n (Rgn_Const true true v') 
                  (closing_rgn_in_sa n x sa'')) =  
                fold_subst_sa rho (opening_rgn_in_sa n (mk_rgn_type w) sa)) 
    by (apply subst_rho_open_close_sa; auto; intuition).
    rewrite H'. 
    exists (opening_rgn_in_sa n (mk_rgn_type w) sa).
    intuition.
    exists sa.
    split; [ assumption | reflexivity].
 - unfold fold_subst_eps.  unfold fold_subst_eps in H0. 
   unfold opening_rgn_in_eps, closing_rgn_in_eps.
   unfold opening_rgn_in_eps, closing_rgn_in_eps in H0.
   destruct H0 as [sa [[sa' [H1 H2]] H3]].
   rewrite <- H3. rewrite <- H2.    
   exists (opening_rgn_in_sa n (Rgn_Const true true v') (closing_rgn_in_sa n x sa)). 
   inversion Hcl1. destruct (H0 sa).
   split.  
   + exists (closing_rgn_in_sa n x sa).  split; [ | reflexivity].
     exists sa. split; [ | reflexivity].  
     apply subst_rho_eps_aux_1 with (sa := sa') (sa':=sa) in H; auto.
   + eapply subst_rho_open_close_sa; eauto. 
     apply subst_rho_eps_aux_1 with (sa := sa') (sa':=sa) in H; auto.
     destruct H as [A [B C]]; auto.
Qed.
   
Lemma subst_rho_open_close :
  forall rho w v' rho' x tyr0 tyr,
    lc_type tyr0 ->
    find_R w rho = Some v' ->
    subst_rho rho' (close_var x tyr0) = subst_rho rho tyr ->
    subst_rho rho' (open (mk_rgn_type (Rgn_Const true false v')) (close_var x tyr0)) =
    subst_rho rho (open (mk_rgn_type w) tyr).
Proof.
  unfold open, close_var.
  intros rho w v' rho' x tyr0 tyr Hcl1 HF.  
  generalize dependent 0.   
  generalize dependent tyr. generalize dependent tyr0. 
  induction tyr0; induction tyr; intros n;
  simpl;
  repeat (rewrite subst_rho_natural ||
                  rewrite subst_rho_boolean ||
                  rewrite subst_rho_unit ||
                  rewrite subst_rho_forallrgn ||
                  rewrite subst_rho_effect ||
                  rewrite subst_rho_pair
         );
  try (solve [intro Z; inversion Z | intro Y; reflexivity | intro X; assumption |
              intros; rewrite subst_rho_tyref in H; inversion H |
              intros; rewrite subst_rho_arrow in H; inversion H ]).
  - inversion Hcl1; subst. 
    intros. f_equal; inversion H.  
    + erewrite <- IHtyr0_1; eauto.
    + erewrite <- IHtyr0_2; eauto. 
  - intro. symmetry in H. rewrite  subst_rho_tyref in H.
    rewrite  subst_rho_tyref in H. inversion H as [ [HR1 HR2] ].
    repeat rewrite subst_rho_tyref. f_equal.
    + erewrite subst_rho_open_close_rgn; eauto. now inversion Hcl1.
    + erewrite IHtyr0; eauto. now inversion Hcl1. 
  - intro. symmetry in H. rewrite  subst_rho_arrow in H.
    rewrite  subst_rho_tyref in H. now inversion H.
  - intro.  rewrite  subst_rho_tyref in H. rewrite  subst_rho_arrow in H. now inversion H.
  - repeat rewrite subst_rho_arrow. intro Z. inversion Z.
    f_equal.
    + rewrite <- IHtyr0_1; auto. now inversion Hcl1.
    + apply subst_rho_open_close_eps; [ now inversion Hcl1 | assumption | now inversion Z].  
    + rewrite <- IHtyr0_2; auto. now inversion Hcl1.
    + apply subst_rho_open_close_eps; [ now inversion Hcl1 | assumption | now inversion Z].  
    + rewrite <- IHtyr0_3; auto. now inversion Hcl1.
  - repeat rewrite subst_rho_forallrgn.
    intro Z; inversion Z.
     f_equal.
    + apply subst_rho_open_close_eps; [ now inversion Hcl1 | assumption | now inversion Z].
    + rewrite <- IHtyr0; auto. now inversion Hcl1.
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
    TcEnv (stty, rho, env,ctxt) ->
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
    TcRho (rho, rgns) -> not_set_elem rgns x -> ~ R.In (elt:=RgnId) x rho.
Proof.
  intros rho rgns x H1 H2.
  inversion H1; subst.
  unfold not_set_elem in H2. unfold Ensembles.Complement in H2. 
  unfold not. intro. 
  apply RMapP.in_find_iff in H. 
  apply H2. 
  eapply H0; eassumption.
Qed.  



Lemma ty_sound:
  forall e env rho hp hp' v dynamic_eff,
    (hp, env, rho, e) ⇓ (hp', v, dynamic_eff) ->
    forall stty ctxt rgns t static_eff,
      TcHeap (hp, stty) ->
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e, t, static_eff) ->
      exists stty',
        (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t')
         /\ TcHeap (hp', stty')
         /\ TcVal (stty', v, subst_rho rho t).
Proof.
  intros e env rho hp hp'  v dynamic_eff D. 
  dynamic_cases (dependent induction D) Case;
  intros stty ctxt rgns t static_eff Hhp Hrho Henv Hexp; 
  inversion Hexp; subst.    
  Case "cnt n".
    exists stty; (split; [| split]; auto). rewrite subst_rho_natural.
    econstructor; eassumption.
  Case "bool b".
    exists stty;  (split; [| split]; auto). rewrite subst_rho_boolean.
    econstructor; eassumption. 
  Case "var x".
    exists stty; (split; [| split]; auto).
    eapply ty_sound_var; eassumption. 
  Case "mu_abs".
    exists stty; (split; [| split]; auto). 
    eapply ty_sound_closure; try (solve [eassumption]). auto.
  Case "rgn_abs".
    exists stty;  (split; [| split]; auto).  
    eapply ty_sound_region_closure; try (solve [eassumption]).
  Case "mu_app".
    edestruct IHD1 as [sttym [Weak1 [TcHeap1 TcVal_mu]]]; eauto. 
    edestruct IHD2 as [sttya [Weaka [TcHeapa TcVal_arg]]]; eauto.  
    eapply ext_stores__env; eauto.  
    inversion TcVal_mu as [ | | | ? ? ? ? ? ? ? ?  TcRho_rho' TcEnv_env' TcExp_abs | | |] ; subst.      
    inversion TcExp_abs as [ | |  | ? ? ? ? ? ? ? ? ? ? ? ? TcExp_ec TcExp_ee | | | | | | | | | | | | | | | | | | | | | ]; subst.  
    rewrite <- H6 in TcVal_mu.   
    do 2 rewrite subst_rho_arrow in H6. inversion H6.
    assert (SubstEq1: subst_rho rho' tyx = subst_rho rho tya) by assumption. 
    assert (SubstEq2: subst_rho rho' tyc = subst_rho rho t) by assumption.
    rewrite <- SubstEq1 in TcVal_arg.
    unfold update_rec_E, update_rec_T in *. 
    edestruct IHD3 as [sttyb [Weakb [TcHeapb TcVal_res]]]; eauto. simpl in *.
    SCase "TcEnv".
      apply update_env. apply update_env. eapply ext_stores__env; eauto.  
      eapply ext_stores__val; eauto. eassumption.
    SCase "TcHeap".
      exists sttyb; intuition.  
    SCase "TcVal".
      edestruct IHD1 as [sttyl [Weak1 [TcHeap1 TcVal_lam]]]; eauto. 
      inversion TcVal_lam as  [ | | | ? ? ? ? ? ? ?  TcRho_rho' TcInc'  TcEnv_env' TcExp_lam | | |]; subst.   
      inversion TcExp_lam as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | | | | | | | | | | | | | |  ]; subst.  
      edestruct IHD2 as [sttyr [Weak2 [TcHeap2 TcVal_res]]]; eauto using update_env, ext_stores__env.
      apply update_rho. assumption. assumption. eapply extended_rho; eauto. 
      exists sttyr; intuition. 
      rewrite subst_rho_forallrgn in H5.
      rewrite subst_rho_forallrgn in H5.
      inversion H5.  
      unfold update_R in TcVal_res. 
      simpl in TcVal_res. rewrite subst_add_comm in TcVal_res.
      SSCase "abstraction body is well typed".
        unfold subst_in_type in TcVal_res.
        rewrite SUBST_AS_CLOSE_OPEN in TcVal_res; auto.
        erewrite subst_rho_open_close in TcVal_res; eauto. 
      SSCase "bound variable is free".
        eapply bound_var_is_fresh; eauto.
  Case "eff_app". 
    edestruct IHD1 as [sttym [Weak1 [TcHeap1 TcVal_mu]]]; eauto.
    edestruct IHD2 as [sttya [Weaka [TcHeapa TcVal_arg]]]; eauto using ext_stores__env.
    inversion TcVal_mu as  [ | | | ? ? ? ? ? ? ? TcRho_rho' TcInc' TcEnv_env' TcExp_abs | | |]; subst. 
    inversion TcExp_abs as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | | | | | | | | | | | | | |  ]; subst. 
    edestruct IHD3 as [sttyb [Weakb [TcHeapb TcVal_res]]]; eauto.
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
    exists sttyb. intuition.
    rewrite subst_rho_effect. rewrite subst_rho_effect in TcVal_res.
    assumption.
  Case "par_pair".
    edestruct IHD3 as [sttym [Weak1 [TcHeap1 TcVal_app1]]]; eauto.  
    edestruct IHD4 as [sttya [Weaka [TcHeapa TcVal_app2]]]; eauto. 
    assert (exists stty' : Sigma,
           (forall (l : SigmaKey) (t' : Tau),
            find_ST l stty = Some t' -> find_ST l stty' = Some t') /\
             TcHeap (heap_eff1, stty') /\ TcVal (stty', Eff theta1, subst_rho rho ty3))
      as HTyped3.
    eapply IHD1; eauto.
    assert (exists stty' : Sigma,
           (forall (l : SigmaKey) (t' : Tau),
            find_ST l stty = Some t' -> find_ST l stty' = Some t') /\
             TcHeap (heap_eff2, stty') /\ TcVal (stty', Eff theta2, subst_rho rho ty4))
      as HTyped4.
    eapply IHD2; eauto.
    assert (exists stty' : Sigma,
           (forall (l : SigmaKey) (t' : Tau),
            find_ST l stty = Some t' -> find_ST l stty' = Some t') /\
             TcHeap (heap_mu1, stty') /\ TcVal (stty', v1, subst_rho rho ty1))
      as HTyped1.
    eapply IHD3; eauto.
    assert (exists stty' : Sigma,
           (forall (l : SigmaKey) (t' : Tau),
            find_ST l stty = Some t' -> find_ST l stty' = Some t') /\
             TcHeap (heap_mu2, stty') /\ TcVal (stty', v2, subst_rho rho ty2))
      as HTyped2.
    eapply IHD4; eauto.
    destruct HTyped1 as[ stty1 [HA1  [HA2 HA3]]].
    destruct HTyped2 as[ stty2 [HB1  [HB2 HB3]]].
    destruct HTyped3 as[ stty3 [HC1  [HC2 HC3]]].
    destruct HTyped4 as[ stty4 [HD1  [HD2 HD3]]].  
    { exists (Functional_Map_Union_Sigma stty1 stty2).
      split.
      + intros. eapply StoreTyping_Extended; eauto.
      + split.
        * eapply TcHeap_Extended with(acts_mu1:=acts_mu1) (acts_mu2:=acts_mu2); eauto.
        * eapply TcValExtended; eauto.
    }
  Case "cond_true".
    edestruct IHD1 as [sttyb [Weakb [TcHeapvb TcVal_e0]]]; eauto. 
    edestruct IHD2 as [stty1 [Weak1 [TcHeapv1 TcVal_e1]]]; 
      eauto using ext_stores__env.
    exists stty1. intuition.
  Case "cond_false".
    edestruct IHD1 as [sttyb [Weakb [TcHeapvb TcVal_e0]]]; eauto. 
    edestruct IHD2 as [stty2 [Weak2 [TcHeapv2 TcVal_e2]]]; 
      eauto using ext_stores__env.
    exists stty2. intuition.  
  Case "new_ref e".
    edestruct IHD with (stty := stty)
                      (ctxt := ctxt)
                      (rgns := rgns)  
                      (t := t0)
                      (static_eff := veff)
      as [sttyv [Weakv [TcHeapv TcVal_v]]]; eauto.
    assert (find_H (r, allocate_H heap' r) heap' = None)
      by (apply allocate_H_fresh).
    exists (update_ST (r, allocate_H heap' r) (subst_rho rho t0) sttyv); split; [ | split].  
    SCase "Extended stores".
      intros k' t' STfind. destruct k' as [r' l']. 
      destruct (eq_nat_dec r r'); destruct (eq_nat_dec (allocate_H heap' r) l'); subst. 
      SSCase "New address must be fresh, prove by contradiction".
        apply Weakv in STfind. 
        inversion_clear TcHeapv as [? ? ?  STfind_Hfind ?].  
        destruct (STfind_Hfind (r', allocate_H heap' r') t' STfind) as [x F].
        assert (C : None = Some x) by (rewrite <- F; rewrite <- H0; reflexivity).
        discriminate. 
      SSCase "Existing addresses are well-typed 1".
        apply G_diff_keys_2; [ simpl; intuition; apply n; congruence |
                             now apply Weakv in STfind ].
      SSCase "Existing addresses are well-typed 2".
        apply G_diff_keys_2; [ simpl; intuition; apply n; congruence |
                           now apply Weakv in STfind ].
      SSCase "Existing addresses are well-typed 3".
         apply G_diff_keys_2; [simpl; intuition; apply n; congruence |
                             now apply Weakv ].
    SCase "Heap typeness".
      apply H_update_heap_fresh; eauto. 
      remember (find_ST (r, allocate_H heap' r) sttyv) as to; symmetry in Heqto.
      destruct to as [ t | ]. 
      SSCase "New address must be fresh, prove by contradiction".
        inversion_clear TcHeapv as [? ? ? STfind_Hfind ?].  
        destruct (STfind_Hfind (r, allocate_H heap' r) t Heqto) as [? ex].
        rewrite H0 in ex. discriminate.
      SSCase "Heap typeness is preserved".
        reflexivity. 
    SCase "Loc is well-typed".
      simpl in H; inversion H; subst. 
      rewrite subst_rho_tyref. unfold mk_rgn_type. rewrite subst_rho_rgn_const.
      econstructor. apply lookup_insert.
      intro.
      eapply TcVal_implies_closed in TcVal_v; eauto.
  Case "get_ref e".
    edestruct IHD with (hp' := hp')
                      (v := Loc (Rgn_Const true false s) l) 
                      (stty := stty)
                      (rgns := rgns)
                      (ctxt := ctxt)
                      (t := Ty_Ref (mk_rgn_type ((Rgn_Const true false s))) t)
                      (static_eff := aeff)
                      (dynamic_eff := aacts)
    as [sttyv [Weakv [TcHeapv TcVal_v]]]; eauto.
    exists sttyv. split; [ | split].
    SCase "HeapTyping extends".
      apply Weakv.
    SCase "Heap is well typed".
      apply TcHeapv.
    SCase "Value is well-typed".
      inversion_clear TcHeapv as [? ? ? ? HeapTcVal]. eapply HeapTcVal; eauto. 
      inversion TcVal_v; subst; simpl in H; inversion H; subst.
      rewrite subst_rho_tyref in H7. inversion H7. subst.
      assumption.
  Case "set_ref e1 e2".
    edestruct IHD1 with (hp' := heap')
                       (v := Loc (Rgn_Const true false s) l) 
                       (stty := stty)
                       (ctxt := ctxt)
                       (rgns := rgns)
                       (t := Ty_Ref (mk_rgn_type ((Rgn_Const true false s))) t0)
                       (static_eff := aeff)
                       (dynamic_eff := aacts)
       as [sttya [Weaka [TcHeapa TcVal_a]]]; eauto.
    edestruct IHD2 with (stty := sttya)
                       (ctxt := ctxt)
                       (rgns := rgns)  
                       (t := t0)
                       (static_eff := veff)
      as [sttyv [Weakv [TcHeapv TcVal_v]]]; eauto using ext_stores__env.
    exists sttyv. split; [ | split].
    SCase "HeapTyping extends".
      eapply weakening_trans; eauto.
    SCase "New heap is well typed".
      apply H_update_heap_exists with (t:= subst_rho rho t0).   
      { assumption. }
      { apply Weakv. inversion TcVal_a; subst.  
        simpl in H0; inversion H0; subst.
        rewrite subst_rho_tyref in H5. inversion H5. subst.
        assumption. }
      { assumption. }
    SCase "Result value is well-typed".
      rewrite subst_rho_unit. constructor.
  Case "nat_plus x y".
    edestruct IHD1 as [sttyx [Weakx [TcHeapvx TcVal_x]]]; eauto. 
    edestruct IHD2 as [sttyy [Weaky [TcHeapvy TcVal_y]]]; 
      eauto using ext_stores__env. 
    exists sttyy. intuition. rewrite subst_rho_natural. constructor.
  Case "nat_minus x y".
    edestruct IHD1 as [sttyx [Weakx [TcHeapvx TcVal_x]]]; eauto. 
    edestruct IHD2 as [sttyy [Weaky [TcHeapvy TcVal_y]]]; 
      eauto using ext_stores__env.
    exists sttyy. intuition. rewrite subst_rho_natural. constructor.
  Case "nat_times x y".
    edestruct IHD1 as [sttyx [Weakx [TcHeapvx TcVal_x]]]; eauto. 
    edestruct IHD2 as [sttyy [Weaky [TcHeapvy TcVal_y]]]; 
      eauto using ext_stores__env.
    exists sttyy. intuition. rewrite subst_rho_natural. constructor.
  Case "bool_eq x y".
    edestruct IHD1 as [sttyx [Weakx [TcHeapvx TcVal_x]]]; eauto. 
    edestruct IHD2 as [sttyy [Weaky [TcHeapvy TcVal_y]]]; 
      eauto using ext_stores__env.
    exists sttyy. intuition. rewrite subst_rho_boolean. constructor.
  Case "alloc_abs".
    exists stty. intuition. rewrite subst_rho_effect. constructor.
  Case "read_abs".
    exists stty. intuition. rewrite subst_rho_effect. constructor.
  Case "write_abs".
    exists stty. intuition. rewrite subst_rho_effect. constructor.
  Case "read_conc".
    exists stty. intuition.
    assert (hp = hp') by (eapply EmptyTracePreservesHeap_1; eauto; reflexivity); now subst.
    rewrite subst_rho_effect. constructor.      
  Case "write_conc".
    exists stty. intuition.
    assert (hp = hp') by (eapply EmptyTracePreservesHeap_1; eauto; reflexivity); now subst.
    rewrite subst_rho_effect. constructor. 
  Case "eff_concat".
    exists stty. intuition. rewrite subst_rho_effect. constructor.
  Case "eff_top".
    exists stty. intuition. rewrite subst_rho_effect. constructor.
  Case "eff_empty".
    exists stty. intuition. rewrite subst_rho_effect. constructor.
Qed.

End TypeSoundness.
