From stdpp Require Import gmap.

Lemma NotNoneIsSome:
  forall {A} x,
    x <> None <-> exists a : A, x = Some a.
Proof.
  intuition.
  - destruct x.
    + exists a. reflexivity.
    + contradict H. reflexivity.
  - subst. destruct H. inversion H.
Qed.

Lemma G_same_key `{Countable K} {A}:
  forall l1 l2 v (heap : gmap K A),
    l1 = l2 ->
    heap !! l1 = Some v ->
    (<[ l2:=v ]> heap) !! l1 = Some v.
Proof.
  intros l1 l2 v heap Heq Hfind.
  rewrite Heq.
  rewrite  lookup_insert_Some.
  left. split; reflexivity.
Qed.

Lemma G_update_same_value `{Countable K} {A}:
  forall (heap : gmap K A) l v v',
    (<[ l:=v ]> heap) !! l= Some v' ->
    v = v'.
Proof.
  intros heap l v v' Hfind.
  rewrite lookup_insert_Some in Hfind.
  destruct Hfind as [[Ha Hb] | [Hc Hd]].
  - assumption.
  - contradict Hc. reflexivity.
Qed.

Lemma G_diff_keys_1 `{Countable K} {A} :
  forall a b v v' (env : gmap K A),
    a <> b ->
    (<[ b:=v ]> env) !! a = Some v' ->
    env !! a = Some v'.
Proof.
  intros.
  apply lookup_insert_Some in H1.
  destruct H1 as [[Ha Hb] | [Hc Hd]].
  - contradict H0. now symmetry.
  - assumption.
Qed.

Lemma G_diff_keys_2 `{Countable K} {A}:
  forall a b v v' (env : gmap K A),
    b <> a ->
    env !! a = Some v' ->
    (<[ b:=v ]> env) !! a = Some v'.
Proof.
  intros.
  apply  lookup_insert_Some.
  right. split; assumption.
Qed.

Lemma G_diff_keys_3 `{Countable K} {A}:
  forall a b v (m : gmap K A),
    a <> b ->
    (<[ b:=v ]> m) !! a <> None ->
    m !! a <> None.
Proof.
  intros.
  contradict H1. apply lookup_insert_None. auto.
Qed.

Lemma find_rho_3 `{Countable K} {A}:
  forall x (m : gmap K A) (e : A),
    m !! x  = None -> ~ m !! x = Some e.
Proof.
  intros. apply eq_None_not_Some in H0. contradict H0.
  unfold is_Some. exists e. assumption.
Qed.
