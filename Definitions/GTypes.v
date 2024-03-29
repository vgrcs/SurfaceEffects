From stdpp Require Import gmap.
Require Import Coq.Sets.Ensembles.
Require Import Definitions.Keys.
Require Import Definitions.Regions.
Require Import Definitions.ComputedActions.
Require Import Definitions.StaticActions.
Require Import Definitions.Values.
Require Import Definitions.Expressions.


Inductive Tau :=
  | Ty_Natural : Tau
  | Ty_Boolean : Tau
  | Ty_Effect  : Tau
  | Ty_Unit    : Tau
  | Ty_Pair    : Tau -> Tau -> Tau
  | Ty_Ref     : Region_in_Type -> Tau -> Tau
  | Ty_Arrow   : Tau -> Epsilon -> Tau -> Epsilon -> Tau -> Tau
  | Ty_ForallRgn : Epsilon -> Tau -> Tau.

Definition SigmaKey := prod nat nat.
Definition Sigma := gmap SigmaKey Tau.
Definition Gamma := gmap VarId Tau.
Definition Omega : Type := Ensemble VarId.


Definition keys_eq x y := Nat.eq (fst x) (fst y) /\ Nat.eq (snd x) (snd y).

Lemma keys_eq_dec : forall (k : nat * nat) (k' : nat * nat),
    { keys_eq k k' } + { ~ keys_eq k k' }.
Proof.
  intros. unfold keys_eq, Nat.eq. destruct k as (r, l);
    destruct k' as (r', l'); subst; simpl.
  destruct (eq_nat_dec r r'); destruct (eq_nat_dec l l'). 
  - left. unfold Nat.eq. auto.
  - right. intro. contradict n. intuition.
  - right. intro. contradict n. intuition.
  - right. intro. contradict n. intuition.
Qed.    


Definition find_ST (k: SigmaKey) (m: Sigma) : option Tau := m !! k.
Definition update_ST (k: SigmaKey) (t: Tau) (m: Sigma) :=  <[ k := t ]>  m.


Definition Merge_ST (v1 v2 : option Tau) : option Tau :=
  match (v1, v2) with
  | (None, _) => None
  | (Some v, _) => Some v
end.

Definition Functional_Map_Union_Sigma (stty1 stty2 : Sigma) : Sigma
  := merge Merge_ST stty1 stty2.


Definition find_T (k: VarId) (m: Gamma) : option Tau :=  m !! k.

Definition update_T (p: VarId * Tau) (m : Gamma) := <[ fst p := snd p ]>  m.

Definition update_rec_T (f: VarId * Tau) (x: VarId * Tau) m :=
  let m' := update_T f m
  in update_T x m'.


(** begin of free regions **)
Definition free_rgn_vars_in_rgn (rgn: Region_in_Type) : Ensemble VarId :=
  match rgn with
  | Rgn_Const _ _ _ => empty_set
  | Rgn_FVar _ _ n => singleton_set n
  | Rgn_BVar _ _ _ => empty_set
  end.

Definition free_region (rgn: Region_in_Type) : Ensemble VarId := free_rgn_vars_in_rgn rgn.


Definition free_rgn_vars_in_sa (sa: StaticAction) : Ensemble VarId :=
  match sa with
  | SA_Alloc rgn => free_rgn_vars_in_rgn rgn
  | SA_Read rgn => free_rgn_vars_in_rgn rgn
  | SA_Write rgn => free_rgn_vars_in_rgn rgn
  end.


Definition free_rgn_vars_in_eps (eps: Epsilon) : Ensemble VarId := 
  fun n => exists (sa : StaticAction),
             eps sa /\ (free_rgn_vars_in_sa sa) n.


Fixpoint frv (t: Tau) : Ensemble VarId :=
  match t with
  | Ty_Natural    => empty_set
  | Ty_Boolean    => empty_set
  | Ty_Effect     => empty_set
  | Ty_Unit       => empty_set
  | Ty_Pair t1 t2 => set_union (frv t1) (frv t2)                        
  | Ty_Ref rgn ty => set_union (free_rgn_vars_in_rgn rgn) (frv ty)
  | Ty_Arrow aty ceff crty eeff erty =>
      set_union (frv aty)
        (set_union (set_union (free_rgn_vars_in_eps ceff)
                      (free_rgn_vars_in_eps eeff))
           (set_union (frv crty)(frv erty)))
  | Ty_ForallRgn eff rty =>
      set_union (free_rgn_vars_in_eps eff) (frv rty)                                      
  end.

Fixpoint not_set_elem_frv (t: Tau) x : Prop :=
  match t with
    | Ty_Natural    => True
    | Ty_Boolean    => True 
    | Ty_Effect     => True
    | Ty_Unit       => True
    | Ty_Pair t1 t2 => (not_set_elem (frv t1) x) /\ (not_set_elem (frv t2) x)  
    | Ty_Ref rgn ty => (not_set_elem (free_rgn_vars_in_rgn rgn) x) /\ 
                       (not_set_elem (frv ty) x)
    | Ty_Arrow aty ceff crty eeff erty 
      => (not_set_elem (frv aty) x) /\
         (not_set_elem (free_rgn_vars_in_eps ceff) x) /\
         (not_set_elem (free_rgn_vars_in_eps eeff) x) /\
         (not_set_elem (frv crty) x) /\
         (not_set_elem (frv erty) x)
    | Ty_ForallRgn eff rty => (not_set_elem (free_rgn_vars_in_eps eff) x) /\
                              (not_set_elem (frv rty) x)
  end.


Notation "x '#' t" := (not_set_elem (frv t) x) (at level 60).


(** locally closed **)
Inductive lc_type_rgn : Region_in_Type -> Prop :=
     | lc_rgn_const : forall r, lc_type_rgn (Rgn_Const true true r)
     | lc_rgn_fvar  : forall r, lc_type_rgn (Rgn_FVar true true r).

Inductive lc_type_sa : StaticAction -> Prop :=
     | lc_sa_alloc : forall r, lc_type_rgn (r) -> lc_type_sa (SA_Alloc r)
     | lc_sa_read  : forall r, lc_type_rgn (r) -> lc_type_sa (SA_Read r)
     | lc_sa_write : forall r, lc_type_rgn (r) -> lc_type_sa (SA_Write r).

Inductive lc_type_eps : Epsilon -> Prop :=
     | lc_eps : forall eps, (forall (sa : StaticAction), eps sa /\ lc_type_sa (sa)) ->
                            lc_type_eps (eps).


Definition mk_rgn_type (u: Region_in_Expr) : Region_in_Type
 := match u with
      | Rgn_Const fv bv n => Rgn_Const true true n
      | Rgn_FVar c bv n => Rgn_FVar true true n
      | Rgn_BVar c fv n => Rgn_BVar true true n                              
    end.

Definition lc u := lc_type_rgn (mk_rgn_type u).


(** begin of openings **)
Definition opening_rgn_in_rgn (k : nat) (u: Region_in_Type) (t: Region_in_Type) : Region_in_Type
 := match t with
    | Rgn_Const _ _ _ => t
    | Rgn_FVar _ _ _ => t
    | Rgn_BVar _ _ n => if (Nat.eqb n k) then u else t
    end.

Definition opening_rgn_in_sa (k : nat) (u: Region_in_Type) (sa: StaticAction) : StaticAction :=
  match sa with
  | SA_Alloc rgn => SA_Alloc (opening_rgn_in_rgn k u rgn)
  | SA_Read rgn  => SA_Read (opening_rgn_in_rgn k u rgn)
  | SA_Write rgn => SA_Write (opening_rgn_in_rgn k u rgn)
  end.

Definition opening_rgn_in_eps (k : nat) (u: Region_in_Type) (eps: Epsilon) : Epsilon := 
  fun sa => exists sa', eps sa' /\ opening_rgn_in_sa k u sa' = sa.

Fixpoint opening_rgn_exp (k: nat) (u: Region_in_Type) (t: Tau) {struct t} : Tau :=
  match t with
  | Ty_Natural => t
  | Ty_Boolean => t
  | Ty_Effect  => t
  | Ty_Unit    => t                     
  | Ty_Pair ty1 ty2  =>  Ty_Pair (opening_rgn_exp k u ty1)  (opening_rgn_exp k u ty2) 
  | Ty_Ref rgn ty => Ty_Ref (opening_rgn_in_rgn k u rgn) (opening_rgn_exp k u ty)
  | Ty_Arrow aty ceff crty eeff erty =>
      Ty_Arrow (opening_rgn_exp k u aty) (opening_rgn_in_eps k u ceff)
        (opening_rgn_exp k u crty) (opening_rgn_in_eps k u eeff)
        (opening_rgn_exp k u erty)
  | Ty_ForallRgn eff rty =>
      Ty_ForallRgn (opening_rgn_in_eps (S k) u eff) (opening_rgn_exp (S k) u rty)
  end.


Definition open_rgn_eff (u: Region_in_Type)  (eps: Epsilon) : Epsilon := opening_rgn_in_eps 0 u eps.
Definition open (u: Region_in_Type)  (t: Tau) : Tau := opening_rgn_exp 0 u t.
Definition open_var (t : Tau) (x : VarId) : Tau :=
  let rgn_fvar := Rgn_FVar true true x
  in opening_rgn_exp 0 (rgn_fvar) t.


(** begin of closings **)
Definition closing_rgn_in_rgn (k : nat) (x: VarId) (t: Region_in_Type) : Region_in_Type
 := match t with
    | Rgn_Const _ _ _ => t
    | Rgn_FVar _ _ n  => if AsciiVars.eq_dec n x then (Rgn_BVar true true k) else t
    | Rgn_BVar _ _ _  => t
    end.

Definition closing_rgn_in_sa (k : nat) (x: VarId) (sa: StaticAction) : StaticAction :=
  match sa with
  | SA_Alloc rgn => SA_Alloc (closing_rgn_in_rgn k x rgn)
  | SA_Read rgn  => SA_Read (closing_rgn_in_rgn k x rgn)
  | SA_Write rgn => SA_Write (closing_rgn_in_rgn k x rgn)
  end.

Definition closing_rgn_in_eps(k : nat) (x: VarId) (eps: Epsilon) : Epsilon :=
  fun sa => exists sa', eps sa' /\ closing_rgn_in_sa k x sa' = sa.

Fixpoint closing_rgn_exp (k: nat) (x: VarId) (t: Tau) {struct t} : Tau :=
  match t with
  | Ty_Natural => t
  | Ty_Boolean => t
  | Ty_Effect  => t
  | Ty_Unit    => t
  | Ty_Pair t1 t2 => Ty_Pair  (closing_rgn_exp k x t1) (closing_rgn_exp k x t2)
  | Ty_Ref rgn ty => Ty_Ref (closing_rgn_in_rgn k x rgn) (closing_rgn_exp k x ty)
  | Ty_Arrow aty ceff crty eeff erty =>
      Ty_Arrow (closing_rgn_exp k x aty)
        (closing_rgn_in_eps k x ceff) (closing_rgn_exp k x crty)
        (closing_rgn_in_eps k x eeff) (closing_rgn_exp k x erty)
  | Ty_ForallRgn eff rty =>
      Ty_ForallRgn (closing_rgn_in_eps (S k) x eff) (closing_rgn_exp (S k) x rty)
  end.


Definition close_var (x : VarId) (t : Tau) := closing_rgn_exp 0 x t.
Definition close_var_eff (x : VarId) (eps : Epsilon) := closing_rgn_in_eps 0 x eps.
(** end of closings **)



Inductive lc_type : Tau -> Prop :=
  | lc_natural : lc_type Ty_Natural
  | lc_pair    : forall t1 t2,
                   lc_type t1 -> lc_type t2 -> lc_type (Ty_Pair t1 t2)
  | lc_ref     : forall r t,
                   lc_type_rgn r -> lc_type t -> lc_type (Ty_Ref r t)
  | lc_arrow   : forall aty ceff crty eeff erty,
                   lc_type aty -> lc_type_eps ceff -> lc_type crty ->
                   lc_type_eps eeff -> lc_type erty ->
                   lc_type (Ty_Arrow aty ceff crty eeff erty)
  | lc_forall  : forall L eff rty,
                   (forall x, not_set_elem L x -> lc_type (open_var rty x)) ->
                   lc_type_eps eff ->
                   lc_type rty ->
                   lc_type (Ty_ForallRgn eff rty).
(** end of locally closed **)



Inductive TcRho : (Rho * Omega) -> Prop :=
  | TC_Rho : forall rho rgns,
               (forall r, R.find r rho <> None <-> set_elem rgns r) ->
               TcRho (rho, rgns).

Inductive TcInc : (Gamma * Omega) -> Prop :=
     | Tc_Inc : forall ctxt rgns, 
                  (forall x t, 
                     find_T x ctxt = Some t -> included (frv t) rgns) ->
                  TcInc (ctxt, rgns). 

Inductive TcRgn : (Omega * Region_in_Expr) -> Prop :=
  | TC_Rgn_Const : forall rgns s,
                      TcRgn (rgns, Rgn_Const true false s)
  | TC_Rgn_Var   : forall rgns r,
                      set_elem rgns r ->
                      TcRgn (rgns, Rgn_FVar true false r).      



(** begin of substitutions **)


Definition subst_rgn  (z : VarId) (u : Region_in_Expr) (t: Region_in_Type) : Region_in_Type :=
  match t with
    | Rgn_Const _ _ r => t
    | Rgn_FVar _ _ r  => if (AsciiVars.eq_dec z r) then mk_rgn_type u else t 
    | Rgn_BVar _ _ _  => t
  end.


Definition subst_sa (z : VarId) (u : Region_in_Expr) (t: StaticAction) : StaticAction :=
 match t with
  | SA_Alloc rgn => SA_Alloc (subst_rgn z u rgn)
  | SA_Read rgn  => SA_Read  (subst_rgn z u rgn)
  | SA_Write rgn => SA_Write (subst_rgn z u rgn)
 end.

Definition subst_eps  (z : VarId) (u : Region_in_Expr) (t: Epsilon) : Epsilon :=
   fun sa => exists sa', t sa' /\ subst_sa z u sa' = sa.


Reserved Notation "'[' x ':=' u ']' t" (at level 20).
Fixpoint subst_type (z : VarId) (u : Region_in_Expr) (t : Tau) {struct t} : Tau :=
  match t with
  | Ty_Natural => Ty_Natural
  | Ty_Boolean => Ty_Boolean
  | Ty_Effect  => Ty_Effect
  | Ty_Unit    => Ty_Unit
  | Ty_Pair t1 t2  => Ty_Pair (subst_type z u t1) (subst_type z u t2)
  | Ty_Ref r t => Ty_Ref (subst_rgn z u r) (subst_type z u t)
  | Ty_Arrow aty ceff crty eeff erty =>
      Ty_Arrow (subst_type z u aty) (subst_eps z u ceff) (subst_type z u crty)
        (subst_eps z u eeff) (subst_type z u erty)
  | Ty_ForallRgn eff rty => Ty_ForallRgn (subst_eps z u eff) (subst_type z u rty)
  end
where "'[' x ':=' u ']' t" := (subst_type x u t).

(** end of substitutions **) 


Definition subst_in_type := fun x r ty => subst_type x (Rgn_Const true false r) ty.

Definition subst_in_eff := fun x r eff => subst_eps x (Rgn_Const true false r) eff.

Definition subst_in_sa := fun x r sa => subst_sa x (Rgn_Const true false r) sa.

Definition subst_in_rgn := fun x r rgn => subst_rgn x (Rgn_Const true false r) rgn.

Definition subst_rho := R.fold subst_in_type.

Definition fold_subst_rgn := R.fold (fun x r rgn => subst_rgn x (Rgn_Const true false r) rgn).

Definition fold_subst_sa rho sa:=
  match sa with
    | SA_Alloc rgn => SA_Alloc (fold_subst_rgn rho rgn)
    | SA_Read rgn => SA_Read (fold_subst_rgn rho rgn)
    | SA_Write rgn => SA_Write (fold_subst_rgn rho rgn)
  end.

Definition fold_subst_eps rho eps :=
  fun sa => exists sa', eps sa' /\ fold_subst_sa rho sa' = sa.


Notation "a '⊕' b" := (Concat a b) (at level 60).

Reserved Notation "ctxt ';;' rgns ';;' rho '⊢' ec '◀' ee "
  (at level 50, left associativity).
Inductive TcExp : (Gamma * Omega  * Expr * Tau * Epsilon) -> Prop :=
| TC_Nat_Cnt :
  forall ctxt rgns n,
    TcExp (ctxt, rgns, Const n, Ty_Natural, Empty_Static_Action)

| TC_Boolean :
  forall ctxt rgns b,
    TcExp (ctxt, rgns, Bool b, Ty_Boolean, Empty_Static_Action)

| TC_Val_Var :
  forall ctxt rgns x ty,
    find_T x ctxt = Some ty ->
    TcExp (ctxt, rgns, Var x, ty, Empty_Static_Action)

| TC_Mu_Abs :
  forall ctxt rgns f x ec ee tyx effc tyc effe,
    (forall rho,
        (BackTriangle
           (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect) (x, tyx) ctxt,
             rgns, rho, ec, ee))) ->    
    (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
    TcInc (ctxt, rgns) ->
    included (frv (Ty_Arrow tyx effc tyc effe Ty_Effect)) rgns ->
    (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
    TcExp (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect) (x, tyx) ctxt,
        rgns, ec, tyc, effc) ->
    TcExp (update_rec_T (f, Ty_Arrow tyx effc tyc effe Ty_Effect) (x, tyx) ctxt,
        rgns, ee, Ty_Effect, effe) ->
    TcExp (ctxt, rgns, Mu f x ec ee, Ty_Arrow tyx effc tyc effe Ty_Effect,
        Empty_Static_Action)

| TC_Rgn_Abs :
  forall ctxt rgns x er effr tyr,
    not_set_elem rgns x ->
    lc_type tyr ->
    lc_type_eps effr ->
    TcInc (ctxt, rgns) ->
    (forall rho,
        BackTriangle (ctxt, set_union rgns (singleton_set x), rho, er, Empty)) ->
    TcExp (ctxt, set_union rgns (singleton_set x), er, tyr, effr) ->
    TcExp (ctxt, rgns, Lambda x er, Ty_ForallRgn (close_var_eff x effr) (close_var x tyr),
        Empty_Static_Action)

| TC_Mu_App :
  forall ctxt rgns ef ea tya effc tyc effe efff effa,
    (forall rho, BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea)) ->
    TcExp (ctxt, rgns, ef, Ty_Arrow tya effc tyc effe Ty_Effect, efff) ->
    TcExp (ctxt, rgns, ea, tya, effa) ->
    included (free_rgn_vars_in_eps effc) rgns ->
    TcExp (ctxt, rgns, Mu_App ef ea,
        tyc, Union_Static_Action (Union_Static_Action efff effa) effc)

| TC_Rgn_App :
  forall ctxt rgns er w tyr effr efff,
    TcExp (ctxt, rgns, er, Ty_ForallRgn effr tyr, efff) ->
    TcRgn (rgns, w) ->
    (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
    lc_type tyr ->
    included (free_rgn_vars_in_eps (open_rgn_eff (mk_rgn_type w) effr)) rgns ->
    (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
    TcExp (ctxt, rgns,  Rgn_App er w, open (mk_rgn_type w) tyr,
        Union_Static_Action efff (open_rgn_eff (mk_rgn_type w) effr))

| TC_Eff_App :
  forall ctxt rgns ef ea tya effc tyc effe efff effa,
    TcExp (ctxt, rgns, ef, Ty_Arrow tya effc tyc effe Ty_Effect, efff) ->
    TcExp (ctxt, rgns, ea, tya, effa) ->
    included (free_rgn_vars_in_eps effe) rgns ->
    TcExp (ctxt, rgns, Eff_App ef ea,
        Ty_Effect, Union_Static_Action (Union_Static_Action efff effa) effe)

| TC_Pair_Par :
  forall ctxt rgns ef1 ea1 ef2 ea2 ty1 ty2 ty3 ty4 eff1 eff2 eff3 eff4,
    TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
    TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
    TcExp (ctxt, rgns, Eff_App ef1 ea1, ty3, eff3) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, ty4, eff4) ->
    TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, Ty_Pair ty1 ty2,
        Union_Static_Action
          (Union_Static_Action
             (Union_Static_Action eff3 eff4) eff2) eff1)

| TC_New_Ref :
  forall ctxt rgns e t veff w s,
    TcExp (ctxt, rgns, e, t, veff) ->
    w = Rgn_Const true false s ->
    (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
    included (free_rgn_vars_in_eps
                (Singleton_Static_Action (SA_Alloc (mk_rgn_type w)))) rgns ->
    (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
    TcExp (ctxt, rgns, Ref w e, Ty_Ref (mk_rgn_type w) t,
        Union_Static_Action veff
          (Singleton_Static_Action (SA_Alloc (mk_rgn_type w))))

| TC_Get_Ref :
  forall ctxt rgns e t aeff w s,
    w = Rgn_Const true false s ->
    TcExp (ctxt, rgns, e, Ty_Ref (mk_rgn_type w) t, aeff) ->
    TcRgn (rgns, w) ->
    (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
    included (free_rgn_vars_in_eps
                (Singleton_Static_Action (SA_Read (mk_rgn_type w)))) rgns ->
    (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
    TcExp (ctxt, rgns, DeRef w e, t,
        Union_Static_Action aeff
          (Singleton_Static_Action (SA_Read  (mk_rgn_type w))))

| TC_Set_Ref
  : forall ctxt rgns ea ev t aeff veff w s,
    w = Rgn_Const true false s ->
    TcExp (ctxt, rgns, ea, Ty_Ref (mk_rgn_type w) t, aeff) ->
    TcExp (ctxt, rgns, ev, t, veff) ->
    TcRgn (rgns, w) ->
    (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
    included (free_rgn_vars_in_eps
                (Singleton_Static_Action (SA_Write (mk_rgn_type w)))) rgns ->
    (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
    TcExp (ctxt, rgns, Assign w ea ev, Ty_Unit,
        Union_Static_Action (
            Union_Static_Action aeff veff)
          (Singleton_Static_Action
             (SA_Write  (mk_rgn_type w))))

| TC_Conditional
  : forall ctxt rgns b e1 e2 te eff eff1 eff2,
    TcExp (ctxt, rgns, b, Ty_Boolean, eff) ->
    TcExp (ctxt, rgns, e1, te, eff1) ->
    TcExp (ctxt, rgns, e2, te, eff2) ->
    TcExp (ctxt, rgns, Cond b e1 e2, te,
        Union_Static_Action eff (Union_Static_Action eff1 eff2))

| TC_Nat_Plus :
  forall ctxt rgns e1 e2 eff1 eff2,
    TcExp (ctxt, rgns, e1, Ty_Natural, eff1) ->
    TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
    TcExp (ctxt, rgns, Plus e1 e2, Ty_Natural, Union_Static_Action eff1 eff2)

| TC_Nat_Minus :
  forall ctxt rgns e1 e2 eff1 eff2,
    TcExp (ctxt, rgns, e1, Ty_Natural, eff1) ->
    TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
    TcExp (ctxt, rgns, Minus e1 e2, Ty_Natural, Union_Static_Action eff1 eff2)

| TC_Nat_Times :
  forall ctxt rgns e1 e2 eff1 eff2,
    TcExp (ctxt, rgns, e1, Ty_Natural, eff1) ->
    TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
    TcExp (ctxt, rgns, Times e1 e2, Ty_Natural, Union_Static_Action eff1 eff2)

| TC_Bool_Eq :
  forall ctxt rgns e1 e2 eff1 eff2,
    TcExp (ctxt, rgns, e1, Ty_Natural, eff1) ->
    TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
    TcExp (ctxt, rgns, Eq e1 e2, Ty_Boolean, Union_Static_Action eff1 eff2)

| TC_Alloc_Abs :
  forall ctxt rgns r,
    TcExp (ctxt, rgns, AllocAbs r, Ty_Effect, Empty_Static_Action)

| TC_Read_Abs :
  forall ctxt rgns r,
    TcExp (ctxt, rgns, ReadAbs r, Ty_Effect, Empty_Static_Action)

| TC_Read_Conc :
  forall ctxt rgns e r t aeff,
    TcExp (ctxt, rgns, e, Ty_Ref (Rgn_Const true true r) t, aeff) ->
    TcExp (ctxt, rgns, ReadConc e, Ty_Effect, aeff)

| TC_Write_Abs :
  forall ctxt rgns r,
    TcExp (ctxt, rgns,  WriteAbs r, Ty_Effect, Empty_Static_Action)

| TC_Write_Conc :
  forall ctxt rgns e r t aeff,
    TcExp (ctxt, rgns, e,  Ty_Ref (Rgn_Const true true r) t, aeff) ->
    TcExp (ctxt, rgns, WriteConc e, Ty_Effect, aeff)

| TC_Eff_Concat :
  forall ctxt rgns a b eff1 eff2,
    TcExp (ctxt, rgns, a, Ty_Effect, eff1) ->
    TcExp (ctxt, rgns, b, Ty_Effect, eff2) -> 
    TcExp (ctxt, rgns, Concat a b, Ty_Effect, Union_Static_Action eff1 eff2)

| TC_Eff_Top :
  forall ctxt rgns, TcExp (ctxt, rgns, Top, Ty_Effect, Empty_Static_Action)

| TC_Eff_Empty :
  forall ctxt rgns, TcExp (ctxt, rgns, Empty, Ty_Effect, Empty_Static_Action)
   
with BackTriangle : Gamma * Omega * Rho * Expr * Expr -> Prop :=
| BT_Num_Pure :
  forall ctxt rgns rho (n : nat),
    TcExp (ctxt, rgns, Const n, Ty_Natural, Empty_Static_Action) ->
    BackTriangle (ctxt, rgns, rho, (Const n), Empty)

| BT_Bool_Pure :
  forall ctxt rgns rho (b : bool),
    TcExp (ctxt, rgns, Bool b, Ty_Boolean, Empty_Static_Action) ->
    BackTriangle (ctxt, rgns, rho, Bool b, Empty)

| BT_Var_Pure :
  forall ctxt rgns rho ty (x : VarId),
    TcExp (ctxt, rgns, Var x, ty, Empty_Static_Action) ->
    BackTriangle (ctxt, rgns, rho, Var x, Empty)

| BT_Abs_Pure :
  forall ctxt rgns rho (f x: VarId) (ec ee: Expr),
    BackTriangle (ctxt, rgns, rho, Mu f x ec ee, Empty)

| BT_Rgn_Pure :
  forall ctxt rgns rho (x: VarId) (e: Expr),
    BackTriangle (ctxt, rgns, rho, Lambda x e, Empty)

| BT_App_Conc :
  forall  ctxt rgns rho (ef ea: Expr) ty_mu ty_eff ty_ef ty_ea
          static_ef static_ea static_mu static_ee,
    TcExp (ctxt, rgns, Mu_App ef ea, ty_mu, static_mu) ->
    TcExp (ctxt, rgns, Eff_App ef ea, ty_eff, static_ee) ->
    ReadOnlyStatic (fold_subst_eps rho static_ee) ->
    TcExp (ctxt, rgns, ef, ty_ef, static_ef) ->
    TcExp (ctxt, rgns, ea, ty_ea, static_ea) ->
    BackTriangle (ctxt, rgns, rho, ef, Eff_App ef ea) ->
    BackTriangle (ctxt, rgns, rho, ea, Eff_App ef ea) ->
    ReadOnlyStatic (fold_subst_eps rho static_ef) ->
    ReadOnlyStatic (fold_subst_eps rho static_ea) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea)

| BT_Pair_Par :
  forall ctxt rgns rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4 ty_e static_ee_1 static_ee_2,
    TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_e, static_ee_1) ->
    ReadOnlyStatic (fold_subst_eps rho static_ee_1) ->
    TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_e, static_ee_2) ->
    ReadOnlyStatic (fold_subst_eps rho static_ee_2) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1) ->
    BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, eff3) ->
    BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, eff4) ->
    BackTriangle (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,(eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4))

| BT_Rgn_App :
  forall ctxt rgns rho er w ty_eb static_er,
    TcExp (ctxt, rgns, er, ty_eb, static_er) ->
    TcExp (ctxt, rgns, Empty, Ty_Effect, Empty_Static_Action) ->
    BackTriangle (ctxt, rgns, rho, er, Empty) ->
    BackTriangle (ctxt, rgns, rho, Rgn_App er w, Empty)

| BT_Cond_Cond :
  forall ctxt rgns rho (e et ef effe efft efff : Expr)
         ty_e ty_et ty_ef static_e static_et static_ef,
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    TcExp (ctxt, rgns, et, ty_et, static_et) ->
    TcExp (ctxt, rgns, ef, ty_ef, static_ef) ->
    ReadOnlyStatic (fold_subst_eps rho static_e) ->
    BackTriangle (ctxt, rgns, rho, e, Empty) ->
    BackTriangle (ctxt, rgns, rho, et, efft) ->
    BackTriangle (ctxt, rgns, rho, ef, efff) ->
    BackTriangle (ctxt, rgns, rho, Cond e et ef, Cond e efft efff)

| BT_Ref_Alloc_Abs :
  forall ctxt rgns rho (e eff : Expr) (w : Region_in_Expr) ty_e static_e,
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    BackTriangle (ctxt, rgns, rho, e, eff) ->
    BackTriangle (ctxt, rgns, rho, Ref w e, eff ⊕ AllocAbs w)

| BT_Ref_Read_Abs :
  forall ctxt rgns rho (e eff : Expr) (w : Region_in_Expr) ty_e static_e,
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    BackTriangle (ctxt, rgns, rho, e, eff) ->
    BackTriangle (ctxt, rgns, rho, DeRef w e, eff ⊕ (ReadAbs w))

| BT_Ref_Read_Conc :
  forall ctxt rgns rho (e eff : Expr) (r : RgnId) ty_e static_e,
    TcExp (ctxt, rgns, e, ty_e, static_e) ->
    BackTriangle (ctxt, rgns, rho, e, Empty) ->
    BackTriangle (ctxt, rgns, rho, DeRef (Rgn_Const true false r) e, ReadConc e)

| BT_Ref_Write_Abs :
  forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr) (w : Region_in_Expr) ty_e1 static_e1,
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    BackTriangle (ctxt, rgns, rho, Assign w e1 e2, eff1 ⊕ (eff2 ⊕ (WriteAbs w)))

| BT_Ref_Write_Conc:
  forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr) (r : RgnId) ty_e1 static_e1,
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    BackTriangle (ctxt, rgns, rho,
        Assign (Rgn_Const true false r) e1 e2, eff1 ⊕ (eff2 ⊕ (WriteConc e1)))

| BT_Plus :
  forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr) ty_e1 ty_e2 static_e1 static_e2,
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    BackTriangle (ctxt, rgns, rho, Plus e1 e2, eff1 ⊕ eff2)

| BT_Minus : forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr) ty_e1 ty_e2 static_e1 static_e2,
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    BackTriangle (ctxt, rgns, rho, Minus e1 e2, eff1 ⊕ eff2)

| BT_Times : forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr) ty_e1 ty_e2 static_e1 static_e2,
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    BackTriangle (ctxt, rgns, rho, Times e1 e2, eff1 ⊕ eff2)


| BT_Eq : forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr) ty_e1 ty_e2 static_e1 static_e2,
    TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
    TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
    ReadOnlyStatic (fold_subst_eps rho static_e1) ->
    BackTriangle (ctxt, rgns, rho, e1, eff1) ->
    BackTriangle (ctxt, rgns, rho, e2, eff2) ->
    BackTriangle (ctxt, rgns, rho, Eq e1 e2, eff1 ⊕ eff2)

| BT_Top_Approx :
  forall ctxt rgns rho (e : Expr),
    BackTriangle (ctxt, rgns, rho, e, Top)

with TcVal : (Sigma * Val * Tau) -> Prop :=
| TC_Num :
  forall stty n,
    TcVal (stty, Num n, Ty_Natural)

| TC_Bit :
  forall stty b,
    TcVal (stty, Bit b, Ty_Boolean)

| TC_Loc :
  forall stty s l ty,
    find_ST (s, l) stty = Some ty ->
    (forall r, r # ty) ->
    TcVal (stty, Loc (Rgn_Const true false s) l,
        Ty_Ref (Rgn_Const true true s) ty)

| TC_Cls :
  forall stty env rho e rgns ctxt t,
    TcRho (rho, rgns) ->
    TcInc (ctxt, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns, e, t, Empty_Static_Action) ->
    TcVal (stty, Cls (env, rho, e), subst_rho rho t)

| TC_Unit :
  forall stty,
    TcVal (stty, Unit, Ty_Unit)

| TC_Pair :
  forall stty v1 v2 ty1 ty2,
    TcVal (stty, v1, ty1) ->
    TcVal (stty, v2, ty2) ->
    TcVal (stty, Pair (v1, v2), Ty_Pair ty1 ty2)

| TC_Eff :
  forall stty e,
    TcVal (stty, Eff e, Ty_Effect)
                        
with TcEnv : (Sigma * Rho * Env * Gamma) -> Prop :=
| TC_Env :
  forall stty rho env ctxt,
    (forall x v, (find_E x env = Some v -> exists t, find_T x ctxt = Some t)) ->
    (forall x t, (find_T x ctxt = Some t -> exists v, find_E x env = Some v)) ->
    (forall x v t, find_E x env = Some v -> find_T x ctxt = Some t ->
                   TcVal (stty, v, subst_rho rho t)) ->
    TcEnv (stty, rho, env, ctxt)

where "ctxt ';;' rgns ';;' rho '⊢' ec '◀' ee" := (BackTriangle (ctxt, rgns, rho, ec, ee)) : type_scope.



Scheme tc_exp__xind := Induction for TcExp Sort Prop
  with bt__xind     := Induction for BackTriangle Sort Prop
  with tc_val__xind := Induction for TcVal Sort Prop
  with tc_env__xind := Induction for TcEnv Sort Prop.

Combined Scheme tc__xind from 
  tc_exp__xind, 
  bt__xind,
  tc_val__xind, 
  tc_env__xind.






  
