From stdpp Require Import gmap.
From stdpp Require Import strings.
From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Ascii.
Require Import theories.BigStep.Core.Regions.
Require Import theories.BigStep.Core.ComputedActions.
Require Import theories.BigStep.Core.StaticActions.
Require Import theories.BigStep.Core.Values.
Require Import theories.BigStep.Core.Expressions.
Require Export theories.BigStep.Typing.TypeSyntax.

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
    find_T x ctxt = Some tyx ->
    find_T f ctxt = Some (Ty_Arrow tyx effc tyc effe Ty_Effect) ->
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
    (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
    included (free_rgn_vars_in_eps effe) rgns ->
    (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
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
    TcRgn (rgns, r) ->
    TcExp (ctxt, rgns, AllocAbs r, Ty_Effect, Empty_Static_Action)

| TC_Read_Abs :
  forall ctxt rgns r,
    TcRgn (rgns, r) ->
    TcExp (ctxt, rgns, ReadAbs r, Ty_Effect, Empty_Static_Action)

| TC_Read_Conc :
  forall ctxt rgns e r t aeff,
    TcExp (ctxt, rgns, e, Ty_Ref (Rgn_Const true true r) t, aeff) ->
    TcExp (ctxt, rgns, ReadConc e, Ty_Effect, aeff)

| TC_Write_Abs :
  forall ctxt rgns r,
    TcRgn (rgns, r) ->
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
  forall ctxt rgns rho (e eff : Expr) (r : RgnVal) ty_e static_e,
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
  forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr) (r : RgnVal) ty_e1 static_e1,
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






  
