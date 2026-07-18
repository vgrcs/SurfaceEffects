Require Import theories.Core.Expressions.
Require Import theories.Core.Regions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.

Inductive SmallStepBackTriangle : Gamma * Omega * Rho * Expr * Expr -> Prop :=
| SSBT_Num_Pure :
    forall ctxt rgns rho (n : nat),
      TcExp (ctxt, rgns, Const n, Ty_Natural, Empty_Static_Action) ->
      SmallStepBackTriangle (ctxt, rgns, rho, Const n, Empty)

| SSBT_Bool_Pure :
    forall ctxt rgns rho (b : bool),
      TcExp (ctxt, rgns, Bool b, Ty_Boolean, Empty_Static_Action) ->
      SmallStepBackTriangle (ctxt, rgns, rho, Bool b, Empty)

| SSBT_Var_Pure :
    forall ctxt rgns rho ty (x : VarId),
      TcExp (ctxt, rgns, Var x, ty, Empty_Static_Action) ->
      SmallStepBackTriangle (ctxt, rgns, rho, Var x, Empty)

| SSBT_Abs_Pure :
    forall ctxt rgns rho (f x : VarId) (ec ee : Expr),
      SmallStepBackTriangle (ctxt, rgns, rho, Mu f x ec ee, Empty)

| SSBT_Rgn_Pure :
    forall ctxt rgns rho (x : VarId) (e : Expr),
      SmallStepBackTriangle (ctxt, rgns, rho, Lambda x e, Empty)

| SSBT_App_Conc :
    forall ctxt rgns rho (ef ea : Expr) ty_mu ty_eff ty_ef ty_ea
      static_ef static_ea static_mu static_ee,
      TcExp (ctxt, rgns, Mu_App ef ea, ty_mu, static_mu) ->
      TcExp (ctxt, rgns, Eff_App ef ea, ty_eff, static_ee) ->
      ReadOnlyStatic (fold_subst_eps rho static_ee) ->
      TcExp (ctxt, rgns, ef, ty_ef, static_ef) ->
      TcExp (ctxt, rgns, ea, ty_ea, static_ea) ->
      SmallStepBackTriangle (ctxt, rgns, rho, ef, Eff_App ef ea) ->
      SmallStepBackTriangle (ctxt, rgns, rho, ea, Eff_App ef ea) ->
      ReadOnlyStatic (fold_subst_eps rho static_ef) ->
      ReadOnlyStatic (fold_subst_eps rho static_ea) ->
      SmallStepBackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea)

| SSBT_Pair_Par_Canonical :
    forall ctxt rgns rho ef1 ea1 ef2 ea2 eff1 eff2
      ty_e static_ee_1 static_ee_2,
      TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_e, static_ee_1) ->
      ReadOnlyStatic (fold_subst_eps rho static_ee_1) ->
      TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_e, static_ee_2) ->
      ReadOnlyStatic (fold_subst_eps rho static_ee_2) ->
      SmallStepBackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1) ->
      SmallStepBackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2) ->
      SmallStepBackTriangle
        (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) ->
      SmallStepBackTriangle
        (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2) ->
      SmallStepBackTriangle
        (ctxt, rgns, rho,
         Pair_Par ef1 ea1 ef2 ea2,
         Concat
           (Concat eff1 eff2)
           (Concat (Eff_App ef1 ea1) (Eff_App ef2 ea2)))

| SSBT_Rgn_App :
    forall ctxt rgns rho er w ty_eb static_er,
      TcExp (ctxt, rgns, er, ty_eb, static_er) ->
      TcExp (ctxt, rgns, Empty, Ty_Effect, Empty_Static_Action) ->
      SmallStepBackTriangle (ctxt, rgns, rho, er, Empty) ->
      SmallStepBackTriangle (ctxt, rgns, rho, Rgn_App er w, Empty)

| SSBT_Cond_Cond :
    forall ctxt rgns rho (e et ef effe efft efff : Expr)
      ty_e ty_et ty_ef static_e static_et static_ef,
      TcExp (ctxt, rgns, e, ty_e, static_e) ->
      TcExp (ctxt, rgns, et, ty_et, static_et) ->
      TcExp (ctxt, rgns, ef, ty_ef, static_ef) ->
      ReadOnlyStatic (fold_subst_eps rho static_e) ->
      SmallStepBackTriangle (ctxt, rgns, rho, e, Empty) ->
      SmallStepBackTriangle (ctxt, rgns, rho, et, efft) ->
      SmallStepBackTriangle (ctxt, rgns, rho, ef, efff) ->
      SmallStepBackTriangle (ctxt, rgns, rho, Cond e et ef, Cond e efft efff)

| SSBT_Ref_Alloc_Abs :
    forall ctxt rgns rho (e eff : Expr) (w : Region_in_Expr) ty_e static_e,
      TcExp (ctxt, rgns, e, ty_e, static_e) ->
      SmallStepBackTriangle (ctxt, rgns, rho, e, eff) ->
      SmallStepBackTriangle (ctxt, rgns, rho, Ref w e, Concat eff (AllocAbs w))

| SSBT_Ref_Read_Abs :
    forall ctxt rgns rho (e eff : Expr) (w : Region_in_Expr) ty_e static_e,
      TcExp (ctxt, rgns, e, ty_e, static_e) ->
      SmallStepBackTriangle (ctxt, rgns, rho, e, eff) ->
      SmallStepBackTriangle (ctxt, rgns, rho, DeRef w e, Concat eff (ReadAbs w))

| SSBT_Ref_Read_Conc :
    forall ctxt rgns rho (e eff : Expr) (r : RgnVal) ty_e static_e,
      TcExp (ctxt, rgns, e, ty_e, static_e) ->
      SmallStepBackTriangle (ctxt, rgns, rho, e, Empty) ->
      SmallStepBackTriangle
        (ctxt, rgns, rho, DeRef (Rgn_Const true false r) e, ReadConc e)

| SSBT_Ref_Write_Abs :
    forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr)
      (w : Region_in_Expr) ty_e1 static_e1,
      SmallStepBackTriangle (ctxt, rgns, rho, e1, eff1) ->
      SmallStepBackTriangle (ctxt, rgns, rho, e2, eff2) ->
      TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
      ReadOnlyStatic (fold_subst_eps rho static_e1) ->
      SmallStepBackTriangle
        (ctxt, rgns, rho, Assign w e1 e2,
         Concat eff1 (Concat eff2 (WriteAbs w)))

| SSBT_Ref_Write_Conc :
    forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr)
      (r : RgnVal) ty_e1 static_e1,
      SmallStepBackTriangle (ctxt, rgns, rho, e1, eff1) ->
      SmallStepBackTriangle (ctxt, rgns, rho, e2, eff2) ->
      TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
      ReadOnlyStatic (fold_subst_eps rho static_e1) ->
      SmallStepBackTriangle
        (ctxt, rgns, rho, Assign (Rgn_Const true false r) e1 e2,
         Concat eff1 (Concat eff2 (WriteConc e1)))

| SSBT_Plus :
    forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr)
      ty_e1 ty_e2 static_e1 static_e2,
      TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
      TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
      ReadOnlyStatic (fold_subst_eps rho static_e1) ->
      SmallStepBackTriangle (ctxt, rgns, rho, e1, eff1) ->
      SmallStepBackTriangle (ctxt, rgns, rho, e2, eff2) ->
      SmallStepBackTriangle (ctxt, rgns, rho, Plus e1 e2, Concat eff1 eff2)

| SSBT_Minus :
    forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr)
      ty_e1 ty_e2 static_e1 static_e2,
      TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
      TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
      ReadOnlyStatic (fold_subst_eps rho static_e1) ->
      SmallStepBackTriangle (ctxt, rgns, rho, e1, eff1) ->
      SmallStepBackTriangle (ctxt, rgns, rho, e2, eff2) ->
      SmallStepBackTriangle (ctxt, rgns, rho, Minus e1 e2, Concat eff1 eff2)

| SSBT_Times :
    forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr)
      ty_e1 ty_e2 static_e1 static_e2,
      TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
      TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
      ReadOnlyStatic (fold_subst_eps rho static_e1) ->
      SmallStepBackTriangle (ctxt, rgns, rho, e1, eff1) ->
      SmallStepBackTriangle (ctxt, rgns, rho, e2, eff2) ->
      SmallStepBackTriangle (ctxt, rgns, rho, Times e1 e2, Concat eff1 eff2)

| SSBT_Eq :
    forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr)
      ty_e1 ty_e2 static_e1 static_e2,
      TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
      TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
      ReadOnlyStatic (fold_subst_eps rho static_e1) ->
      SmallStepBackTriangle (ctxt, rgns, rho, e1, eff1) ->
      SmallStepBackTriangle (ctxt, rgns, rho, e2, eff2) ->
      SmallStepBackTriangle (ctxt, rgns, rho, Eq e1 e2, Concat eff1 eff2)

| SSBT_Top_Approx :
    forall ctxt rgns rho ea,
      SmallStepBackTriangle (ctxt, rgns, rho, ea, Top).

Theorem SmallStepBackTriangle_as_BackTriangle :
  forall ctxt rgns rho ea ee,
    SmallStepBackTriangle (ctxt, rgns, rho, ea, ee) ->
    BackTriangle (ctxt, rgns, rho, ea, ee).
Proof.
  intros ctxt rgns rho ea ee HBack.
  induction HBack; try solve [econstructor; eauto].
Qed.

Theorem SmallStepBackTriangle_pair_par_inv :
  forall ctxt rgns rho ef1 ea1 ef2 ea2 eff,
    SmallStepBackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2, eff) ->
    eff = Top \/
    exists eff1 eff2 ty_e static_ee_1 static_ee_2,
      eff =
        Concat
          (Concat eff1 eff2)
          (Concat (Eff_App ef1 ea1) (Eff_App ef2 ea2)) /\
      TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_e, static_ee_1) /\
      ReadOnlyStatic (fold_subst_eps rho static_ee_1) /\
      TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_e, static_ee_2) /\
      ReadOnlyStatic (fold_subst_eps rho static_ee_2) /\
      SmallStepBackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1) /\
      SmallStepBackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2) /\
      SmallStepBackTriangle
        (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) /\
      SmallStepBackTriangle
        (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2).
Proof.
  intros ctxt rgns rho ef1 ea1 ef2 ea2 eff HBack.
  inversion HBack; subst; try discriminate.
  - right.
    repeat eexists; repeat split; eauto.
  - left. reflexivity.
Qed.

Theorem SmallStepBackTriangle_pair_par_branch_backtriangles :
  forall ctxt rgns rho ef1 ea1 ef2 ea2 eff,
    SmallStepBackTriangle
      (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2, eff) ->
    eff = Top \/
    BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, Eff_App ef1 ea1) /\
    BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, Eff_App ef2 ea2).
Proof.
  intros ctxt rgns rho ef1 ea1 ef2 ea2 eff HBack.
  destruct
    (SmallStepBackTriangle_pair_par_inv
      ctxt rgns rho ef1 ea1 ef2 ea2 eff HBack)
    as [HTop | (_eff1 & _eff2 & _ty_e & _static1 & _static2 &
        _HEff & _HTc1 & _HRO1 & _HTc2 & _HRO2 &
        _HBackEff1 & _HBackEff2 & HBackMu1 & HBackMu2)].
  - left. exact HTop.
  - right.
    split; apply SmallStepBackTriangle_as_BackTriangle; assumption.
Qed.
