Require Import Coq.Sets.Ensembles.
Require Import Definitions.Regions.

(* Static Actions; for type-and-effect system *)
Inductive StaticAction : Set :=
| SA_Alloc : Region_in_Type -> StaticAction
| SA_Read  : Region_in_Type -> StaticAction
| SA_Write : Region_in_Type -> StaticAction.

Definition Epsilon := Ensemble StaticAction.

(* Static Actions; for type-and-effect system *)
Definition Empty_Static_Action := Empty_set StaticAction.
Definition Singleton_Static_Action (e : StaticAction) :=  Singleton StaticAction e.
Definition Union_Static_Action (a b : Ensemble StaticAction) :=  Union StaticAction a b.

Inductive ReadOnlyStatic : Epsilon -> Prop :=
| Static_RO_Empty     : ReadOnlyStatic (Empty_Static_Action)
| Static_RO_Singleton :
  forall r, ReadOnlyStatic (Singleton_Static_Action (SA_Read r))
| Static_RO_Union     :
  forall eps1 eps2,
    ReadOnlyStatic eps1 ->
    ReadOnlyStatic eps2 ->
    ReadOnlyStatic (Union_Static_Action eps1 eps2).                       


Inductive Disjoint_Static : StaticAction -> StaticAction -> Prop :=
 | DS_Read_Read   : forall r1 r2, Disjoint_Static (SA_Read r1) (SA_Read r2)
 | DS_Write_Write : forall r1 r2, r1 <> r2 -> Disjoint_Static (SA_Write r1) (SA_Write r2)
 | DS_Read_Write  : forall r1 r2, r1 <> r2 -> Disjoint_Static (SA_Read r1) (SA_Write r2)
 | DS_Write_Read  : forall r1 r2, r1 <> r2 -> Disjoint_Static (SA_Write r1) (SA_Read r2).
