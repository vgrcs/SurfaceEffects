Require Import Coq.Sets.Ensembles.
Require Import Definitions.Regions.

(* Static Actions; for type-and-effect system *)
Inductive StaticAction : Set :=
| SA2_Alloc : Region_in_Type -> StaticAction
| SA2_Read  : Region_in_Type -> StaticAction
| SA2_Write : Region_in_Type -> StaticAction.

Definition Epsilon := Ensemble StaticAction.

(* Static Actions; for type-and-effect system *)
Definition SA_Alloc:= SA2_Alloc.
Definition SA_Read:= SA2_Read.
Definition SA_Write:= SA2_Write.

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
 | DS_Read_Read   : forall r1 r2, Disjoint_Static (SA2_Read r1) (SA2_Read r2)
 | DS_Write_Write : forall r1 r2, r1 <> r2 -> Disjoint_Static (SA2_Write r1) (SA2_Write r2)
 | DS_Read_Write  : forall r1 r2, r1 <> r2 -> Disjoint_Static (SA2_Read r1) (SA2_Write r2)
 | DS_Write_Read  : forall r1 r2, r1 <> r2 -> Disjoint_Static (SA2_Write r1) (SA2_Read r2).
