Require Import Coq.Sets.Ensembles.
Require Import Definitions.Regions.

Definition empty_set `{T: Type} := Empty_set T.
Definition singleton_set `{T: Type} (e: T) := Singleton T e.
Definition set_union `{T: Type} (s1 s2: Ensemble T) := Union T s1 s2.
Definition set_elem `{T: Type} (s: Ensemble T) (e: T) := Ensembles.In T s e.
Definition not_set_elem `{T: Type} (s: Ensemble T) (e: T) := Ensembles.Complement T s e.
Definition included `{T: Type} (s1 s2: Ensemble T) := Ensembles.Included T s1 s2.
Definition set_minus `{T: Type} (s: Ensemble T) (e: T)  := Ensembles.Subtract T s e.


(* Computed Actions; for effect specification *)
Inductive ComputedAction : Set :=
| CA_ReadConc  : RgnVal -> nat -> ComputedAction
| CA_WriteConc : RgnVal -> nat -> ComputedAction 
| CA_AllocAbs  : RgnVal -> ComputedAction
| CA_ReadAbs   : RgnVal -> ComputedAction
| CA_WriteAbs  : RgnVal -> ComputedAction. 

Definition Theta := option (Ensemble ComputedAction).
Definition Theta_Top : Theta := None.
Definition Theta_Empty : Theta := Some empty_set.
Definition Union_Theta (theta1 theta2 : Theta) := 
  match theta1,theta2 with
    | None, _ => None
    | _, None => None
    | Some acts1, Some acts2 => Some (set_union acts1 acts2)                                    
  end.

Inductive Disjoint_Computed_Actions : ComputedAction -> ComputedAction -> Prop :=
| D_CA_ReadConc_ReadConc    : forall r1 l1 r2 l2,
    Disjoint_Computed_Actions (CA_ReadConc r1 l1) (CA_ReadConc r2 l2)
| D_CA_ReadConc_Alloc       : forall r1 l1 r2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_ReadConc r1 l1) (CA_AllocAbs r2)
| D_CA_ReadConc_ReadAbs     : forall r1 l1 r2,
    Disjoint_Computed_Actions (CA_ReadConc r1 l1) (CA_ReadAbs r2)
| D_CA_ReadConc_WriteAbs    :
  forall r1 l1 r2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_ReadConc r1 l1) (CA_WriteAbs r2)
| D_CA_ReadConc_WriteConc   : forall r1 l1 r2 l2,
    r1 <> r2 -> l1 <> l2 ->
    Disjoint_Computed_Actions (CA_ReadConc r1 l1) (CA_WriteConc r2 l2) 
| D_CA_ReadAbs_ReadConc    : forall r1 r2 l2,
    Disjoint_Computed_Actions (CA_ReadAbs r1) (CA_ReadConc r2 l2)
| D_CA_ReadAbs_ReadAbs     : forall r1 r2,
    Disjoint_Computed_Actions (CA_ReadAbs r1) (CA_ReadAbs r2)
| D_CA_ReadAbs_Alloc       : forall r1 r2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_ReadAbs r1) (CA_AllocAbs r2)
| D_CA_ReadAbs_WriteAbs    : forall r1 r2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_ReadAbs r1) (CA_WriteAbs r2)
| D_CA_ReadAbs_WriteConc   : forall r1 r2 l2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_ReadAbs r1) (CA_WriteConc r2 l2)
| D_CA_WriteConc_WriteConc : forall r1 l1 r2 l2,
    r1 <> r2 ->
    l1 <> l2 ->
    Disjoint_Computed_Actions (CA_WriteConc r1 l1) (CA_WriteConc r2 l2)
| D_CA_WriteAbs_WriteConc  : forall r1 r2 l2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_WriteAbs r1) (CA_WriteConc r2 l2)
| D_CA_WriteAbs_WriteAbs   : forall r1 r2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_WriteAbs r1) (CA_WriteAbs r2)
| D_CA_WriteAbs_Alloc      : forall r1 r2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_WriteAbs r1) (CA_AllocAbs r2)
| D_CA_WriteConc_ReadConc  : forall r1 l1 r2 l2,
    r1 <> r2 ->
    l1 <> l2 ->
    Disjoint_Computed_Actions (CA_WriteConc r1 l1) (CA_ReadConc r2 l2)
| D_CA_WriteConc_ReadAbs   : forall r1 l1 r2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_WriteConc r1 l1) (CA_ReadAbs r2)
| D_CA_WriteConc_Alloc     : forall r1 l1 r2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_WriteConc r1 l1) (CA_AllocAbs r2)
| D_CA_WriteAbs_ReadConc   : forall r1 r2 l2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_WriteAbs r1) (CA_ReadConc r2 l2)
| D_CA_WriteAbs_ReadAbs    : forall r1 r2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_WriteAbs r1) (CA_ReadAbs r2)
| D_CA_Alloc_Alloc         : forall r1 r2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_AllocAbs r1) (CA_AllocAbs r2)
| D_CA_Alloc_ReadAbs       : forall r1 r2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_AllocAbs r1) (CA_ReadAbs r2)
| D_CA_Alloc_ReadConc      : forall r1 r2 l2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_AllocAbs r1) (CA_ReadConc r2 l2)
| D_CA_Alloc_WriteAbs      : forall r1 r2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_AllocAbs r1) (CA_WriteAbs r2)
| D_CA_Alloc_WriteConc     : forall r1 r2 l2,
    r1 <> r2 ->
    Disjoint_Computed_Actions (CA_AllocAbs r1) (CA_WriteConc r2 l2).                                                                                     

Inductive Disjoint_Sets_Computed_Actions : Ensemble (ComputedAction) -> Ensemble (ComputedAction) -> Prop :=
 | D_Set_CA   : forall theta1 theta2,
                  (forall d1 d2,
                     set_elem theta1 d1 ->
                     set_elem theta2 d2 ->
                     Disjoint_Computed_Actions d1 d2) ->
                 Disjoint_Sets_Computed_Actions theta1 theta2.                                                

Inductive Disjointness : Theta -> Theta -> Prop :=
| D_Theta  : forall theta1 theta2,
    Disjoint_Sets_Computed_Actions theta1 theta2 ->
    Disjointness (Some theta1) (Some theta2).


Inductive Conflict_Computed_Actions : ComputedAction -> ComputedAction -> Prop :=
| C_WriteConc_ReadConc : forall r l,
    Conflict_Computed_Actions  (CA_ReadConc r l) ( CA_WriteConc r l)
| C_WriteAbs_ReadConc : forall r l,
    Conflict_Computed_Actions  (CA_ReadConc r l) ( CA_WriteAbs r)
| C_ReadAbs_WriteConc : forall r l,
    Conflict_Computed_Actions  (CA_ReadAbs r) ( CA_WriteConc r l)
| C_WriteAbs_ReadAbs : forall r,
    Conflict_Computed_Actions  (CA_ReadAbs r) ( CA_WriteAbs r)
| C_WriteAbs_WriteAbs : forall r,
    Conflict_Computed_Actions  (CA_WriteAbs r) ( CA_WriteAbs r)
| C_WriteAbs_WriteConc : forall r l,
    Conflict_Computed_Actions  (CA_WriteAbs r) ( CA_WriteConc r l)
| C_WriteConc_WriteAbs : forall r l,
    Conflict_Computed_Actions (CA_WriteConc r l) (CA_WriteAbs r)
| C_WriteConc_WriteConc : forall r l,
    Conflict_Computed_Actions (CA_WriteConc r l) (CA_WriteConc r l)
| C_WriteConc_ReadAbs : forall r l,
    Conflict_Computed_Actions (CA_WriteConc r l) (CA_ReadAbs r).

Inductive Conflict_Sets_Computed_Actions : Ensemble (ComputedAction) -> Ensemble (ComputedAction) -> Prop :=
| C_Set_CA  :
  forall theta1 theta2,
  forall d1 d2,
    set_elem theta1 d1 ->
    set_elem theta2 d2 ->
    Conflict_Computed_Actions d1 d2 ->
    Conflict_Sets_Computed_Actions theta1 theta2. 

Inductive Conflictness : Theta -> Theta -> Prop :=
 | C_TopL : forall theta2, Conflictness None theta2
 | C_TopR : forall theta1, Conflictness theta1 None
 | C_Theta  : forall theta1 theta2,
     Conflict_Sets_Computed_Actions theta1 theta2 ->
     Conflictness (Some theta1) (Some theta2).
