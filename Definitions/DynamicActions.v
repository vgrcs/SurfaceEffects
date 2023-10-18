Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import Definitions.Regions.
Require Import Definitions.Values.
Require Import Definitions.ComputedActions.

(* Dynamic Actions; for operational semantics *)
Inductive DynamicAction : Type :=
| DA_Alloc : RgnId -> nat -> Val -> DynamicAction
| DA_Read  : RgnId -> nat -> Val -> DynamicAction
| DA_Write : RgnId -> nat -> Val -> DynamicAction. 

Definition Trace := list DynamicAction.

Inductive Phi :=
 | Phi_Nil : Phi
 | Phi_Elem : DynamicAction -> Phi
 | Phi_Par : Phi -> Phi -> Phi
 | Phi_Seq : Phi -> Phi -> Phi.


Fixpoint phi_as_list (phi : Phi) : Trace :=
  match phi with
    | Phi_Nil => nil
    | Phi_Elem a => a::nil
    | Phi_Seq phi1 phi2 =>  (phi_as_list phi1) ++ (phi_as_list phi2)
    | Phi_Par phi1 phi2 =>  (phi_as_list phi1) ++ (phi_as_list phi2)
  end.                   

Lemma simplify_phi_as_list:
  forall phi1 phi2, phi1 = phi2 ->
                    phi_as_list phi1 = phi_as_list phi2.  
Proof.
  intros.
  induction phi1, phi2;
  try (solve [ unfold phi_as_list; simpl; reflexivity | unfold phi_as_list; simpl; inversion H]).
  - unfold phi_as_list; simpl; inversion H. subst. auto.
  - rewrite H. auto.
  - rewrite H. auto. 
Qed.

Inductive ReadOnlyPhi : Phi -> Prop :=
 | Phi_RO_Nil  : ReadOnlyPhi (Phi_Nil)
 | Phi_RO_Elem : forall r a v, ReadOnlyPhi (Phi_Elem (DA_Read r a v))
 | Phi_RO_Seq  : forall phi1 phi2, ReadOnlyPhi phi1 -> ReadOnlyPhi phi2 -> ReadOnlyPhi (Phi_Seq phi1 phi2)
 | Phi_RO_Par  : forall phi1 phi2, ReadOnlyPhi phi1 -> ReadOnlyPhi phi2 -> ReadOnlyPhi (Phi_Par phi1 phi2). 

Definition Empty_Dynamic_Action := Empty_set DynamicAction.
Definition Singleton_Dynamic_Action (e : DynamicAction) :=  Singleton DynamicAction e.
Definition Union_Dynamic_Action (a b : Ensemble DynamicAction) :=  Union DynamicAction a b.

Inductive DA_in_Phi : DynamicAction -> Phi -> Prop :=
| DAP_Trace : forall da, DA_in_Phi da (Phi_Elem da)
| DAP_Par   : forall da phi1 phi2, DA_in_Phi da phi1 \/ DA_in_Phi da phi2 -> DA_in_Phi da (Phi_Par phi1 phi2)
| DAP_Seq   : forall da phi1 phi2, DA_in_Phi da phi1 \/ DA_in_Phi da phi2 -> DA_in_Phi da (Phi_Seq phi1 phi2).
  
Inductive DA_in_Theta : DynamicAction -> Theta -> Prop :=
| DAT_Top :
    forall da, DA_in_Theta da None
| DAT_Alloc_Abs :
    forall s l v acts,
      set_elem acts (CA_AllocAbs s) ->
      DA_in_Theta (DA_Alloc s l v) (Some acts)
| DAT_Read_Abs :
    forall s l v acts,
      set_elem acts (CA_ReadAbs s) ->
      DA_in_Theta (DA_Read s l v) (Some acts)
| DAT_Read_Conc :
    forall s l v acts,
      set_elem acts (CA_ReadConc s l) ->
      DA_in_Theta (DA_Read s l v) (Some acts)
| DAT_Write_Abs :
    forall s l v acts,
      set_elem acts (CA_WriteAbs s) ->
      DA_in_Theta (DA_Write s l v) (Some acts)
| DAT_Write_Conc :
    forall s l v acts,
      set_elem acts (CA_WriteConc s l) ->
      DA_in_Theta (DA_Write s l v) (Some acts)
| DAT_intror :
    forall da a acts, DA_in_Theta da (Some acts) ->
                      DA_in_Theta da (Some (set_union acts a))
| DAT_introl :
    forall da a acts, DA_in_Theta da (Some acts) ->
                      DA_in_Theta da (Some (set_union a acts)).


Inductive Disjoint_Dynamic : DynamicAction -> DynamicAction -> Prop :=
| DD_Alloc_Alloc  : forall r1 l1 r2 l2 v1 v2,
    (r1, l1) <> (r2, l2) ->
    Disjoint_Dynamic (DA_Alloc r1 l1 v1) (DA_Alloc r2 l2 v2)
| DD_Alloc_Read   :forall r1 l1 r2 l2 v1 v2,
    (r1, l1) <> (r2, l2) ->
    Disjoint_Dynamic (DA_Alloc r1 l1 v1) (DA_Read r2 l2 v2)
| DD_Alloc_Write  : forall r1 l1 r2 l2 v1 v2,
    (r1, l1) <> (r2, l2) ->
    Disjoint_Dynamic (DA_Alloc r1 l1 v1) (DA_Write r2 l2 v2)
| DD_Read_Alloc   : forall r1 l1 r2 l2 v1 v2,
    (r1, l1) <> (r2, l2) ->
    Disjoint_Dynamic (DA_Read r1 l1 v1) (DA_Alloc r2 l2 v2)
| DD_Read_Read   : forall r1 l1 r2 l2 v1 v2,
    Disjoint_Dynamic (DA_Read r1 l1 v1) (DA_Read r2 l2 v2)
| DD_Read_Write   : forall r1 l1 r2 l2 v1 v2,
    (r1, l1) <> (r2, l2) ->
    Disjoint_Dynamic (DA_Read r1 l1 v1) (DA_Write r2 l2 v2)
| DD_Write_Alloc  : forall r1 l1 r2 l2 v1 v2,
    (r1, l1) <> (r2, l2) ->
    Disjoint_Dynamic (DA_Write r2 l2 v2) (DA_Alloc r1 l1 v1)
| DD_Write_Write  : forall r1 l1 r2 l2 v1 v2,
    (r1, l1) <> (r2, l2) ->
    Disjoint_Dynamic (DA_Write r2 l2 v2) (DA_Write r1 l1 v1)
| DD_Write_Read   : forall r1 l1 r2 l2 v1 v2,
    (r1, l1) <> (r2, l2) ->
    Disjoint_Dynamic (DA_Write r2 l2 v2) (DA_Read r1 l1 v1).


Inductive Disjoint_Traces : Trace -> Trace -> Prop :=
| D_Trace_DA :
  forall phi1 phi2,
    (forall p1 p2,
        List.In p1 phi1 ->
        List.In p2 phi2 ->
        Disjoint_Dynamic p1 p2) ->
    Disjoint_Traces phi1 phi2.

Inductive Conflict_Dynamic_Actions : DynamicAction -> DynamicAction -> Prop :=
| D_Read_Write : forall r l v (a : DynamicAction),
                   Conflict_Dynamic_Actions ( DA_Read r l v) (DA_Write r l v)
| D_Write_Write : forall r l v (a : DynamicAction),
              Conflict_Dynamic_Actions ( DA_Write r l v) (DA_Write r l v).                                            

Inductive Conflict_Traces : Trace -> Trace -> Prop :=
| C_Trace_DA : forall p1 p2 phi1 phi2,
    List.In p1 phi1 ->
    List.In p2 phi2 ->
    Conflict_Dynamic_Actions p1 p2 ->
    Conflict_Traces phi1 phi2.


Reserved Notation "phi '⊑' theta" (at level 50, left associativity).
Inductive Phi_Theta_Soundness : Phi -> Theta -> Prop :=
| PTS_Nil : forall theta,
    (Phi_Nil) ⊑ theta
| PTS_Elem : forall da theta,
    DA_in_Theta da theta ->
    (Phi_Elem da) ⊑ theta
| PTS_Seq : forall phi1 phi2 theta,
    phi1 ⊑ theta ->
    phi2 ⊑ theta ->
    Phi_Seq phi1 phi2 ⊑ theta
| PTS_Par : forall phi1 phi2 theta,
    phi1 ⊑ theta ->
    phi2 ⊑ theta ->
    Phi_Par phi1 phi2 ⊑ theta
where "phi '⊑' theta" := (Phi_Theta_Soundness phi theta) : type_scope.



Inductive Det_Trace : Phi -> Prop :=
| DET_Empty : Det_Trace (Phi_Nil)
| DET_Elem  : forall da,
    Det_Trace (Phi_Elem da)
| DET_Seq   : forall phi1 phi2,
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Det_Trace (Phi_Seq phi1 phi2)
| DET_Par   : forall phi1 phi2,
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    not (Conflict_Traces (phi_as_list phi1) (phi_as_list phi2)) /\
      Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    Det_Trace (Phi_Par phi1 phi2). 
