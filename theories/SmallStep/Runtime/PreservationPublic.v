Require Import theories.SmallStep.Runtime.NoAllocPreservation.
Require Import theories.SmallStep.Runtime.Preservation.
Require Import theories.SmallStep.Runtime.RegularPreservation.

(** Stable preservation endpoints.

    The preservation files contain rule-by-rule internal lemmas for each state
    shape.  This facade collects the reusable theorems that other proof layers
    should prefer. *)

Definition Runtime_step_store_preservation :=
  Step_store_resolved_state_preservation.

Definition Runtime_steps_store_preservation :=
  Steps_store_resolved_state_preservation.

Definition Runtime_stepsN_store_preservation :=
  StepsN_store_resolved_state_preservation.

Definition Runtime_steps_view_store_preservation :=
  StepsView_store_resolved_state_preservation.

Definition Runtime_step_heap_neutral_regular_preservation :=
  Step_heap_neutral_regular_state_preservation.

Definition Runtime_steps_heap_neutral_regular_preservation :=
  Steps_heap_neutral_regular_state_preservation.

Definition Runtime_stepsN_heap_neutral_regular_preservation :=
  StepsN_heap_neutral_regular_state_preservation.

Definition Runtime_step_heap_neutral_resolved_preservation :=
  Step_heap_neutral_resolved_state_preservation_wf.

Definition Runtime_steps_heap_neutral_resolved_preservation :=
  Steps_heap_neutral_resolved_state_preservation_wf.

Definition Runtime_noalloc_step_preservation :=
  NoAllocStateShape_step_preservation.
