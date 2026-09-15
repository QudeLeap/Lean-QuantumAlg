/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Validation
import all QuantumAlg.Components.Classical.GF2.Native.Decision.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources

/-!
# Actual event allowances of original sample validation

Every column charges its original AND and XOR. The original parity clear,
possible copy and clear failure markers, and unconditional final self-AND
are counted from the same actual paths. Uniform allowances cover every
syntactic branch without claiming the bound is attained by reachable stores.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

/-- The original product and accumulation events retain their chronological order. -/
def validationColumnEvents (kind : ProblemKind) : List (Resource.Event kind) :=
  [.classicalOperation (.bit .and), .classicalOperation (.bit .xor)]

/-- The actual column emits both original native bit instructions. -/
theorem gf2ValidationColumn_events
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (parity product : CWriteRef ctx .bit)
    (row : Fin rowCount) (column : Fin width)
    (path : (validationColumn input candidate parity product row column).Path) :
    (validationColumn input candidate parity product row column).eventTrace path =
      validationColumnEvents kind := rfl

/-- The exact actual column duration equals the sum of its two emitted event durations. -/
theorem gf2ValidationColumn_duration_eventTrace
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (parity product : CWriteRef ctx .bit)
    (row : Fin rowCount) (column : Fin width) (duration : Resource.Event kind → Nat)
    (path : (validationColumn input candidate parity product row column).Path) :
    (validationColumn input candidate parity product row column).depth duration path =
      (((validationColumn input candidate parity product row column).eventTrace path).map
        duration).sum := by
  change duration (.classicalOperation (.bit .and)) +
    duration (.classicalOperation (.bit .xor)) =
      duration (.classicalOperation (.bit .and)) +
        (duration (.classicalOperation (.bit .xor)) + 0)
  omega

/-- One actual parity clear precedes all columns and the possible two failure markers. -/
def validationRowEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.singleton (.classicalOperation (.bit .xor)) +
    (ResourcePool.scale width (ResourcePool.ofList (validationColumnEvents kind)) +
      ResourcePool.ofList (decisionFailureEvents kind))

/-- The original full row traversal is followed by its unconditional actual self-AND. -/
def validationEnvelope (kind : ProblemKind) (rowCount width : Nat) : ResourcePool kind :=
  ResourcePool.scale rowCount (validationRowEnvelope kind width) +
    ResourcePool.singleton (.classicalOperation (.bit .and))

/-- Every original row stage retains the arbitrary durations of its real bit events. -/
def validationRowDepthLimit (width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  duration (.classicalOperation (.bit .xor)) +
    ((∑ _column : Fin width, (duration (.classicalOperation (.bit .and)) +
      duration (.classicalOperation (.bit .xor)))) +
        (duration (.classicalOperation (.bit .copy)) + duration (.classicalOperation (.bit .xor))))

/-- Original rows and the final success marker retain their serial duration allowance. -/
def validationDepthLimit (rowCount width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  (∑ _row : Fin rowCount, validationRowDepthLimit width duration) +
    duration (.classicalOperation (.bit .and))

private theorem rowBody_pool_le
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (success parity product : CWriteRef ctx .bit) (row : Fin rowCount)
    (path : (validationRowBody input candidate success parity product row).Path) :
    (validationRowBody input candidate success parity product row).resourcePool path ≤
      validationRowEnvelope kind width := by
  change ResourcePool.ofList
    (([.classicalOperation (.bit .xor)] : List (Resource.Event kind)) ++
      ((Circuit.forRange width (validationColumn input candidate parity product row)).eventTrace
        path.2.1 ++ (decisionChoice true success path.2.2.1).eventTrace path.2.2.2)) ≤ _
  simp only [ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add
    (Circuit.forRange_pool_le width _ _ (fun _column _path => le_rfl) path.2.1)
    (choice_pool_le true success path.2.2.1 path.2.2.2))

private theorem rowBody_depth_le
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (success parity product : CWriteRef ctx .bit) (row : Fin rowCount)
    (duration : Resource.Event kind → Nat)
    (path : (validationRowBody input candidate success parity product row).Path) :
    (validationRowBody input candidate success parity product row).depth duration path ≤
      validationRowDepthLimit width duration :=
  Nat.add_le_add_left (Nat.add_le_add
    (Circuit.forRange_depth_le_sum width _ duration _ (fun _column _path => le_rfl) path.2.1)
    (choice_depth_le true success path.2.2.1 duration path.2.2.2)) _

private theorem rowBody_duration
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (success parity product : CWriteRef ctx .bit) (row : Fin rowCount)
    (duration : Resource.Event kind → Nat)
    (path : (validationRowBody input candidate success parity product row).Path) :
    (validationRowBody input candidate success parity product row).depth duration path =
      (((validationRowBody input candidate success parity product row).eventTrace path).map
        duration).sum := by
  change duration (.classicalOperation (.bit .xor)) +
    ((Circuit.forRange width (validationColumn input candidate parity product row)).depth
      duration path.2.1 + (decisionChoice true success path.2.2.1).depth duration path.2.2.2) =
    ((([.classicalOperation (.bit .xor)] : List (Resource.Event kind)) ++
      ((Circuit.forRange width (validationColumn input candidate parity product row)).eventTrace
        path.2.1 ++ (decisionChoice true success path.2.2.1).eventTrace path.2.2.2)).map
          duration).sum
  rw [Circuit.forRange_duration_eventTrace width _ duration
    (gf2ValidationColumn_duration_eventTrace input candidate parity product row · duration),
    choice_duration, gf2DecisionChoice_events]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Both actual row scopes preserve the original native event allowance. -/
theorem gf2ValidationRow_pool_le
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (path : (validateRow input candidate success row).Path) :
    (validateRow input candidate success row).resourcePool path ≤
      validationRowEnvelope kind width :=
  rowBody_pool_le _ _ _ _ _ row path

/-- Both actual row scopes preserve all original arbitrary event durations. -/
theorem gf2ValidationRow_depth_le
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (duration : Resource.Event kind → Nat)
    (path : (validateRow input candidate success row).Path) :
    (validateRow input candidate success row).depth duration path ≤
      validationRowDepthLimit width duration :=
  rowBody_depth_le _ _ _ _ _ row duration path

/-- Actual lexical initialization and release preserve the same-path serial duration equation. -/
theorem gf2ValidationRow_duration_eventTrace
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (duration : Resource.Event kind → Nat)
    (path : (validateRow input candidate success row).Path) :
    (validateRow input candidate success row).depth duration path =
      (((validateRow input candidate success row).eventTrace path).map duration).sum :=
  rowBody_duration _ _ _ _ _ row duration path

/-- The real current-success branch cannot exceed the original selected-row allowance. -/
theorem gf2ValidationSample_pool_le
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (path : (validationSample input candidate success row).Path) :
    (validationSample input candidate success row).resourcePool path ≤
      validationRowEnvelope kind width := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change (0 : ResourcePool kind) ≤ _
        exact zero_le
      · exact gf2ValidationRow_pool_le input candidate success row path

/-- The current-success branch retains the original arbitrary-duration row allowance. -/
theorem gf2ValidationSample_depth_le
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (duration : Resource.Event kind → Nat)
    (path : (validationSample input candidate success row).Path) :
    (validationSample input candidate success row).depth duration path ≤
      validationRowDepthLimit width duration := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact Nat.zero_le _
      · exact gf2ValidationRow_depth_le input candidate success row duration path

/-- The actual success outcome selects the same path in both trace and duration. -/
theorem gf2ValidationSample_duration_eventTrace
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (duration : Resource.Event kind → Nat)
    (path : (validationSample input candidate success row).Path) :
    (validationSample input candidate success row).depth duration path =
      (((validationSample input candidate success row).eventTrace path).map duration).sum := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · rfl
      · exact gf2ValidationRow_duration_eventTrace input candidate success row duration path

/-- The complete actual row traversal charges its final real self-AND, even with no rows. -/
theorem gf2ValidationSamples_pool_le
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (path : (validateSamples input candidate success).Path) :
    (validateSamples input candidate success).resourcePool path ≤
      validationEnvelope kind rowCount width := by
  change ResourcePool.ofList
    ((Circuit.forRange rowCount (validationSample input candidate success)).eventTrace path.1 ++
      [.classicalOperation (.bit .and)]) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (Circuit.forRange_pool_le rowCount _ _
    (gf2ValidationSample_pool_le input candidate success) path.1) le_rfl

/-- All original row and final-marker durations are retained in the complete allowance. -/
theorem gf2ValidationSamples_depth_le
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (duration : Resource.Event kind → Nat) (path : (validateSamples input candidate success).Path) :
    (validateSamples input candidate success).depth duration path ≤
      validationDepthLimit rowCount width duration :=
  Nat.add_le_add_right (Circuit.forRange_depth_le_sum rowCount _ duration _
    (gf2ValidationSample_depth_le input candidate success · duration) path.1) _

/-- The same full actual validation path determines both serial duration and emitted events. -/
theorem gf2ValidationSamples_duration_eventTrace
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (duration : Resource.Event kind → Nat) (path : (validateSamples input candidate success).Path) :
    (validateSamples input candidate success).depth duration path =
      (((validateSamples input candidate success).eventTrace path).map duration).sum := by
  change (Circuit.forRange rowCount (validationSample input candidate success)).depth
    duration path.1 + duration (.classicalOperation (.bit .and)) =
    (((Circuit.forRange rowCount (validationSample input candidate success)).eventTrace path.1 ++
      ([.classicalOperation (.bit .and)] : List (Resource.Event kind))).map duration).sum
  rw [Circuit.forRange_duration_eventTrace rowCount _ duration
    (gf2ValidationSample_duration_eventTrace input candidate success · duration)]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Every syntactic selected-row path has at most two events per column plus three markers. -/
theorem gf2ValidationRow_unitDepth_le
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (path : (validateRow input candidate success row).Path) :
    (validateRow input candidate success row).depth (fun _ => 1) path ≤ 2 * width + 3 := by
  have bound := gf2ValidationRow_depth_le input candidate success row (fun _ => 1) path
  simp only [validationRowDepthLimit, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at bound
  omega

/-- The original full validation allowance includes its final real marker at every row count. -/
theorem gf2ValidationSamples_unitDepth_le
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (path : (validateSamples input candidate success).Path) :
    (validateSamples input candidate success).depth (fun _ => 1) path ≤
      rowCount * (2 * width + 3) + 1 := by
  have bound := gf2ValidationSamples_depth_le input candidate success (fun _ => 1) path
  simpa only [validationDepthLimit, validationRowDepthLimit, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, show (1 : Nat) + 1 = 2 from rfl,
    Nat.mul_comm width 2, Nat.add_assoc, Nat.add_left_comm 1] using bound

end

end QuantumAlg.ClassicalRoutines.GF2.Native
