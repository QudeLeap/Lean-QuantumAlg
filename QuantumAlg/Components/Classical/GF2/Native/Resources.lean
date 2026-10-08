/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native
import all QuantumAlg.Components.Classical.GF2.Native.Echelon.Resources
import all QuantumAlg.Components.Classical.GF2.Native.Candidate.Resources
import all QuantumAlg.Components.Classical.GF2.Native.Validation.Resources

/-!
# Actual resources of complete same-context GF(2) recovery

The original prefix, complement, single NOT and decision are followed by the
three actual success branches and the final real packOption. Bounds retain
each component's original native allowance. Durations and counts are read
from the same complete actual path, without asserting reachable-path tightness.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

/-- The selected coordinate of a complete-recovery operation. -/
def gf2OperationEvent (label : Resource.ClassicalOpLabel) : Resource.Event model :=
  .classicalOperation (BitWord.selectedCoordinate (execution := model) label)

/-- The original packOption event retains the candidate's actual machine width. -/
def gf2OutputPackEvent (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) : Resource.Event model :=
  gf2OperationEvent (model := model) (.nominalEncoding (.packOption width))

/-- The actual final instruction emits exactly its original optional encoding event. -/
theorem gf2PackOutput_events (success : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (path : (packOutput success candidate output).Path) :
    (packOutput success candidate output).eventTrace path = [gf2OutputPackEvent model width] := by
  unfold packOutput at path ⊢
  rw [BitWord.bitWord_instruction_eventTrace]
  change [gf2OperationEvent (model := model) (.nominalEncoding (.packOption width))] = _
  rfl

/-- The final pack contributes precisely its selected singleton resource. -/
theorem gf2PackOutput_pool_le (success : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (path : (packOutput success candidate output).Path) :
    (packOutput success candidate output).resourcePool path ≤
      ResourcePool.singleton (gf2OutputPackEvent model width) := by
  rw [Circuit.resourcePool, gf2PackOutput_events]
  simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero]
  exact le_rfl

/-- The final pack is charged once by every selected duration assignment. -/
theorem gf2PackOutput_depth (success : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (duration : Resource.Event model → Nat)
    (path : (packOutput success candidate output).Path) :
    (packOutput success candidate output).depth duration path =
      duration (gf2OutputPackEvent model width) := by
  unfold packOutput at path ⊢
  rw [BitWord.bitWord_instruction_depth]
  change duration
    (gf2OperationEvent (model := model) (.nominalEncoding (.packOption width))) = _
  rfl

/-- The final pack's duration is the sum of its actual singleton event trace. -/
theorem gf2PackOutput_duration_eventTrace (success : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (duration : Resource.Event model → Nat)
    (path : (packOutput success candidate output).Path) :
    (packOutput success candidate output).depth duration path =
      (((packOutput success candidate output).eventTrace path).map duration).sum := by
  rw [gf2PackOutput_depth, gf2PackOutput_events]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- A selected native leaf contributes its selected singleton resource. -/
private theorem instruction_pool_le {inputShape outputShape : CShape}
    (op : ClassicalOp inputShape outputShape ctx ctx)
    (path : (BitWord.instruction (execution := model) op).Path) :
    (BitWord.instruction (execution := model) op).resourcePool path ≤
      ResourcePool.singleton (gf2OperationEvent (model := model) op.label) := by
  rw [Circuit.resourcePool, BitWord.bitWord_instruction_eventTrace]
  simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero]
  exact le_rfl

/-- A selected native leaf contributes its selected event duration once. -/
private theorem instruction_depth_le {inputShape outputShape : CShape}
    (op : ClassicalOp inputShape outputShape ctx ctx)
    (duration : Resource.Event model → Nat)
    (path : (BitWord.instruction (execution := model) op).Path) :
    (BitWord.instruction (execution := model) op).depth duration path ≤
      duration (gf2OperationEvent (model := model) op.label) := by
  rw [BitWord.bitWord_instruction_depth]
  exact le_rfl

/-- A selected native leaf has the same duration as its singleton trace. -/
private theorem instruction_duration {inputShape outputShape : CShape}
    (op : ClassicalOp inputShape outputShape ctx ctx)
    (duration : Resource.Event model → Nat)
    (path : (BitWord.instruction (execution := model) op).Path) :
    (BitWord.instruction (execution := model) op).depth duration path =
      (((BitWord.instruction (execution := model) op).eventTrace path).map duration).sum := by
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_eventTrace]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- All original native stage allowances are added in their actual chronological order. -/
def intoEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (rowCount width : Nat) : ResourcePool model :=
  ((ResourcePool.scale rowCount (rowEnvelope (model := model) rowCount width) +
    echelonEnvelope (model := model)
    rowCount width) +
    (ResourcePool.singleton
      (gf2OperationEvent (model := model) (.wordUnary .complement width)) +
    (ResourcePool.singleton (gf2OperationEvent (model := model) (.bit .not)) +
    (uniqueFreeEnvelope (model := model) width +
    (candidateEnvelope (model := model) rowCount width +
    (decisionTestEnvelope (model := model) width +
    (validationEnvelope (model := model) rowCount width +
    ResourcePool.singleton (gf2OutputPackEvent model width))))))))

/-- Each original stage retains its arbitrary-duration allowance in the same sequence. -/
def intoDepthLimit (rowCount width : Nat) (duration : Resource.Event model → Nat) : Nat :=
  ((rowCount * rowDepthLimit rowCount width duration + echelonDepthLimit rowCount width
    duration) +
    (duration (gf2OperationEvent (model := model) (.wordUnary .complement width)) +
    (duration (gf2OperationEvent (model := model) (.bit .not)) +
    (uniqueFreeDepthLimit width duration +
    (candidateDepthLimit rowCount width duration + (decisionTestDepthLimit width duration +
    (validationDepthLimit rowCount width duration + duration (gf2OutputPackEvent model
    width))))))))

omit [BitWord.Selected model] in
private theorem when_pool_le (success : CWriteRef ctx .bit) (body : Circuit model ctx ctx)
    (budget : ResourcePool model) (bound : ∀ path, body.resourcePool path ≤ budget)
    (path : (whenSuccessful success body).Path) :
    (whenSuccessful success body).resourcePool path ≤ budget := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change (0 : ResourcePool model) ≤ _
        exact zero_le
      · exact bound path

omit [BitWord.Selected model] in
private theorem when_depth_le (success : CWriteRef ctx .bit) (body : Circuit model ctx ctx)
    (duration : Resource.Event model → Nat) (budget : Nat)
    (bound : ∀ path, body.depth duration path ≤ budget)
    (path : (whenSuccessful success body).Path) :
    (whenSuccessful success body).depth duration path ≤ budget := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact Nat.zero_le _
      · exact bound path

omit [BitWord.Selected model] in
private theorem when_duration (success : CWriteRef ctx .bit) (body : Circuit model ctx ctx)
    (duration : Resource.Event model → Nat)
    (equation : ∀ path, body.depth duration path = ((body.eventTrace path).map duration).sum)
    (path : (whenSuccessful success body).Path) :
    (whenSuccessful success body).depth duration path =
      (((whenSuccessful success body).eventTrace path).map
        duration).sum := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · rfl
      · exact equation path

omit [BitWord.Selected model] in
private theorem serial_pool_le (first second : Circuit model ctx ctx)
    (leftBudget rightBudget : ResourcePool model)
    (left : ∀ path, first.resourcePool path ≤ leftBudget)
    (right : ∀ path, second.resourcePool path ≤ rightBudget)
    (path : (first.seq second).Path) :
    (first.seq second).resourcePool path ≤ leftBudget + rightBudget := by
  change ResourcePool.ofList (first.eventTrace path.1 ++ second.eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (left path.1) (right path.2)

omit [BitWord.Selected model] in
private theorem serial_depth_le (first second : Circuit model ctx ctx)
    (duration : Resource.Event model → Nat) (leftBudget rightBudget : Nat)
    (left : ∀ path, first.depth duration path ≤ leftBudget)
    (right : ∀ path, second.depth duration path ≤ rightBudget)
    (path : (first.seq second).Path) :
    (first.seq second).depth duration path ≤ leftBudget + rightBudget :=
  Nat.add_le_add (left path.1) (right path.2)

omit [BitWord.Selected model] in
private theorem serial_duration (first second : Circuit model ctx ctx)
    (duration : Resource.Event model → Nat)
    (left : ∀ path, first.depth duration path = ((first.eventTrace path).map duration).sum)
    (right : ∀ path, second.depth duration path = ((second.eventTrace path).map duration).sum)
    (path : (first.seq second).Path) :
    (first.seq second).depth duration path =
      (((first.seq second).eventTrace path).map
        duration).sum := by
  change first.depth duration path.1 + second.depth duration path.2 =
    ((first.eventTrace path.1 ++ second.eventTrace path.2).map duration).sum
  rw [List.map_append, List.sum_append]
  exact congrArg₂ (· + ·) (left path.1) (right path.2)

variable (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
  (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
  (used : CWriteRef ctx (.unsignedWord rowCount))
  (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
  (columns candidate zero : CWriteRef ctx (.unsignedWord width))
  (success : CWriteRef ctx .bit) (output : CWriteRef ctx (.option (.unsignedWord width)))

/-- The original complete circuit charges all native stages and its final actual packing. -/
theorem gf2Into_pool_le
    (path : (into input matrix used rows columns candidate zero success output).Path) :
    (into input matrix used rows columns candidate zero success output).resourcePool path ≤
      intoEnvelope model rowCount width :=
  (serial_pool_le _ _ _ _ (gf2LoadAndReduce_pool_le matrix used rows columns input)
  (serial_pool_le _ _ _ _
    (instruction_pool_le (complementPivotMaskOp columns))
  (serial_pool_le _ _ _ _ (instruction_pool_le (pivotFoundOp success))
  (serial_pool_le _ _ _ _ (gf2UniqueFree_pool_le columns zero success)
  (serial_pool_le _ _ _ _ (when_pool_le success _ _ (gf2BuildCandidate_pool_le matrix rows
    columns candidate zero))
  (serial_pool_le _ _ _ _ (when_pool_le success _ _ (gf2CandidateNonzero_pool_le candidate zero
    success))
  (serial_pool_le _ _ _ _ (when_pool_le success _ _ (gf2ValidationSamples_pool_le input
    candidate success))
  (gf2PackOutput_pool_le success candidate output)))))))) path

/-- The complete original dependency order retains every actual event-duration allowance. -/
theorem gf2Into_depth_le (duration : Resource.Event model → Nat)
    (path : (into input matrix used rows columns candidate zero success output).Path) :
    (into input matrix used rows columns candidate zero success output).depth duration path ≤
      intoDepthLimit rowCount width duration :=
  (serial_depth_le _ _ duration _ _ (gf2LoadAndReduce_depth_le matrix used rows columns input
    duration)
  (serial_depth_le _ _ duration _ _
    (instruction_depth_le (complementPivotMaskOp columns) duration)
  (serial_depth_le _ _ duration _ _ (instruction_depth_le (pivotFoundOp success) duration)
  (serial_depth_le _ _ duration _ _ (gf2UniqueFree_depth_le columns zero success duration)
  (serial_depth_le _ _ duration _ _ (when_depth_le success _ duration _
    (gf2BuildCandidate_depth_le matrix rows columns candidate zero duration))
  (serial_depth_le _ _ duration _ _ (when_depth_le success _ duration _
    (gf2CandidateNonzero_depth_le candidate zero success duration))
  (serial_depth_le _ _ duration _ _ (when_depth_le success _ duration _
    (gf2ValidationSamples_depth_le input candidate success duration))
  (fun current => (gf2PackOutput_depth success candidate output duration current).le)))))))) path

/-- Exact duration is the sum of the events emitted by that same complete actual path. -/
theorem gf2Into_duration_eventTrace (duration : Resource.Event model → Nat)
    (path : (into input matrix used rows columns candidate zero success output).Path) :
    (into input matrix used rows columns candidate zero success output).depth duration path =
      (((into input matrix used rows columns candidate zero success output).eventTrace path).map
        duration).sum :=
  (serial_duration _ _ duration (gf2LoadAndReduce_duration_eventTrace matrix used rows columns
    input duration)
  (serial_duration _ _ duration
    (instruction_duration (complementPivotMaskOp columns) duration)
  (serial_duration _ _ duration (instruction_duration (pivotFoundOp success) duration)
  (serial_duration _ _ duration (gf2UniqueFree_duration_eventTrace columns zero success
    duration)
  (serial_duration _ _ duration (when_duration success _ duration
    (gf2BuildCandidate_duration_eventTrace matrix rows columns candidate zero duration))
  (serial_duration _ _ duration (when_duration success _ duration
    (gf2CandidateNonzero_duration_eventTrace candidate zero success duration))
  (serial_duration _ _ duration (when_duration success _ duration
    (gf2ValidationSamples_duration_eventTrace input candidate success duration))
  (gf2PackOutput_duration_eventTrace success candidate output duration)))))))) path

/-- The actual native instruction count is bounded by the original unit-duration stage sum. -/
theorem gf2Into_eventCount_le
    (path : (into input matrix used rows columns candidate zero success output).Path) :
    ((into input matrix used rows columns candidate zero success output).eventTrace path).length ≤
      intoDepthLimit (model := model) rowCount width (fun _ => 1) := by
  have bound := gf2Into_depth_le input matrix used rows columns candidate zero success output
    (fun _ => 1) path
  rw [gf2Into_duration_eventTrace] at bound
  simpa only [List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_one] using bound

end

end QuantumAlg.ClassicalRoutines.GF2.Native
