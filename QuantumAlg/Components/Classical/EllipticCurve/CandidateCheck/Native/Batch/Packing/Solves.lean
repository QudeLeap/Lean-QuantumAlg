/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing
import all QuantumAlg.Core.Execution.Retained.Distribution
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Execution.CycleSchedule

/-!
# The actual checked batch's deterministic final packing protocol

The original option pack has its own independent result specification. Its
same actual run proves certain output, restoration, the one native classical
event and both live-space peaks. A standalone classical schedule retains this
paid tail without declaring an extra quantum computation or final reset.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.BatchPacking

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  (ctx : RuntimeCtx model.kind) (width scalarWidth : Nat)

/-- Deterministic option encoding of the two actual incoming result latches.

**Input.** Any incoming persistent store, joint service state and reference.
**Output.** The incoming accepted bit and selected word encoded as an option.
**Resource budget.** One width-indexed option-pack operation, one additional
optional word and the complete existing resident and auxiliary contexts;
unit dependency depth one.
**Success.** The specified exact option is returned with probability one.
**Source.** The deterministic option encoding of the existing checked batch's
`packBatchResult` instruction and `CShape.packOption` value semantics.
-/
def problem : Problem model (persistentCtx ctx width scalarWidth)
    (batchResultCtx ctx width scalarWidth) (.option (.unsignedWord scalarWidth)) where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun before output => output = CShape.packOption (.product
    (before.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef))
    (before.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)))
  successLB := ⟨1, le_rfl⟩
  states := []
  resources :=
    { events := ResourcePool.ofList [.classicalOperation
        (BitWord.selectedCoordinate (execution := model)
          (.nominalEncoding (.packOption scalarWidth)))]
      resident := SpacePool.ofShape (.option (.unsignedWord scalarWidth)) +
        (persistentCtx ctx width scalarWidth).residentSpace
      auxiliary := SpacePool.ofShape (.option (.unsignedWord scalarWidth)) +
        (persistentCtx ctx width scalarWidth).auxiliarySpace }
  depth :=
    { duration := fun _ => 1
      limit := 1
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

/-- The original final retained-cell allocation and option-pack instruction. -/
def algorithm : Algorithm model (persistentCtx ctx width scalarWidth)
    (batchResultCtx ctx width scalarWidth) (.option (.unsignedWord scalarWidth)) :=
  ⟨{ code := packBatchResult ctx width scalarWidth
     output := Output.all _ (.read (batchResultRead ctx width scalarWidth)) }⟩

private def bodyStep
    (before : Store (batchResultCtx ctx width scalarWidth) × model.HiddenState) :
    (Store (batchResultCtx ctx width scalarWidth) × model.HiddenState) ×
      (BitWord.instruction (execution := model)
        (batchResultOp ctx width scalarWidth)).Path :=
  let result := BitWord.instructionStep (execution := model)
    (batchResultOp ctx width scalarWidth) before.1
  ((result.1, before.2), result.2)

private theorem relational {Reference : Register}
    (input : OracleInput model.classicalOracles (persistentCtx ctx width scalarWidth)
      Reference) :
    (algorithm (model := model) ctx width scalarWidth).relationalDistribution input =
      (input.state.toPMF input.normalized).map (fun entry =>
        (entry.1, CShape.packOption (.product
          (entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef))
          (entry.1.read
            (.storage (persistentSelected ctx width scalarWidth).toCStorageRef))))) := by
  let inner := persistentCtx ctx width scalarWidth
  have mapped := AlgorithmRun.relationalDistribution_retained_eq_map
    (model := model) inner inner.canonicalFreshKey (.option (.unsignedWord scalarWidth))
    inner.canonicalFreshKey_fresh
    (BitWord.instruction (execution := model) (batchResultOp ctx width scalarWidth))
    (algorithm (model := model) ctx width scalarWidth).run.output
    (bodyStep ctx width scalarWidth)
    (fun _ {_} _ state => BitWord.bitWord_instruction_execute _ state) input
  refine mapped.trans ?_
  apply congrArg ((input.state.toPMF input.normalized).map)
  funext entry
  exact congrArg (Prod.mk entry.1) (packBatchResultStep_output ctx width scalarWidth entry.1)

/-- Every actual final packing event is the paid classical option operation. -/
theorem onlyClassical : Circuit.IsClassical (packBatchResult (model := model)
    ctx width scalarWidth) := by
  intro path event present
  rw [packBatchResult_eventTrace] at present
  have same := List.mem_singleton.mp present
  exact Or.inl ⟨_, same⟩

/-- Actual packing restores every borrowed classical-quantum-reference correlation. -/
theorem restores (Reference : Register) {History : Type} [Fintype History]
    (state : State (persistentCtx ctx width scalarWidth) Reference
      (model.HiddenState × History)) :
    (packBatchResult (model := model) ctx width scalarWidth).BorrowedRestored
      Reference state ((packBatchResult ctx width scalarWidth).execute Reference state) := by
  let inner := persistentCtx ctx width scalarWidth
  let retention := Circuit.retain (model := model) inner inner.canonicalFreshKey
    (.option (.unsignedWord scalarWidth)) inner.canonicalFreshKey_fresh
  let body := BitWord.instruction (execution := model) (batchResultOp ctx width scalarWidth)
  exact Circuit.borrowedRestored_seq retention body state
    (Circuit.borrowedRestored_retain _ _ _ state)
    (Circuit.borrowedRestored_classical (BitWord.selectedApplication
      (execution := model) (batchResultOp ctx width scalarWidth))
        (retention.execute Reference state))

/-- The same original run satisfies all seven independent protocol clauses. -/
theorem solves : Algorithm.Solves (algorithm (model := model) ctx width scalarWidth)
    (problem (model := model) ctx width scalarWidth) := by
  constructor
  · intro Reference input _valid _initialized
    change 1 ≤ ((algorithm (model := model) ctx width scalarWidth).relationalDistribution
      input).toOuterMeasure _
    rw [relational, PMF.toOuterMeasure_map_apply]
    apply le_of_eq
    symm
    exact (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (fun _ _ => rfl)
  · intro _Reference _input _valid _initialized _requirement present
    exact False.elim (List.not_mem_nil present)
  · intro Reference input _valid _initialized
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact restores ctx width scalarWidth reference state
  · intro _Reference _input _valid _initialized path _supported
    exact le_of_eq (packBatchResult_resourcePool ctx width scalarWidth path)
  · intro _Reference _input _valid _initialized path _supported
    exact le_of_eq (packBatchResult_resident ctx width scalarWidth path)
  · intro _Reference _input _valid _initialized path _supported
    exact le_of_eq (packBatchResult_auxiliary ctx width scalarWidth path)
  · intro _Reference _input _valid _initialized path _supported
    exact le_of_eq (packBatchResult_depth ctx width scalarWidth (fun _ => 1) path)

/-- The exact paid final pack is a standalone classical completion section. -/
def schedule : Circuit.CycleSchedule
    (.classical (problem (model := model) ctx width scalarWidth))
    (packBatchResult (model := model) ctx width scalarWidth) :=
  .classical _
    { output := (algorithm (model := model) ctx width scalarWidth).run.output
      certified := solves ctx width scalarWidth }
    (onlyClassical ctx width scalarWidth)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.BatchPacking
