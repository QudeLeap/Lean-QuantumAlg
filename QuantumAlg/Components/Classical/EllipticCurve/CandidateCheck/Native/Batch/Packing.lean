/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual final batch-result packing

After all original attempts, one actual retained cell is allocated. The
original option-pack instruction reads the persistent accepted and selected
latches and writes that cell. Its real record preserves all earlier inputs,
the seven persistent destinations, arbitrary quantum references and history.
The final native event and the new optional word are both charged explicitly.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} (ctx : RuntimeCtx kind) (width scalarWidth : Nat)

/-- The actual retention and option-pack return their complete Store and instruction path. -/
def packBatchResultStep (before : Store (persistentCtx ctx width scalarWidth)) :
    Store (batchResultCtx ctx width scalarWidth) × (packBatchResult ctx width scalarWidth).Path :=
  let inner := persistentCtx ctx width scalarWidth
  ((before.pushRetained inner.canonicalFreshKey (.option (.unsignedWord scalarWidth))
    inner.canonicalFreshKey_fresh).applyOp (batchResultOp ctx width scalarWidth), ((), ()))

section

attribute [local irreducible] persistentCtx

/-- Lift the actual deterministic Store record to every complete quantum-reference block. -/
def packBatchResultState (Reference : Register) {History : Type} [Fintype History]
    (state : State (persistentCtx ctx width scalarWidth) Reference History) :
    State (batchResultCtx ctx width scalarWidth) Reference
      (History × (packBatchResult ctx width scalarWidth).Path) :=
  state.mapClassical (fun entry =>
    ((packBatchResultStep ctx width scalarWidth entry.1).1,
      (entry.2, (packBatchResultStep ctx width scalarWidth entry.1).2)))

/-- Actual result retention and packing preserve every complete reference block and history. -/
theorem packBatchResult_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State (persistentCtx ctx width scalarWidth) Reference History) :
    (packBatchResult ctx width scalarWidth).execute Reference state =
      packBatchResultState ctx width scalarWidth Reference state := by
  refine (Circuit.execute_retainedStep (persistentCtx ctx width scalarWidth)
    (persistentCtx ctx width scalarWidth).canonicalFreshKey (.option (.unsignedWord scalarWidth))
    (persistentCtx ctx width scalarWidth).canonicalFreshKey_fresh
    (batchResultOp ctx width scalarWidth) state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

/-- The actual final output encodes exactly the incoming persistent first-success latches. -/
theorem packBatchResultStep_output (before : Store (persistentCtx ctx width scalarWidth)) :
    (packBatchResultStep ctx width scalarWidth before).1.read
      (batchResultRead ctx width scalarWidth) =
        CShape.packOption (.product
          (before.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef))
          (before.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef))) := by
  let inner := persistentCtx ctx width scalarWidth
  let shape := CShape.option (.unsignedWord scalarWidth)
  let entered := before.pushRetained inner.canonicalFreshKey shape inner.canonicalFreshKey_fresh
  have actual := Store.read_applyOp_output entered (batchResultOp ctx width scalarWidth)
  change (packBatchResultStep ctx width scalarWidth before).1.read
    (batchResultRead ctx width scalarWidth) =
      CShape.packOption (.product
        (entered.read ((CInputRef.storage
          (persistentAccepted ctx width scalarWidth).toCStorageRef).underRetained
            inner.canonicalFreshKey shape inner.canonicalFreshKey_fresh))
        (entered.read ((CInputRef.storage
          (persistentSelected ctx width scalarWidth).toCStorageRef).underRetained
            inner.canonicalFreshKey shape inner.canonicalFreshKey_fresh))) at actual
  simpa only [entered, Store.read_pushRetained_underRetained] using actual

/-- Every earlier structural input and retained latch survives the new output write unchanged. -/
theorem packBatchResultStep_read_other (before : Store (persistentCtx ctx width scalarWidth))
    {shape : CShape} (input : CInputRef (persistentCtx ctx width scalarWidth) shape) :
    (packBatchResultStep ctx width scalarWidth before).1.read
      (input.underRetained (persistentCtx ctx width scalarWidth).canonicalFreshKey
        (.option (.unsignedWord scalarWidth))
        (persistentCtx ctx width scalarWidth).canonicalFreshKey_fresh) = before.read input := by
  let inner := persistentCtx ctx width scalarWidth
  let outputShape := CShape.option (.unsignedWord scalarWidth)
  let entered := before.pushRetained inner.canonicalFreshKey outputShape
    inner.canonicalFreshKey_fresh
  exact (Store.read_applyOp_of_not_mem_storageKeys entered (batchResultOp ctx width scalarWidth)
    (input.underRetained inner.canonicalFreshKey outputShape inner.canonicalFreshKey_fresh)
    (input.fresh_not_mem_storageKeys_underRetained inner.canonicalFreshKey outputShape
      inner.canonicalFreshKey_fresh)).trans
      (Store.read_pushRetained_underRetained before inner.canonicalFreshKey outputShape
        inner.canonicalFreshKey_fresh input)

/-- The final retained result emits exactly the original paid option-pack instruction. -/
theorem packBatchResult_eventTrace (path : (packBatchResult ctx width scalarWidth).Path) :
    (packBatchResult ctx width scalarWidth).eventTrace path =
      [.classicalOperation (.nominalEncoding (.packOption scalarWidth))] := rfl

/-- The exact native pool is the singleton event of that same actual final instruction. -/
theorem packBatchResult_resourcePool (path : (packBatchResult ctx width scalarWidth).Path) :
    (packBatchResult ctx width scalarWidth).resourcePool path =
      ResourcePool.ofList [.classicalOperation (.nominalEncoding (.packOption scalarWidth))] := rfl

/-- Exactly one real native instruction executes even for a zero-width selected word. -/
theorem packBatchResult_eventCount (path : (packBatchResult ctx width scalarWidth).Path) :
    ((packBatchResult ctx width scalarWidth).eventTrace path).length = 1 := rfl

/-- The actual final dependency duration is exactly the original pack-operation duration. -/
theorem packBatchResult_depth (duration : Resource.Event kind → Nat)
    (path : (packBatchResult ctx width scalarWidth).Path) :
    (packBatchResult ctx width scalarWidth).depth duration path =
      duration (.classicalOperation (.nominalEncoding (.packOption scalarWidth))) := by
  change 0 + _ = _
  exact Nat.zero_add _

/-- Resident peak adds the actual final optional word beside all seven persistent destinations. -/
theorem packBatchResult_resident (path : (packBatchResult ctx width scalarWidth).Path) :
    (packBatchResult ctx width scalarWidth).peakResidentSpace path =
      SpacePool.ofShape (.option (.unsignedWord scalarWidth)) +
        (persistentCtx ctx width scalarWidth).residentSpace := by
  exact (Circuit.retainedStep_peakResidentSpace (persistentCtx ctx width scalarWidth)
    (persistentCtx ctx width scalarWidth).canonicalFreshKey (.option (.unsignedWord scalarWidth))
    (persistentCtx ctx width scalarWidth).canonicalFreshKey_fresh
    (batchResultOp ctx width scalarWidth) path).trans
      (RuntimeCtx.residentSpace_addRetained _ _ _ _)

/-- Auxiliary peak includes the same real output allocation and the complete prior workspace. -/
theorem packBatchResult_auxiliary (path : (packBatchResult ctx width scalarWidth).Path) :
    (packBatchResult ctx width scalarWidth).peakAuxiliarySpace path =
      SpacePool.ofShape (.option (.unsignedWord scalarWidth)) +
        (persistentCtx ctx width scalarWidth).auxiliarySpace := by
  exact (Circuit.retainedStep_peakAuxiliarySpace (persistentCtx ctx width scalarWidth)
    (persistentCtx ctx width scalarWidth).canonicalFreshKey (.option (.unsignedWord scalarWidth))
    (persistentCtx ctx width scalarWidth).canonicalFreshKey_fresh
    (batchResultOp ctx width scalarWidth) path).trans
      (RuntimeCtx.auxiliarySpace_addRetained _ _ _ _)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
