/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Initialization

/-!
# Actual final-output failure mass

The real final option-pack reports no result precisely when the existing
accepted bit is false, regardless of the selected word. The event reads the
same final batchResultRead and preserves every complete reference block.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

attribute [local irreducible] persistentCtx packBatchResultStep

private theorem packOption_none_iff {shape : CShape}
    (tag : CShape.Value .bit) (value : CShape.Value shape) :
    CShape.packOption (.product tag value) = .optionNone ↔ tag.toBool = false := by
  cases tag with
  | bit flag => cases flag <;> simp [CShape.packOption, CShape.Value.toBool]

private theorem option_none_weight {shape : CShape} {R : Register}
    (state : DensityOperator R) (tag : CShape.Value .bit) (value : CShape.Value shape)
    (observed : CShape.Value (.option shape))
    (same : observed = CShape.packOption (.product tag value)) :
    (if observed = .optionNone then Effect.one R else Effect.zero R).weight state =
      (if tag.toBool = false then Effect.one R else Effect.zero R).weight state := by
  simp only [same, packOption_none_iff]

/-- The actual final optional output is absent exactly with the incoming failure mass. -/
theorem packBatchResult_none_weight (width scalarWidth : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H)) :
    ((packBatchResult ctx width scalarWidth).execute Reference state).effectWeight
        (fun entry => if entry.1.read (batchResultRead ctx width scalarWidth) = .optionNone then
          Effect.one ((batchResultCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((batchResultCtx ctx width scalarWidth).register.prod Reference)) =
      state.effectWeight (fun entry => if (entry.1.read
        (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false then
          Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) := by
  let observe := fun entry : Store (batchResultCtx ctx width scalarWidth) × H =>
    entry.1.read (batchResultRead ctx width scalarWidth)
  rw [packBatchResult_execute]
  have observed :
      (packBatchResultState ctx width scalarWidth Reference state).effectWeight
        (fun entry => if entry.1.read (batchResultRead ctx width scalarWidth) = .optionNone then
          Effect.one ((batchResultCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((batchResultCtx ctx width scalarWidth).register.prod Reference)) =
      (packBatchResultObserved ctx width scalarWidth observe Reference state).effectWeight
        (fun value => if value = .optionNone then
          Effect.one ((batchResultCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((batchResultCtx ctx width scalarWidth).register.prod Reference)) := by
    unfold packBatchResultObserved
    let update : Store (batchResultCtx ctx width scalarWidth) ×
        (model.HiddenState × (H × (packBatchResult ctx width scalarWidth).Path)) →
        (CShape.option (.unsignedWord scalarWidth)).Value :=
      fun entry => observe (entry.1, entry.2.2.1)
    let effects : (CShape.option (.unsignedWord scalarWidth)).Value →
        Effect ((batchResultCtx ctx width scalarWidth).register.prod Reference) :=
      fun value => if value = .optionNone then Effect.one _ else Effect.zero _
    change (packBatchResultState ctx width scalarWidth Reference state).effectWeight
      (fun entry => effects (update entry)) =
        ((packBatchResultState ctx width scalarWidth Reference state).mapClassical
          update).effectWeight effects
    exact (ExecutionState.effectWeight_mapClassical_decision (Classical.decEq _)
      (packBatchResultState ctx width scalarWidth Reference state) update effects).symm
  rw [observed, packBatchResult_observe]
  unfold packBatchResultExpected
  rw [ExecutionState.effectWeight_mapClassical_decision]
  unfold ExecutionState.effectWeight
  apply Finset.sum_congr rfl
  intro entry _
  dsimp only
  exact option_none_weight (state.block entry)
    (entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef))
    (entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)) _
    (packBatchResultStep_output ctx width scalarWidth entry.1)


end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
