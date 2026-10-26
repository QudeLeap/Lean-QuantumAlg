/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Framing
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Layer.Denominators
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Seed
import all QuantumAlg.Core.Execution.Store.Ext
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Protection

/-!
# Structural input reads retained by the actual table builder

A read whose storage keys avoid the actual five arrays and four working
words survives every original row, batch and layer. The statement is
independent of the width, window size and input values. It observes the
same complete returned Store, service state and chronological Path.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open Execution ClassicalAlgorithms.Modular

noncomputable section

private lemma sequence_record_read_other {model : ExecutionModel}
    {ctx : RuntimeCtx model.kind} {allocation : Bool}
    (first last : Circuit model ctx ctx allocation)
    (head : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × first.Path)
    (tail : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × last.Path)
    {shape : CShape} (observed : CInputRef ctx shape)
    (headRead : ∀ before, (head before).1.1.read observed =
      before.1.read observed)
    (tailRead : ∀ before, (tail before).1.1.read observed =
      before.1.read observed)
    (before : Store ctx × model.HiddenState) :
    (Circuit.sequenceRecord first last head tail before).1.1.read observed =
      before.1.read observed :=
  (tailRead (head before).1).trans (headRead before)

private lemma range_record_read_other {model : ExecutionModel}
    {ctx : RuntimeCtx model.kind} (count : Nat) (body : Fin count → Circuit model ctx ctx)
    (records : ∀ index, Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (body index).Path)
    {shape : CShape} (observed : CInputRef ctx shape)
    (stepRead : ∀ index before, (records index before).1.1.read observed =
      before.1.read observed) (before : Store ctx × model.HiddenState) :
    (Circuit.forRangeRecord count body records before).1.1.read observed =
      before.1.read observed :=
  Circuit.forRangeRecord_invariant count body records
    (fun _ current => current.1.read observed = before.1.read observed)
    (fun index current established => (stepRead index current).trans established) before rfl

namespace TableFrame

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

private lemma seed_record_read_other (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) {shape : CShape} (observed : CInputRef ctx shape)
    (free : ∀ key ∈ frame.outputKeys, key ∉ observed.storageKeys)
    (before : Store ctx × model.HiddenState) :
    (frame.prepareSeedRecord spec level environment before).1.1.read observed =
      before.1.read observed := by
  rcases level with ⟨level, bound⟩
  cases level with
  | zero =>
      exact frame.coordinates.seedRecord_read_other frame.baseX frame.baseY
        (layerSeed window ⟨0, bound⟩) before observed
        (free _ (by simp [outputKeys, coordinates]))
        (free _ (by simp [outputKeys, coordinates]))
  | succ level =>
      apply RowInstruction.rangeRecord_read_other
      intro index
      apply free
      fin_cases index <;> simp [doubleInstructions, RowInstruction.writtenKey, outputKeys]

private lemma batch_record_read_other (spec : ModulusSpec width) (count : Nat)
    (fits : count < 2 ^ window) (environment : model.Environment)
    {shape : CShape} (observed : CInputRef ctx shape)
    (free : ∀ key ∈ frame.outputKeys, key ∉ observed.storageKeys)
    (before : Store ctx × model.HiddenState) :
    (frame.batch.valueRecord spec count fits environment before).1.1.read observed =
      before.1.read observed :=
  frame.batch.valueRecord_read_other spec environment count fits observed
    (free _ (by simp [outputKeys, batch]))
    (free _ (by simp [outputKeys, batch]))
    (free _ (by simp [outputKeys, batch]))
    (free _ (by simp [outputKeys, batch]))
    (free _ (by simp [outputKeys, batch])) before

private lemma denominators_record_read_other (level : Fin window)
    (environment : model.Environment) {shape : CShape} (observed : CInputRef ctx shape)
    (free : ∀ key ∈ frame.outputKeys, key ∉ observed.storageKeys)
    (before : Store ctx × model.HiddenState) :
    (frame.layerDenominatorsRecord level environment before).1.1.read observed =
      before.1.read observed :=
  frame.layerDenominatorsRecord_read_other level environment before observed
    (free _ (by simp [outputKeys]))
    (free _ (by simp [outputKeys]))

private lemma extensions_record_read_other (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) {shape : CShape} (observed : CInputRef ctx shape)
    (free : ∀ key ∈ frame.outputKeys, key ∉ observed.storageKeys)
    (before : Store ctx × model.HiddenState) :
    (frame.layerExtensionsRecord spec level environment before).1.1.read observed =
      before.1.read observed := by
  apply range_record_read_other
  intro index current
  apply RowInstruction.rangeRecord_read_other
  intro slot
  apply free
  fin_cases slot <;> simp [extendInstructions, RowInstruction.writtenKey, outputKeys]

private lemma layer_record_read_other (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) {shape : CShape} (observed : CInputRef ctx shape)
    (free : ∀ key ∈ frame.outputKeys, key ∉ observed.storageKeys)
    (before : Store ctx × model.HiddenState) :
    (frame.layerRecord spec level environment before).1.1.read observed =
      before.1.read observed := by
  unfold layerRecord
  apply sequence_record_read_other
  · exact frame.seed_record_read_other spec level environment observed free
  · apply sequence_record_read_other
    · exact frame.denominators_record_read_other level environment observed free
    · apply sequence_record_read_other
      · exact frame.batch_record_read_other spec (layerCount level) (layerFits level)
          environment observed free
      · exact frame.extensions_record_read_other spec level environment observed free

private lemma layers_record_read_other (spec : ModulusSpec width)
    (environment : model.Environment) {shape : CShape} (observed : CInputRef ctx shape)
    (free : ∀ key ∈ frame.outputKeys, key ∉ observed.storageKeys)
    (before : Store ctx × model.HiddenState) :
    (frame.coordinateLayersRecord spec environment before).1.1.read observed =
      before.1.read observed :=
  range_record_read_other _ _ _ observed
    (fun level => frame.layer_record_read_other spec level environment observed free) before

private lemma final_denominators_read_other (spec : ModulusSpec width)
    (environment : model.Environment) {shape : CShape} (observed : CInputRef ctx shape)
    (free : ∀ key ∈ frame.outputKeys, key ∉ observed.storageKeys)
    (before : Store ctx × model.HiddenState) :
    (frame.finalDenominatorsRecord spec environment before).1.1.read observed =
      before.1.read observed := by
  apply range_record_read_other
  intro index current
  apply RowInstruction.rangeRecord_read_other
  intro slot
  apply free
  fin_cases slot <;> simp [tangentInstructions, RowInstruction.writtenKey, outputKeys]

private lemma finish_rows_read_other (spec : ModulusSpec width)
    (environment : model.Environment) {shape : CShape} (observed : CInputRef ctx shape)
    (free : ∀ key ∈ frame.outputKeys, key ∉ observed.storageKeys)
    (before : Store ctx × model.HiddenState) :
    (frame.finishRowsRecord spec environment before).1.1.read observed =
      before.1.read observed := by
  apply range_record_read_other
  intro index current
  apply RowInstruction.rangeRecord_read_other
  intro slot
  apply free
  fin_cases slot <;> simp [finishInstructions, RowInstruction.writtenKey, outputKeys]

private lemma clear_identity_read_other (row : Fin (2 ^ window))
    {shape : CShape} (observed : CInputRef ctx shape)
    (free : ∀ key ∈ frame.outputKeys, key ∉ observed.storageKeys)
    (before : Store ctx × model.HiddenState) :
    (frame.clearIdentityRecord (model := model) row before).1.1.read observed =
      before.1.read observed := by
  apply range_record_read_other
  intro column current
  rw [frame.clearIdentityStep_store]
  apply Store.read_applyOp_of_not_mem_storageKeys
  apply free
  change (frame.arrays.column column).key ∈ frame.outputKeys
  fin_cases column <;> simp [Arrays.column, outputKeys]

/-- Every structurally separate read survives the complete actual five-table record. -/
lemma circuitRecord_read_other (spec : ModulusSpec width) (environment : model.Environment)
    {shape : CShape} (observed : CInputRef ctx shape)
    (free : ∀ key ∈ frame.outputKeys, key ∉ observed.storageKeys)
    (before : Store ctx × model.HiddenState) :
    (frame.circuitRecord spec environment before).1.1.read observed =
      before.1.read observed := by
  unfold circuitRecord
  apply sequence_record_read_other
  · exact frame.layers_record_read_other spec environment observed free
  · apply sequence_record_read_other
    · exact frame.final_denominators_read_other spec environment observed free
    · apply sequence_record_read_other
      · exact frame.batch_record_read_other spec (2 ^ window - 1) finalBatchFits
          environment observed free
      · apply sequence_record_read_other
        · exact frame.finish_rows_read_other spec environment observed free
        · exact frame.clear_identity_read_other _ observed free

end TableFrame

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
