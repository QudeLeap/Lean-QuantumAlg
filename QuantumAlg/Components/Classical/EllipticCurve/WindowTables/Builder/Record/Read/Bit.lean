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

/-!
# Retained caller Boolean flags throughout the actual table builder

Every original output is an unsigned word or an array of unsigned words.
A live Boolean storage cell has a different shape and therefore a
different key. Symbolic chronological-record induction retains its value
through every real slot, batch and layer. The actual returned hidden state
and every original Path remain unchanged in the record being observed.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open Execution ClassicalAlgorithms.Modular

noncomputable section

private lemma word_bit_free {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (word : CWriteRef ctx (.unsignedWord width)) (observed : CStorageRef ctx .bit) :
    word.key ∉ (CInputRef.storage observed).storageKeys := by
  change word.key ∉ [observed.key]
  simp only [List.mem_singleton]
  intro same
  have shapes := CStorageRef.storageRef_shape_eq_of_key word.toCStorageRef observed same
  cases shapes

private lemma array_bit_free {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width length : Nat} (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (observed : CStorageRef ctx .bit) :
    array.key ∉ (CInputRef.storage observed).storageKeys := by
  change array.key ∉ [observed.key]
  simp only [List.mem_singleton]
  intro same
  have shapes := CStorageRef.storageRef_shape_eq_of_key array.toCStorageRef observed same
  cases shapes

private lemma row_record_read_bit {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width length : Nat} (spec : ModulusSpec width)
    (modulus : CWriteRef ctx (.unsignedWord (width + 1))) (environment : model.Environment)
    (count : Nat) (instructions : Fin count → RowInstruction ctx width length)
    (before : Store ctx × model.HiddenState) (observed : CStorageRef ctx .bit) :
    (RowInstruction.rangeRecord spec modulus environment count instructions before).1.1.read
      (.storage observed) = before.1.read (.storage observed) := by
  apply RowInstruction.rangeRecord_read_other
  intro index
  cases instructions index <;>
    first | exact word_bit_free _ observed | exact array_bit_free _ observed

private lemma sequence_record_read_bit {model : ExecutionModel}
    {ctx : RuntimeCtx model.kind} {allocation : Bool}
    (first last : Circuit model ctx ctx allocation)
    (head : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × first.Path)
    (tail : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × last.Path)
    (observed : CStorageRef ctx .bit)
    (headRead : ∀ before, (head before).1.1.read (.storage observed) =
      before.1.read (.storage observed))
    (tailRead : ∀ before, (tail before).1.1.read (.storage observed) =
      before.1.read (.storage observed))
    (before : Store ctx × model.HiddenState) :
    (Circuit.sequenceRecord first last head tail before).1.1.read (.storage observed) =
      before.1.read (.storage observed) :=
  (tailRead (head before).1).trans (headRead before)

private lemma range_record_read_bit {model : ExecutionModel}
    {ctx : RuntimeCtx model.kind} (count : Nat) (body : Fin count → Circuit model ctx ctx)
    (records : ∀ index, Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (body index).Path)
    (observed : CStorageRef ctx .bit)
    (stepRead : ∀ index before, (records index before).1.1.read (.storage observed) =
      before.1.read (.storage observed)) (before : Store ctx × model.HiddenState) :
    (Circuit.forRangeRecord count body records before).1.1.read (.storage observed) =
      before.1.read (.storage observed) :=
  Circuit.forRangeRecord_invariant count body records
    (fun _ current => current.1.read (.storage observed) = before.1.read (.storage observed))
    (fun index current established => (stepRead index current).trans established) before rfl

namespace TableFrame

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

private lemma seed_record_read_bit (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) (observed : CStorageRef ctx .bit)
    (before : Store ctx × model.HiddenState) :
    (frame.prepareSeedRecord spec level environment before).1.1.read (.storage observed) =
      before.1.read (.storage observed) := by
  rcases level with ⟨level, bound⟩
  cases level with
  | zero =>
      exact frame.coordinates.seedRecord_read_other frame.baseX frame.baseY
        (layerSeed window ⟨0, bound⟩) before (.storage observed)
        (array_bit_free _ observed) (array_bit_free _ observed)
  | succ level =>
      exact row_record_read_bit spec frame.modulus environment 15
        (frame.doubleInstructions (previousSeed window ⟨level + 1, bound⟩)
          (layerSeed window ⟨level + 1, bound⟩)) before observed

private lemma batch_record_read_bit (spec : ModulusSpec width) (count : Nat)
    (fits : count < 2 ^ window) (environment : model.Environment)
    (observed : CStorageRef ctx .bit) (before : Store ctx × model.HiddenState) :
    (frame.batch.valueRecord spec count fits environment before).1.1.read (.storage observed) =
      before.1.read (.storage observed) :=
  frame.batch.valueRecord_read_other spec environment count fits (.storage observed)
    (array_bit_free _ observed) (word_bit_free _ observed)
    (array_bit_free _ observed) (word_bit_free _ observed)
    (word_bit_free _ observed) before

private lemma denominators_record_read_bit (level : Fin window)
    (environment : model.Environment) (observed : CStorageRef ctx .bit)
    (before : Store ctx × model.HiddenState) :
    (frame.layerDenominatorsRecord level environment before).1.1.read (.storage observed) =
      before.1.read (.storage observed) :=
  frame.layerDenominatorsRecord_read_other level environment before (.storage observed)
    (word_bit_free _ observed) (array_bit_free _ observed)

private lemma extensions_record_read_bit (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) (observed : CStorageRef ctx .bit)
    (before : Store ctx × model.HiddenState) :
    (frame.layerExtensionsRecord spec level environment before).1.1.read (.storage observed) =
      before.1.read (.storage observed) := by
  apply range_record_read_bit
  intro index current
  exact row_record_read_bit spec frame.modulus environment 10
    (frame.extendInstructions (layerSeed window level) (oldRow level index) (newRow level index))
    current observed

private lemma layer_record_read_bit (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) (observed : CStorageRef ctx .bit)
    (before : Store ctx × model.HiddenState) :
    (frame.layerRecord spec level environment before).1.1.read (.storage observed) =
      before.1.read (.storage observed) := by
  unfold layerRecord
  apply sequence_record_read_bit
  · exact frame.seed_record_read_bit spec level environment observed
  · apply sequence_record_read_bit
    · exact frame.denominators_record_read_bit level environment observed
    · apply sequence_record_read_bit
      · exact frame.batch_record_read_bit spec (layerCount level) (layerFits level)
          environment observed
      · exact frame.extensions_record_read_bit spec level environment observed

private lemma layers_record_read_bit (spec : ModulusSpec width)
    (environment : model.Environment) (observed : CStorageRef ctx .bit)
    (before : Store ctx × model.HiddenState) :
    (frame.coordinateLayersRecord spec environment before).1.1.read (.storage observed) =
      before.1.read (.storage observed) :=
  range_record_read_bit _ _ _ observed
    (fun level => frame.layer_record_read_bit spec level environment observed) before

private lemma final_denominators_read_bit (spec : ModulusSpec width)
    (environment : model.Environment) (observed : CStorageRef ctx .bit)
    (before : Store ctx × model.HiddenState) :
    (frame.finalDenominatorsRecord spec environment before).1.1.read (.storage observed) =
      before.1.read (.storage observed) := by
  apply range_record_read_bit
  intro index current
  exact row_record_read_bit spec frame.modulus environment 3
    (frame.tangentInstructions (nonzeroRow window index)) current observed

private lemma finish_rows_read_bit (spec : ModulusSpec width)
    (environment : model.Environment) (observed : CStorageRef ctx .bit)
    (before : Store ctx × model.HiddenState) :
    (frame.finishRowsRecord spec environment before).1.1.read (.storage observed) =
      before.1.read (.storage observed) := by
  apply range_record_read_bit
  intro index current
  exact row_record_read_bit spec frame.modulus environment 15
    (frame.finishInstructions (nonzeroRow window index)) current observed

private lemma clear_identity_read_bit (row : Fin (2 ^ window))
    (observed : CStorageRef ctx .bit) (before : Store ctx × model.HiddenState) :
    (frame.clearIdentityRecord (model := model) row before).1.1.read (.storage observed) =
      before.1.read (.storage observed) := by
  apply range_record_read_bit
  intro column current
  rw [frame.clearIdentityStep_store]
  exact Store.read_applyOp_of_not_mem_storageKeys _ _ (.storage observed)
    (array_bit_free _ observed)

/-- Every original Boolean caller cell survives the complete actual five-table record. -/
lemma circuitRecord_read_bit (spec : ModulusSpec width) (environment : model.Environment)
    (observed : CStorageRef ctx .bit) (before : Store ctx × model.HiddenState) :
    (frame.circuitRecord spec environment before).1.1.read (.storage observed) =
      before.1.read (.storage observed) := by
  unfold circuitRecord
  apply sequence_record_read_bit
  · exact frame.layers_record_read_bit spec environment observed
  · apply sequence_record_read_bit
    · exact frame.final_denominators_read_bit spec environment observed
    · apply sequence_record_read_bit
      · exact frame.batch_record_read_bit spec (2 ^ window - 1) finalBatchFits
          environment observed
      · apply sequence_record_read_bit
        · exact frame.finish_rows_read_bit spec environment observed
        · exact frame.clear_identity_read_bit _ observed

end TableFrame

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
