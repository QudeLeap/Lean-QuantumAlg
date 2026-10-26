/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Blocks
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Read
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.Work

/-!
# Exact original doubling inputs at the real scalar block boundaries

The actual scalar writes retain both original coordinate arrays, the
stored widened modulus and the supplied curve coefficient. These laws
hold before either destination write, including in-place doubling.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- Original actual input reads at a scalar-block boundary of the doubling program. -/
structure InputReads (frame : CoordinateFrame ctx width length) (source : Fin length)
    (original current : Store ctx) : Prop where
  modulus : current.read (wordRead frame.modulus) = original.read (wordRead frame.modulus)
  x : current.read (rowRead frame.x source) = original.read (rowRead frame.x source)
  y : current.read (rowRead frame.y source) = original.read (rowRead frame.y source)
  curveA : current.read frame.curveA = original.read frame.curveA

variable (frame : CoordinateFrame ctx width length)

private lemma scalar_modulus_free (word : CWriteRef ctx (.unsignedWord width)) :
    word.key ∉ (wordRead frame.modulus).storageKeys := by
  change word.key ∉ [frame.modulus.key]
  simpa only [List.mem_singleton] using Ne.symm (modulus_word_key_ne frame.modulus word)

private lemma scalar_row_free (word : CWriteRef ctx (.unsignedWord width))
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width))) (row : Fin length) :
    word.key ∉ (rowRead array row).storageKeys := by
  change word.key ∉ [array.key]
  simpa only [List.mem_singleton] using word_array_key_ne word array

/-- Each actual scalar write preserves the originally supplied curve coefficient. -/
lemma write_read_curveA (index : Fin 4) (store : Store ctx) (value : CShape.Word width) :
    (store.write (frame.work.word index) value).read frame.curveA = store.read frame.curveA := by
  apply Store.read_write_of_not_mem_storageKeys
  apply frame.protectedCoefficient
  fin_cases index <;> simp [Work.word]

/-- The first seven actual scalar slots retain every original input of the doubling formulas. -/
lemma slopeStore_inputReads (spec : ModulusSpec width) (source : Fin length) (store : Store ctx) :
    InputReads frame source store (frame.slopeStore spec source store) := by
  constructor
  · exact frame.slopeStore_read_other spec source store _
      (frame.scalar_modulus_free _) (frame.scalar_modulus_free _)
      (frame.scalar_modulus_free _) (frame.scalar_modulus_free _)
  · exact frame.slopeStore_read_other spec source store _
      (scalar_row_free _ _ _) (scalar_row_free _ _ _)
      (scalar_row_free _ _ _) (scalar_row_free _ _ _)
  · exact frame.slopeStore_read_other spec source store _
      (scalar_row_free _ _ _) (scalar_row_free _ _ _)
      (scalar_row_free _ _ _) (scalar_row_free _ _ _)
  · apply frame.slopeStore_read_other
    all_goals exact frame.protectedCoefficient _ (by simp)

/-- The six actual scalar result slots retain the same original coordinate and constant reads. -/
lemma resultStore_inputReads (spec : ModulusSpec width) (source : Fin length) (store : Store ctx) :
    InputReads frame source store (frame.resultStore spec source store) := by
  constructor
  · exact frame.resultStore_read_other spec source store _
      (frame.scalar_modulus_free _) (frame.scalar_modulus_free _)
  · exact frame.resultStore_read_other spec source store _
      (scalar_row_free _ _ _) (scalar_row_free _ _ _)
  · exact frame.resultStore_read_other spec source store _
      (scalar_row_free _ _ _) (scalar_row_free _ _ _)
  · apply frame.resultStore_read_other
    all_goals exact frame.protectedCoefficient _ (by simp)

/-- Exact input readback composes only on its shared actual intermediate Store. -/
lemma InputReads.trans (source : Fin length) (original middle final : Store ctx)
    (first : InputReads frame source original middle)
    (second : InputReads frame source middle final) : InputReads frame source original final :=
  ⟨second.modulus.trans first.modulus, second.x.trans first.x, second.y.trans first.y,
    second.curveA.trans first.curveA⟩

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
