/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Finish.Last
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.Columns

/-!
# Exact input reads at the two real final-row block boundaries

The first two blocks preserve the original coordinate row, widened modulus
and supplied zero/one values. These read equalities keep all later finite
word expressions attached to the original Store while sharing small actual
intermediate blocks in the proof.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- Exact original input values at a real intermediate Store of the final row. -/
structure FinishInputReads (frame : TableFrame ctx width length) (row : Fin length)
    (original current : Store ctx) : Prop where
  modulus : current.read (wordRead frame.modulus) = original.read (wordRead frame.modulus)
  x : current.read (rowRead frame.arrays.x row) = original.read (rowRead frame.arrays.x row)
  y : current.read (rowRead frame.arrays.y row) = original.read (rowRead frame.arrays.y row)
  zero : current.read frame.zero = original.read frame.zero
  one : current.read frame.one = original.read frame.one

variable (frame : TableFrame ctx width length)

private lemma scalar_modulus_free (word : CWriteRef ctx (.unsignedWord width)) :
    word.key ∉ (wordRead frame.modulus).storageKeys := by
  change word.key ∉ [frame.modulus.key]
  simpa only [List.mem_singleton] using Ne.symm (modulus_word_key_ne frame.modulus word)

private lemma scalar_row_free (word : CWriteRef ctx (.unsignedWord width))
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width))) (row : Fin length) :
    word.key ∉ (rowRead array row).storageKeys := by
  change word.key ∉ [array.key]
  simpa only [List.mem_singleton] using word_array_key_ne word array

private lemma array_modulus_free
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width))) :
    array.key ∉ (wordRead frame.modulus).storageKeys := by
  change array.key ∉ [frame.modulus.key]
  simpa only [List.mem_singleton] using Ne.symm (modulus_array_key_ne frame.modulus array)

private lemma array_row_free
    (written observed : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : written.key ≠ observed.key) :
    written.key ∉ (rowRead observed row).storageKeys := by
  change written.key ∉ [observed.key]
  simpa only [List.mem_singleton] using different

/-- The first five actual scalar updates retain every original input needed by the later blocks. -/
lemma finishFirstStore_inputReads (spec : ModulusSpec width) (row : Fin length)
    (store : Store ctx) :
    FinishInputReads frame row store (frame.finishFirstStore spec row store) := by
  constructor
  · exact frame.finishFirstStore_read_other spec row store _
      (frame.scalar_modulus_free _) (frame.scalar_modulus_free _) (frame.scalar_modulus_free _)
  · exact frame.finishFirstStore_read_other spec row store _
      (scalar_row_free _ _ _) (scalar_row_free _ _ _) (scalar_row_free _ _ _)
  · exact frame.finishFirstStore_read_other spec row store _
      (scalar_row_free _ _ _) (scalar_row_free _ _ _) (scalar_row_free _ _ _)
  · apply frame.finishFirstStore_read_other
    all_goals exact frame.outputKey_free _ (by simp [outputKeys]) frame.zero (by simp)
  · apply frame.finishFirstStore_read_other
    all_goals exact frame.outputKey_free _ (by simp [outputKeys]) frame.one (by simp)

/-- The middle five real updates retain the same original-coordinate and constant inputs. -/
lemma finishMiddleStore_inputReads (spec : ModulusSpec width) (row : Fin length)
    (store : Store ctx) :
    FinishInputReads frame row store (frame.finishMiddleStore spec row store) := by
  constructor
  · exact frame.finishMiddleStore_read_other spec row store _
      (frame.array_modulus_free _) (frame.array_modulus_free _) (frame.scalar_modulus_free _)
  · exact frame.finishMiddleStore_read_other spec row store _
      (array_row_free _ _ _ (frame.arrays.column_key_ne 3 0 (by decide)))
      (array_row_free _ _ _ (frame.arrays.column_key_ne 2 0 (by decide)))
      (scalar_row_free _ _ _)
  · exact frame.finishMiddleStore_read_other spec row store _
      (array_row_free _ _ _ (frame.arrays.column_key_ne 3 1 (by decide)))
      (array_row_free _ _ _ (frame.arrays.column_key_ne 2 1 (by decide)))
      (scalar_row_free _ _ _)
  · apply frame.finishMiddleStore_read_other
    all_goals exact frame.outputKey_free _ (by simp [outputKeys]) frame.zero (by simp)
  · apply frame.finishMiddleStore_read_other
    all_goals exact frame.outputKey_free _ (by simp [outputKeys]) frame.one (by simp)

/-- Exact original-input observations compose on their true shared intermediate Store. -/
lemma FinishInputReads.trans (row : Fin length) (original middle final : Store ctx)
    (first : FinishInputReads frame row original middle)
    (second : FinishInputReads frame row middle final) :
    FinishInputReads frame row original final :=
  ⟨second.modulus.trans first.modulus, second.x.trans first.x, second.y.trans first.y,
    second.zero.trans first.zero, second.one.trans first.one⟩

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
