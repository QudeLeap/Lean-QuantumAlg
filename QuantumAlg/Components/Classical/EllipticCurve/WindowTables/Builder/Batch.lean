/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Inputs
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Total.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Row

/-!
# Original total batch inverse in the actual five-array frame

The original C/D batch retains every coordinate row and writes the inverse
of each original nonzero denominator into that same actual C row. Its
loaded inputs and all returned words are read from the chronological Store.
The genuine zero-count branch remains identity without a scratch promise.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- Every coordinate or other actual array outside C/D survives the original complete batch. -/
lemma batchRecord_read_array_row (spec : ModulusSpec width) (count : Nat) (fits : count < length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width))) (row : Fin length)
    (denominatorFree : frame.arrays.c.key ≠ array.key)
    (prefixFree : frame.arrays.d.key ≠ array.key) :
    (frame.batch.valueRecord spec count fits environment before).1.1.read (rowRead array row) =
      before.1.read (rowRead array row) := by
  apply frame.batch.valueRecord_read_other spec environment count fits
  · change frame.arrays.d.key ∉ [array.key]
    simpa only [List.mem_singleton] using prefixFree
  · change frame.work.product.key ∉ [array.key]
    simpa only [List.mem_singleton] using word_array_key_ne _ _
  · change frame.arrays.c.key ∉ [array.key]
    simpa only [List.mem_singleton] using denominatorFree
  · change frame.work.inverse.key ∉ [array.key]
    simpa only [List.mem_singleton] using word_array_key_ne _ _
  · change frame.work.temporary.key ∉ [array.key]
    simpa only [List.mem_singleton] using word_array_key_ne _ _

/-- Each visited positive row receives the inverse of its actual incoming represented value. -/
lemma batchRecord_denominator_inverse (spec : ModulusSpec width) [Fact spec.modulus.Prime]
    (environment : model.Environment) (count : Nat) (fits : count < length)
    (values : Nat → ZMod spec.modulus) (before : Store ctx × model.HiddenState)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord)
    (one : (before.1.read frame.one).toNat = 1)
    (nonzero : ∀ position < count, values position ≠ 0)
    (represented : ∀ index : Fin length, 1 ≤ index.val → index.val ≤ count →
      ((before.1.read (rowRead frame.arrays.c index)).toNat : ZMod spec.modulus) =
        values (index.val - 1))
    (index : Fin length) (positive : 1 ≤ index.val) (within : index.val ≤ count) :
    ((frame.batch.valueRecord spec count fits environment before).1.1.read
      (rowRead frame.arrays.c index)).toNat = ((values (index.val - 1))⁻¹).val := by
  apply frame.batch.valueRecord_denominator_inverse spec environment count fits
    (frame.outputKey_modulus_free _ (by simp [outputKeys, batch]))
    (frame.outputKey_modulus_free _ (by simp [outputKeys, batch]))
    (frame.outputKey_modulus_free _ (by simp [outputKeys, batch]))
    (frame.outputKey_modulus_free _ (by simp [outputKeys, batch]))
    (frame.outputKey_modulus_free _ (by simp [outputKeys, batch]))
    values before loaded one nonzero represented index positive within

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
