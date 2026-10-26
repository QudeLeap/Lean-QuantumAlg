/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Protection
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Framing
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Instructions
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Denominator
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Total

/-!
# Original loaded inputs throughout the actual table construction

The actual modulus and five protected structural input words retain their
original readings through the real row programs and the complete total
batch. These are exact returned-Store equalities, including the true empty
batch. No new input promise is attached to the circuit constructor.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- The actual loaded modulus and the five original protected input readings agree. -/
structure OriginalInputs (frame : TableFrame ctx width length)
    (before after : Store ctx) : Prop where
  modulus : after.read (wordRead frame.modulus) = before.read (wordRead frame.modulus)
  inputs : ∀ input ∈ [frame.zero, frame.one, frame.curveA, frame.baseX, frame.baseY],
    after.read input = before.read input

/-- The original Store agrees with itself, with no assumption on old scratch words. -/
lemma OriginalInputs.refl (frame : TableFrame ctx width length) (store : Store ctx) :
    OriginalInputs frame store store := ⟨rfl, fun _ _ => rfl⟩

/-- Exact actual input agreements compose through the same intermediate Store. -/
lemma OriginalInputs.trans (frame : TableFrame ctx width length) (first middle last : Store ctx)
    (head : OriginalInputs frame first middle) (tail : OriginalInputs frame middle last) :
    OriginalInputs frame first last :=
  ⟨tail.modulus.trans head.modulus, fun input member =>
    (tail.inputs input member).trans (head.inputs input member)⟩

variable (frame : TableFrame ctx width length)

/-- Each of the nine actual original output cells avoids the separately widened modulus cell. -/
lemma outputKey_modulus_free (key : StorageKey) (inside : key ∈ frame.outputKeys) :
    key ∉ (wordRead frame.modulus).storageKeys := by
  simp only [outputKeys, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    change _ ∉ [frame.modulus.key]
    first
      | simpa only [List.mem_singleton] using
          Ne.symm (modulus_array_key_ne frame.modulus frame.arrays.x)
      | simpa only [List.mem_singleton] using
          Ne.symm (modulus_array_key_ne frame.modulus frame.arrays.y)
      | simpa only [List.mem_singleton] using
          Ne.symm (modulus_array_key_ne frame.modulus frame.arrays.c)
      | simpa only [List.mem_singleton] using
          Ne.symm (modulus_array_key_ne frame.modulus frame.arrays.d)
      | simpa only [List.mem_singleton] using
          Ne.symm (modulus_array_key_ne frame.modulus frame.arrays.e)
      | simpa only [List.mem_singleton] using
          Ne.symm (modulus_word_key_ne frame.modulus frame.work.product)
      | simpa only [List.mem_singleton] using
          Ne.symm (modulus_word_key_ne frame.modulus frame.work.inverse)
      | simpa only [List.mem_singleton] using
          Ne.symm (modulus_word_key_ne frame.modulus frame.work.temporary)
      | simpa only [List.mem_singleton] using
          Ne.symm (modulus_word_key_ne frame.modulus frame.work.slope)

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : TableFrame ctx width length)

/-- A real original row sequence preserves all loaded inputs whenever its actual outputs belong
to the original frame. -/
lemma rowRecord_originalInputs (spec : ModulusSpec width) (count : Nat)
    (instructions : Fin count → RowInstruction ctx width length) (environment : model.Environment)
    (outputs : ∀ index, (instructions index).writtenKey ∈ frame.outputKeys)
    (before : Store ctx × model.HiddenState) :
    OriginalInputs frame before.1
      (RowInstruction.rangeRecord spec frame.modulus environment count instructions before).1.1 :=
  ⟨RowInstruction.rangeRecord_read_other spec frame.modulus environment count instructions before
      (wordRead frame.modulus) (fun index => frame.outputKey_modulus_free _ (outputs index)),
    fun input member => RowInstruction.rangeRecord_read_other spec frame.modulus environment count
      instructions before input
      (fun index => frame.outputKey_free _ (outputs index) input member)⟩

/-- The same original loaded inputs survive the complete actual total batch,
including count zero. -/
lemma batchRecord_originalInputs (spec : ModulusSpec width) (count : Nat) (fits : count < length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    OriginalInputs frame before.1
      (frame.batch.valueRecord spec count fits environment before).1.1 := by
  refine ⟨?_, ?_⟩
  · apply frame.batch.valueRecord_read_other spec environment count fits
    all_goals exact frame.outputKey_modulus_free _ (by simp [outputKeys, batch])
  · intro input member
    apply frame.batch.valueRecord_read_other spec environment count fits
    all_goals exact frame.outputKey_free _ (by simp [outputKeys, batch]) input member

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
