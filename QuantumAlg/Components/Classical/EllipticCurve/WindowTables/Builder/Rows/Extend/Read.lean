/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Extend.X

/-!
# Original coordinate inputs at the actual secant scalar boundaries

Both the seed and earlier coordinate row retain their exact original
values through the first five scalar slots. The widened actual modulus
is preserved by their typed storage shapes, including operand aliases.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- Actual original coordinate and modulus reads at one secant scalar-block boundary. -/
structure ExtendInputReads (frame : TableFrame ctx width length) (seed row : Fin length)
    (original current : Store ctx) : Prop where
  modulus : current.read (wordRead frame.modulus) = original.read (wordRead frame.modulus)
  x : current.read (rowRead frame.arrays.x row) = original.read (rowRead frame.arrays.x row)
  y : current.read (rowRead frame.arrays.y row) = original.read (rowRead frame.arrays.y row)
  baseX : current.read (rowRead frame.arrays.x seed) = original.read (rowRead frame.arrays.x seed)
  baseY : current.read (rowRead frame.arrays.y seed) = original.read (rowRead frame.arrays.y seed)

private lemma word_modulus_free (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (word : CWriteRef ctx (.unsignedWord width)) : word.key ∉ (wordRead modulus).storageKeys := by
  change word.key ∉ [modulus.key]
  simpa only [List.mem_singleton] using Ne.symm (modulus_word_key_ne modulus word)

private lemma word_row_free (word : CWriteRef ctx (.unsignedWord width))
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width))) (row : Fin length) :
    word.key ∉ (rowRead array row).storageKeys := by
  change word.key ∉ [array.key]
  simpa only [List.mem_singleton] using word_array_key_ne word array

variable (frame : TableFrame ctx width length)

/-- Both actual slope-prefix outputs retain every original coordinate input. -/
lemma extendFirstStore_inputReads (spec : ModulusSpec width) (seed row : Fin length)
    (store : Store ctx) :
    ExtendInputReads frame seed row store (frame.extendFirstStore spec seed row store) := by
  constructor
  · exact frame.extendFirstStore_read_other spec seed row store _
      (word_modulus_free _ _) (word_modulus_free _ _)
  all_goals
    exact frame.extendFirstStore_read_other spec seed row store _
      (word_row_free _ _ _) (word_row_free _ _ _)

/-- The three real temporary overwrites retain those same original coordinate inputs. -/
lemma extendXStore_inputReads (spec : ModulusSpec width) (seed row : Fin length)
    (store : Store ctx) :
    ExtendInputReads frame seed row store (frame.extendXStore spec seed row store) := by
  constructor
  · exact frame.extendXStore_read_other spec seed row store _ (word_modulus_free _ _)
  all_goals exact frame.extendXStore_read_other spec seed row store _ (word_row_free _ _ _)

/-- Exact original-input observations compose on the one actual intermediate Store. -/
lemma ExtendInputReads.trans (seed row : Fin length) (original middle final : Store ctx)
    (first : ExtendInputReads frame seed row original middle)
    (second : ExtendInputReads frame seed row middle final) :
    ExtendInputReads frame seed row original final :=
  ⟨second.modulus.trans first.modulus, second.x.trans first.x, second.y.trans first.y,
    second.baseX.trans first.baseX, second.baseY.trans first.baseY⟩

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
