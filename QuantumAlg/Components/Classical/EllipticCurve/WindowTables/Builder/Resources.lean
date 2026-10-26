/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Accounting

/-!
# Actual row-program event ceilings for the five arrays

Each statement counts the full selected path of the actual row circuit,
including lexical arithmetic scratch and actual coefficient inversion.
The doubling writes directly into its existing seed row, so it needs no
additional persistent point tuple or redundant pair of coordinate copies.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution ClassicalAlgorithms.Modular
open scoped BigOperators

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- The first seed pays its two actual existing-array writes. -/
lemma seedRow_eventCount (index : Fin length)
    (path : (frame.seedRow (model := model) index).Path) :
    ((frame.seedRow (model := model) index).eventTrace path).length = 2 := by
  dsimp only [seedRow, Circuit.Path] at path
  change List.length (_ ++ _) = 2
  rw [List.length_append, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Shared-modulus doubling pays its actual coefficient and all fifty-seven other operations. -/
lemma doubleRow_eventCount_le (spec : ModulusSpec width) (source destination : Fin length)
    (path : (frame.doubleRow (model := model) spec source destination).Path) :
    ((frame.doubleRow (model := model) spec source destination).eventTrace path).length ≤
      30 * width + 127 := by
  dsimp only [doubleRow] at path ⊢
  calc
    _ ≤ ∑ index : Fin 15,
        (![5, 30 * width + 70, 3, 5, 5, 5, 3, 5, 3, 6, 6, 3, 6, 1, 1] : Fin 15 → Nat)
          index := by
      apply Accounting.range_eventCount_le
      intro index selected
      fin_cases index <;> first
        | exact (Field.Native.Shared.sharedAddIntoWord_eventCount _ _ _ _ selected).le
        | exact Accounting.coefficient_eventCount_le spec _ _ selected
        | exact (Accounting.multiply_eventCount _ _ _ _ selected).le
        | exact (Field.Native.Shared.sharedSubIntoWord_eventCount _ _ _ _ selected).le
        | exact (Accounting.instruction_eventCount _ selected).le
    _ = 30 * width + 127 := by simp [Fin.sum_univ_succ]; omega

/-- An actual subtraction and existing-array write pay seven native operations. -/
lemma denominatorRow_eventCount (seed row : Fin length)
    (path : (frame.denominatorRow (model := model) seed row).Path) :
    ((frame.denominatorRow (model := model) seed row).eventTrace path).length = 7 := by
  dsimp only [denominatorRow, Circuit.Path] at path
  change List.length (_ ++ _) = 7
  rw [List.length_append, Field.Native.Shared.sharedSubIntoWord_eventTrace,
    BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The nonseed affine addition uses exactly the actual forty-one native instructions. -/
lemma extendRow_eventCount_le (seed row destination : Fin length)
    (path : (frame.extendRow (model := model) seed row destination).Path) :
    ((frame.extendRow (model := model) seed row destination).eventTrace path).length ≤ 41 := by
  dsimp only [extendRow] at path ⊢
  calc
    _ ≤ ∑ index : Fin 10, (![6, 3, 3, 6, 6, 6, 3, 6, 1, 1] : Fin 10 → Nat) index := by
      apply Accounting.range_eventCount_le
      intro index selected
      fin_cases index <;> first
        | exact (Accounting.multiply_eventCount _ _ _ _ selected).le
        | exact (Field.Native.Shared.sharedSubIntoWord_eventCount _ _ _ _ selected).le
        | exact (Accounting.instruction_eventCount _ selected).le
    _ = 41 := by norm_num [Fin.sum_univ_succ]

/-- The original negative tangent denominator pays add, subtract and row write. -/
lemma tangentDenominatorRow_eventCount_le (row : Fin length)
    (path : (frame.tangentDenominatorRow (model := model) row).Path) :
    ((frame.tangentDenominatorRow (model := model) row).eventTrace path).length ≤ 12 := by
  dsimp only [tangentDenominatorRow] at path ⊢
  calc
    _ ≤ ∑ index : Fin 3, (![5, 6, 1] : Fin 3 → Nat) index := by
      apply Accounting.range_eventCount_le
      intro index selected
      fin_cases index <;> first
        | exact (Field.Native.Shared.sharedAddIntoWord_eventCount _ _ _ _ selected).le
        | exact (Field.Native.Shared.sharedSubIntoWord_eventCount _ _ _ _ selected).le
        | exact (Accounting.instruction_eventCount _ selected).le
    _ = 12 := by norm_num [Fin.sum_univ_succ]

/-- All five final columns, including the exceptional slope and x+1, are actually written. -/
lemma finishRow_eventCount_le (row : Fin length)
    (path : (frame.finishRow (model := model) row).Path) :
    ((frame.finishRow (model := model) row).eventTrace path).length ≤ 53 := by
  dsimp only [finishRow] at path ⊢
  calc
    _ ≤ ∑ index : Fin 15,
        (![3, 5, 5, 5, 3, 1, 5, 5, 1, 5, 1, 6, 1, 6, 1] : Fin 15 → Nat) index := by
      apply Accounting.range_eventCount_le
      intro index selected
      fin_cases index <;> first
        | exact (Field.Native.Shared.sharedAddIntoWord_eventCount _ _ _ _ selected).le
        | exact (Accounting.multiply_eventCount _ _ _ _ selected).le
        | exact (Field.Native.Shared.sharedSubIntoWord_eventCount _ _ _ _ selected).le
        | exact (Accounting.instruction_eventCount _ selected).le
    _ = 53 := by norm_num [Fin.sum_univ_succ]

/-- Row zero is really overwritten in every array; none of its five entries is implicit. -/
lemma clearIdentityRow_eventCount_le (row : Fin length)
    (path : (frame.clearIdentityRow (model := model) row).Path) :
    ((frame.clearIdentityRow (model := model) row).eventTrace path).length ≤ 5 := by
  dsimp only [clearIdentityRow] at path ⊢
  calc
    _ ≤ ∑ _index : Fin 5, 1 := by
      apply Accounting.range_eventCount_le
      intro index selected
      fin_cases index <;> exact (Accounting.instruction_eventCount _ selected).le
    _ = 5 := by norm_num

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
