/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Circuit
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Accounting

/-!
# Paid prefix/XGCD/reverse batch event bound

Each real forward row pays one existing-array write and one three-operation
multiply. Each reverse row pays two such multiplies and one real overwrite.
A nonempty batch additionally pays one initialization and one actual total
coefficient computation. An empty batch executes the actual identity.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular
open scoped BigOperators

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : BatchFrame ctx width length)

/-- Four actual native instructions in the prefix step, including its true D-row overwrite. -/
lemma forwardStep_eventCount (index : Fin length)
    (path : (frame.forwardStep (model := model) index).Path) :
    ((frame.forwardStep (model := model) index).eventTrace path).length = 4 := by
  dsimp only [forwardStep, Circuit.Path] at path
  change List.length (_ ++ _) = 4
  rw [List.length_append, Accounting.instruction_eventCount, Accounting.multiply_eventCount]

/-- Every reverse row pays two original multiplies before replacing the original denominator. -/
lemma reverseStep_eventCount (index : Fin length)
    (path : (frame.reverseStep (model := model) index).Path) :
    ((frame.reverseStep (model := model) index).eventTrace path).length = 7 := by
  dsimp only [reverseStep, Circuit.Path] at path
  change List.length (_ ++ (_ ++ _)) = 7
  rw [List.length_append, List.length_append, Accounting.multiply_eventCount,
    Accounting.multiply_eventCount, Accounting.instruction_eventCount]

/-- The increasing pass pays exactly four instructions for every original nonzero row. -/
lemma forwardPass_eventCount_le (count : Nat) (fits : count < length)
    (path : (frame.forwardPass (model := model) count fits).Path) :
    ((frame.forwardPass (model := model) count fits).eventTrace path).length ≤ 4 * count := by
  calc
    _ ≤ ∑ _index : Fin count, 4 := Accounting.range_eventCount_le count _ _
      (fun index selected => (frame.forwardStep_eventCount _ selected).le) path
    _ = 4 * count := by simp [Nat.mul_comm]

/-- The decreasing pass pays exactly seven instructions for every original nonzero row. -/
lemma reversePass_eventCount_le (count : Nat) (fits : count < length)
    (path : (frame.reversePass (model := model) count fits).Path) :
    ((frame.reversePass (model := model) count fits).eventTrace path).length ≤ 7 * count := by
  calc
    _ ≤ ∑ _index : Fin count, 7 := Accounting.range_eventCount_le count _ _
      (fun index selected => (frame.reverseStep_eventCount _ selected).le) path
    _ = 7 * count := by simp [Nat.mul_comm]

/-- Independent instruction ceiling with the true empty-batch identity branch. -/
def eventBudget (width count : Nat) : Nat :=
  if count = 0 then 0 else 11 * count + 30 * width + 71

/-- The complete actual batch pays its real initializer, both passes and total XGCD coefficient. -/
lemma circuit_eventCount_le (spec : ModulusSpec width) (count : Nat) (fits : count < length) :
    ∀ path : (frame.circuit (model := model) spec count fits).Path,
      ((frame.circuit (model := model) spec count fits).eventTrace path).length ≤
        eventBudget width count := by
  unfold circuit eventBudget
  by_cases empty : count = 0
  · rw [if_pos empty, if_pos empty]
    intro path
    exact Nat.le_refl _
  · rw [if_neg empty, if_neg empty]
    intro path
    have initialized := Accounting.instruction_eventCount
      (model := model) (ClassicalOp.wordResize width width ctx frame.one frame.work.product)
      path.1
    have forward := frame.forwardPass_eventCount_le count fits path.2.1
    have inverted := Accounting.coefficient_eventCount_le spec
      (wordRead frame.work.product) frame.work.inverse path.2.2.1
    have backward := frame.reversePass_eventCount_le count fits path.2.2.2
    change List.length (_ ++ (_ ++ (_ ++ _))) ≤ _
    simp only [List.length_append]
    omega

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
