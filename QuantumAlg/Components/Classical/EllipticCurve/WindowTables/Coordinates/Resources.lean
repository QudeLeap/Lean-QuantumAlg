/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Accounting

/-!
# Actual native costs of two-array coordinate doubling

The actual raw XGCD coefficient is paid once. The other fifty-seven native
operations include both final coordinate writes. The bound projects this
same actual circuit and does not assume mathematical inverse access or
three additional arrays.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution ClassicalAlgorithms.Modular
open scoped BigOperators

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : CoordinateFrame ctx width length)

/-- The true slot paths pay their original XGCD envelope and fifty-seven other native operations. -/
lemma doubleCircuit_eventCount_le (spec : ModulusSpec width) (source destination : Fin length)
    (path : (frame.doubleCircuit (model := model) spec source destination).Path) :
    ((frame.doubleCircuit (model := model) spec source destination).eventTrace path).length ≤
      30 * width + 127 := by
  dsimp only [doubleCircuit] at path ⊢
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

/-- The same actual native-classical coordinate obeys the instruction ceiling directly. -/
lemma doubleCircuit_classical_weight_le (spec : ModulusSpec width) (source destination : Fin length)
    (path : (frame.doubleCircuit (model := model) spec source destination).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((frame.doubleCircuit (model := model) spec source destination).resourcePool path) ≤
        30 * width + 127 :=
  (Accounting.classical_weight_le_eventCount _ path).trans
    (frame.doubleCircuit_eventCount_le spec source destination path)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
