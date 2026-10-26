/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Resources.Complete
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Budget.Values

/-!
# Concrete native-classical bounds of the actual five-array builders

Each theorem concerns every real path of the constructed program, including
its true XGCD and all arithmetic scopes. The independent symbolic ceiling
is instantiated at the original full and tail widths. These are resource
statements; table-value and denominator correctness are separate proofs.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Every actual full-window five-array construction path pays at most this native work. -/
lemma circuit_full16_classical_weight_le (frame : TableFrame ctx 256 (2 ^ 16))
    (spec : ModulusSpec 256) (path : (frame.circuit (model := model) spec).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((frame.circuit (model := model) spec).resourcePool path) ≤ 9087409 :=
  (frame.circuit_classical_weight_le spec path).trans_eq constructionBudget_full16

/-- Every actual tail-window five-array construction path has its own smaller native ceiling. -/
lemma circuit_tail4_classical_weight_le (frame : TableFrame ctx 256 (2 ^ 4))
    (spec : ModulusSpec 256) (path : (frame.circuit (model := model) spec).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((frame.circuit (model := model) spec).resourcePool path) ≤ 56221 :=
  (frame.circuit_classical_weight_le spec path).trans_eq constructionBudget_tail4

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
