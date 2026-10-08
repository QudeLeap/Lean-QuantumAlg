/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.ScalarMul.Native.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Cardinality

/-!
# Original numerical ceiling for actual scalar multiplication

Two real initialization instructions precede all declared scalar slots.
Each slot retains both original complete-addition allowances, including
leading zero bits and the exact zero-width initialization behavior.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.ScalarMul.Native

open Execution ClassicalAlgorithms.EllipticCurve

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- Every original slot retains both actual complete-addition allowances. -/
theorem scalarEnvelope_card_le (model : ExecutionModel) [BitWord.Selected model]
    (spec : CurveSpec width)
    (scalarWidth : Nat) :
    (scalarEnvelope model spec scalarWidth).card ≤
      2 + scalarWidth * (248 * width + 644) := by
  have addition := Add.Native.additionEnvelope_card_le model spec
  have doubled : (Add.Native.additionEnvelope model spec).card +
      (Add.Native.additionEnvelope model spec).card ≤ 248 * width + 644 := by omega
  simp only [scalarEnvelope, Multiset.card_add, ResourcePool.scale, Multiset.card_nsmul]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left scalarWidth doubled) 2

/-- The actual full scalar trace obeys the original declared-width numerical ceiling. -/
theorem scalarInto_eventCount_le (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (path : (scalarInto spec bits point accumulator).Path) :
    ((scalarInto spec bits point accumulator).eventTrace path).length ≤
      2 + scalarWidth * (248 * width + 644) :=
  (Multiset.card_le_card (scalarInto_pool_le spec bits point accumulator path)).trans
    (scalarEnvelope_card_le model spec scalarWidth)

end QuantumAlg.ClassicalRoutines.EllipticCurve.ScalarMul.Native
