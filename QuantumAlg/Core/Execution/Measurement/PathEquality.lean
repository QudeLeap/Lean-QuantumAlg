/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Matrix

/-!
# Actual Z paths depend only on their measured wire values

Unmeasured coordinates do not change the outcome path or any of its real
classical writes [dW19, qcnotes.tex:5409,5420].
-/

namespace QuantumAlg.Circuit

/-- Agreement on the actual measured wires gives equality of the actual finite outcome paths. -/
theorem measurementBasisPath_eq_of_agree {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx)) (left right : ctx.register.Index)
    (same : measurementLabelsAgree readouts left right) :
    measurementBasisPath readouts left = measurementBasisPath readouts right := by
  induction readouts with
  | nil => rfl
  | cons head tail induction =>
      exact Prod.ext same.1 (induction same.2)

/-- Every actual classical write is unchanged by modifying only unmeasured basis coordinates. -/
theorem writeMeasurementPath_eq_of_agree {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx)) (store : Execution.Store ctx)
    (left right : ctx.register.Index) (same : measurementLabelsAgree readouts left right) :
    writeMeasurementPath readouts store (measurementBasisPath readouts left) =
      writeMeasurementPath readouts store (measurementBasisPath readouts right) :=
  congrArg (writeMeasurementPath readouts store)
    (measurementBasisPath_eq_of_agree readouts left right same)

end QuantumAlg.Circuit
