/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Measure.Instrument

/-!
# Complete original-label fibers of actual quantum updates

Selecting an earlier classical label before or after an actual unitary or
Z update preserves the same full quantum block. This keeps an untouched
classical frame available when proving the measured arithmetic separately
in each original-history fiber [dW19, qcnotes.tex:5381,5409]. It does not
normalize, discard a quantum system or introduce an execution operation.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

variable {C D O : Type} [Fintype C] [DecidableEq D] {R : Register}

/-- Unitary conjugation commutes with selecting an unchanged original classical label. -/
theorem selectClassical_applyUnitary (state : ExecutionState C R)
    (operator : C → UnitaryOperator R) (read : C → D) (selected : D) :
    (state.applyUnitary operator).selectClassical read selected =
      (state.selectClassical read selected).applyUnitary operator := by
  apply ExecutionState.ext
  intro entry
  apply DensityOperator.ext
  by_cases same : read entry = selected
  · simp only [selectClassical_block, applyUnitary_block, same, if_true]
  · simp only [selectClassical_block, applyUnitary_block, same, if_false,
      DensityOperator.zero_matrix, DensityOperator.applyUnitary_matrix,
      Matrix.mul_zero, Matrix.zero_mul]

/-- Recording the actual Z outcome preserves selection by the complete original label. -/
theorem selectClassical_measureZ [Fintype O] [DecidableEq O]
    (state : ExecutionState C R) (readout : R.Index → O)
    (read : C → D) (selected : D) :
    (state.measureZ readout).selectClassical (fun record => read record.1) selected =
      (state.selectClassical read selected).measureZ readout := by
  apply ExecutionState.ext
  rintro ⟨entry, outcome⟩
  by_cases same : read entry = selected
  · simp only [selectClassical_block, measureZ_block, same, if_true]
  · simp only [selectClassical_block, measureZ_block, same, if_false,
      ZMeasurement.branch_zero]

end

end QuantumAlg.ExecutionState
