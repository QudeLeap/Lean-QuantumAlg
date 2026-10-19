/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Resources
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Unmatched
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Unmatched

/-!
# One unmatched parity query shared by the real and imaginary branches

The inner selector chooses short versus long parity. The outer selector
chooses real versus imaginary. The final controlled query depends only on
the inner selector and is therefore shared across real and imaginary parts.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))

private lemma zero_phase_matrix (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    (((Total.phase m n oracles 0).binaryMatrix environment) :
      HilbertOperator (Qubits (1 + (m + n)))) = 1 := by
  rw [totalPhase_projector_matrix]
  simp only [mul_zero, rotZStdOp_zero]
  change HilbertOperator.tensor 1 _ + HilbertOperator.tensor 1 _ = _
  rw [← HilbertOperator.tensor_add]
  simp only [OrthogonalProjector.complement, add_sub_cancel]
  exact HilbertOperator.one_tensor_one

/-- The two longer branches share their final source occurrence but have independent phases. -/
def unmatched (phases : List ((ℝ × ℝ) × (ℝ × ℝ))) (realAngle imaginaryAngle : ℝ) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) true true false)
      (SharedFour.layout m n) :=
  ((circuit (m := m) (n := n) true phases).seq
    (SharedFour.lastSignal (m := m) (n := n) (decide ((phases.length + 1) % 2 = 0)))).seq
    (phase m n (UnitarySource.model (m + n) true true false) 0 realAngle 0 imaginaryAngle)

/-- The full operator contains two short words and two independently extended words. -/
lemma totalFourUnmatched_matrix (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle : ℝ) :
    (((unmatched (m := m) (n := n) phases realAngle imaginaryAngle).binaryMatrix
      (UnitarySource.interpretation U true true false)) :
      HilbertOperator (Qubits (1 + (1 + (1 + (m + n)))))) =
      Native.branchMatrix
        (Native.branchMatrix
          ((Total.circuit (m := m) (n := n) true (phases.map fun a => a.1.1)).binaryMatrix
            (UnitarySource.interpretation U true true false))
          ((Total.circuit (m := m) (n := n) true
            (realAngle :: phases.map fun a => a.1.2)).binaryMatrix
              (UnitarySource.interpretation U true true false)))
        (Native.branchMatrix
          ((Total.circuit (m := m) (n := n) true (phases.map fun a => a.2.1)).binaryMatrix
            (UnitarySource.interpretation U true true false))
          ((Total.circuit (m := m) (n := n) true
            (imaginaryAngle :: phases.map fun a => a.2.2)).binaryMatrix
              (UnitarySource.interpretation U true true false))) := by
  rw [unmatched, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]
  change _ * (_ * _) = _
  rw [totalFourPhase_matrix, SharedFour.lastSignal_matrix, totalFourWord_matrix]
  repeat rw [Native.branchMatrix_mul]
  simp only [zero_phase_matrix,
    Matrix.one_mul, Total.circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    List.length_map, Submonoid.coe_mul]

/-- Exact depth includes the one shared conditional query implementation and all native phases. -/
lemma totalFourUnmatched_depth (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle : ℝ) :
    (unmatched (m := m) (n := n) phases realAngle imaginaryAngle).evaluatedEventDepth (fun _ => 1) =
      (phaseDepth m n + 1) * phases.length +
        (if (phases.length + 1) % 2 = 0 then 4 else 1) +
        phaseDepth m n := by
  simp only [unmatched, UnitaryCircuit.evaluatedEventDepth_seq, totalFourWord_depth,
    SharedFour.lastSignal,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_unit_depth,
    UnitarySource.Conditional.withSpectator_depth, totalFourPhase_depth, decide_eq_true_eq]

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
