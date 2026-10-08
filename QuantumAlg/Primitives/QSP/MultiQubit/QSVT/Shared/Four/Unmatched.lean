/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Resources
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Unmatched

/-!
# One unmatched parity query shared by the real and imaginary branches

The inner selector chooses short versus long parity. The outer selector
chooses real versus imaginary. The final controlled query depends only on
the inner selector and is therefore shared across real and imaginary parts.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n))) (positive : 0 < n)

/-- One final parity-controlled source access, with the real/imaginary selector untouched. -/
def lastSignal (inverse : Bool) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model U true true false) (layout m n) :=
  UnitaryCircuit.onBinarySuffix 1 (UnitarySource.Conditional.withSpectator U inverse)

private theorem lastSignal_matrix (inverse : Bool) :
    ((lastSignal U inverse).binaryMatrix :
      HilbertOperator (Qubits (1 + (1 + (1 + (m + n)))))) =
      Native.branchMatrix
        (Native.branchMatrix 1 (KnownZero.signal U true inverse).binaryMatrix)
        (Native.branchMatrix 1 (KnownZero.signal U true inverse).binaryMatrix) := by
  rw [lastSignal, UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix]
  change HilbertOperator.tensor 1 _ = _
  rw [UnitarySource.Conditional.withSpectator_binaryMatrix, Native.branchMatrix_same,
    KnownZero.signal_matrix]
  rfl

/-- The two longer branches share their final source occurrence but have independent phases. -/
def unmatched (phases : List ((ℝ × ℝ) × (ℝ × ℝ))) (realAngle imaginaryAngle : ℝ) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model U true true false) (layout m n) :=
  ((circuit U positive true phases).seq
    (lastSignal U (decide ((phases.length + 1) % 2 = 0)))).seq
    (phase m n positive (UnitarySource.model U true true false) 0 realAngle 0 imaginaryAngle)

/-- The full operator contains two short words and two independently extended words. -/
theorem fourUnmatched_matrix (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle : ℝ) :
    ((unmatched U positive phases realAngle imaginaryAngle).binaryMatrix :
      HilbertOperator (Qubits (1 + (1 + (1 + (m + n)))))) =
      Native.branchMatrix
        (Native.branchMatrix
          (KnownZero.circuit U positive true (phases.map fun a => a.1.1)).binaryMatrix
          (KnownZero.circuit U positive true
            (realAngle :: phases.map fun a => a.1.2)).binaryMatrix)
        (Native.branchMatrix
          (KnownZero.circuit U positive true (phases.map fun a => a.2.1)).binaryMatrix
          (KnownZero.circuit U positive true
            (imaginaryAngle :: phases.map fun a => a.2.2)).binaryMatrix) := by
  rw [unmatched, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]
  change _ * (_ * _) = _
  rw [fourPhase_matrix, lastSignal_matrix, fourWord_matrix]
  repeat rw [Native.branchMatrix_mul]
  simp only [Shared.zero_phase_matrix positive,
    Matrix.one_mul, KnownZero.circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    List.length_map, Submonoid.coe_mul]

/-- Exact depth includes the one shared conditional query implementation and all native phases. -/
theorem fourUnmatched_depth (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle : ℝ) :
    (unmatched U positive phases realAngle imaginaryAngle).evaluatedEventDepth (fun _ => 1) =
      (2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 11) * phases.length +
        (if (phases.length + 1) % 2 = 0 then 4 else 1) +
        (2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 10) := by
  simp only [unmatched, UnitaryCircuit.evaluatedEventDepth_seq, fourWord_depth, lastSignal,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_unit_depth,
    UnitarySource.Conditional.withSpectator_depth, fourPhase_depth, decide_eq_true_eq]

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
