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
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) true true false) (layout m n) :=
  UnitaryCircuit.onBinarySuffix 1 (UnitarySource.Conditional.withSpectator (m + n) inverse)

private lemma lastSignal_matrix (inverse : Bool) :
    (((lastSignal (m := m) (n := n) inverse).binaryMatrix
      (UnitarySource.interpretation U true true false)) :
      HilbertOperator (Qubits (1 + (1 + (1 + (m + n)))))) =
      Native.branchMatrix
        (Native.branchMatrix 1 ((KnownZero.signal (m := m) (n := n) true inverse).binaryMatrix
          (UnitarySource.interpretation U true true false)))
        (Native.branchMatrix 1 ((KnownZero.signal (m := m) (n := n) true inverse).binaryMatrix
          (UnitarySource.interpretation U true true false))) := by
  rw [lastSignal, UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix]
  change HilbertOperator.tensor 1 _ = _
  rw [UnitarySource.Conditional.withSpectator_binaryMatrix, Native.branchMatrix_same,
    KnownZero.signal_matrix]
  rfl

/-- The two longer branches share their final source occurrence but have independent phases. -/
def unmatched (phases : List ((ℝ × ℝ) × (ℝ × ℝ))) (realAngle imaginaryAngle : ℝ) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) true true false) (layout m n) :=
  ((circuit (m := m) (n := n) positive true phases).seq
    (lastSignal (m := m) (n := n) (decide ((phases.length + 1) % 2 = 0)))).seq
    (phase m n positive (UnitarySource.model (m + n) true true false) 0 realAngle 0 imaginaryAngle)

/-- The full operator contains two short words and two independently extended words. -/
lemma fourUnmatched_matrix (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle : ℝ) :
    (((unmatched (m := m) (n := n) positive phases realAngle imaginaryAngle).binaryMatrix
      (UnitarySource.interpretation U true true false)) :
      HilbertOperator (Qubits (1 + (1 + (1 + (m + n)))))) =
      Native.branchMatrix
        (Native.branchMatrix
          ((KnownZero.circuit (m := m) (n := n) positive true (phases.map fun a
            => a.1.1)).binaryMatrix (UnitarySource.interpretation U true true false))
          ((KnownZero.circuit (m := m) (n := n) positive true
            (realAngle :: phases.map fun a => a.1.2)).binaryMatrix
              (UnitarySource.interpretation U true true false)))
        (Native.branchMatrix
          ((KnownZero.circuit (m := m) (n := n) positive true (phases.map fun a
            => a.2.1)).binaryMatrix (UnitarySource.interpretation U true true false))
          ((KnownZero.circuit (m := m) (n := n) positive true
            (imaginaryAngle :: phases.map fun a => a.2.2)).binaryMatrix
              (UnitarySource.interpretation U true true false))) := by
  rw [unmatched, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]
  change _ * (_ * _) = _
  rw [fourPhase_matrix, lastSignal_matrix, fourWord_matrix]
  repeat rw [Native.branchMatrix_mul]
  simp only [Shared.zero_phase_matrix positive,
    Matrix.one_mul, KnownZero.circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    List.length_map, Submonoid.coe_mul]

/-- Exact depth includes the one shared conditional query implementation and all native phases. -/
lemma fourUnmatched_depth (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle : ℝ) :
    (unmatched (m := m) (n := n) positive phases realAngle imaginaryAngle).evaluatedEventDepth
      (fun _ => 1) =
      (2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 11) * phases.length +
        (if (phases.length + 1) % 2 = 0 then 4 else 1) +
        (2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 10) := by
  simp only [unmatched, UnitaryCircuit.evaluatedEventDepth_seq, fourWord_depth, lastSignal,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_unit_depth,
    UnitarySource.Conditional.withSpectator_depth, fourPhase_depth, decide_eq_true_eq]

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
