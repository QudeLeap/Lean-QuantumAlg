/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Phase
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.ControlWork.Four.Resources

/-!
# Shared four-branch native phases on every original register width

The selector wires are unchanged. Empty signal registers borrow an original
control when available, and the completely empty source uses rotations alone.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
noncomputable section

/-- Four selected angles on the same two selectors, phase ancilla and original source. -/
def phase (m n : Nat) (oracles : OracleModel) (a b c d : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles (SharedFour.layout m n) :=
  match m, n with
  | 0, 0 => Gate.Rotation.Multiplex.Four.onPrefix oracles 0
      (-2 * a) (-2 * b) (-2 * c) (-2 * d)
  | k + 1, 0 => ControlWork.Four.phase k 0 oracles a b c d
  | m, n + 1 => SharedFour.phase m (n + 1) (Nat.zero_lt_succ n) oracles a b c d

/-- Every selected branch equals the complete original native phase on all widths. -/
theorem totalFourPhase_matrix (m n : Nat) (oracles : OracleModel) (a b c d : ℝ) :
    ((phase m n oracles a b c d).binaryMatrix :
      HilbertOperator (Qubits (1 + (1 + (1 + (m + n)))))) =
      Native.branchMatrix
        (Native.branchMatrix (Total.phase m n oracles a).binaryMatrix
          (Total.phase m n oracles b).binaryMatrix)
        (Native.branchMatrix (Total.phase m n oracles c).binaryMatrix
          (Total.phase m n oracles d).binaryMatrix) := by
  cases n with
  | zero =>
      cases m with
      | zero =>
          simp only [phase, Total.phase,
            Gate.Rotation.Multiplex.Four.fourRotation_prefix_binaryMatrix,
            Gate.singleQubitAt_first_binaryMatrix, UnitaryOperator.coe_tensor]
          rfl
      | succ k => exact ControlWork.Four.controlWork_fourPhase_matrix k 0 oracles a b c d
  | succ n =>
      simpa only [phase, Total.phase] using
        SharedFour.fourPhase_matrix m (n + 1) (Nat.zero_lt_succ n) oracles a b c d

/-- Independent full sequential phase depth, including all selector rotations. -/
def phaseDepth (m n : Nat) : Nat :=
  match m, n with
  | 0, 0 => 10
  | k + 1, 0 => 4 * (2 * k + EncodedBit.Word.OneDirtyLayout.gateCount k) + 56
  | m, _ + 1 => 2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 10

/-- The same actual four-branch circuit determines its full dependency depth. -/
theorem totalFourPhase_depth (m n : Nat) (oracles : OracleModel) (a b c d : ℝ) :
    (phase m n oracles a b c d).evaluatedEventDepth (fun _ => 1) = phaseDepth m n := by
  cases n with
  | zero =>
      cases m with
      | zero => exact Gate.Rotation.Multiplex.Four.fourRotation_prefix_depth oracles 0 _ _ _ _
      | succ k => exact ControlWork.Four.controlWork_fourPhase_depth k 0 oracles a b c d
  | succ n =>
      cases m <;> exact SharedFour.fourPhase_depth _ (n + 1) (Nat.zero_lt_succ n)
        oracles a b c d

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
