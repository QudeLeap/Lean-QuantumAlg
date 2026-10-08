/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Rotation.Multiplex.Four.Binary
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Phase

/-!
# Four projector-phase branches sharing one pair of native flips

The two selector wires only select phase angles. Projector flips act on the
original phase and source wires, and are shared by all four branches.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

/-- Two selectors, one phase ancilla, then the complete original source register. -/
abbrev layout (m n : Nat) :=
  (QuantumSignature.qubits (1 + (1 + (1 + (m + n))))).canonicalPlacement.layout

/-- Four supplied angles use just one common flip/rotation/flip schedule. -/
def phase (m n : Nat) (positive : 0 < n) (oracles : OracleModel)
    (a00 a01 a10 a11 : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles (layout m n) :=
  let flip := UnitaryCircuit.onBinarySuffix 1
    (UnitaryCircuit.onBinarySuffix 1 (KnownZero.flip m n positive oracles))
  (flip.seq (Gate.Rotation.Multiplex.Four.onPrefix oracles (m + n)
    (2 * a00) (2 * a01) (2 * a10) (2 * a11))).seq flip

/-- All four independently specified phase operators occur as the exact original branches. -/
theorem fourPhase_matrix (m n : Nat) (positive : 0 < n) (oracles : OracleModel)
    (a00 a01 a10 a11 : ℝ) :
    ((phase m n positive oracles a00 a01 a10 a11).binaryMatrix :
      HilbertOperator (Qubits (1 + (1 + (1 + (m + n)))))) =
      Native.branchMatrix
        (Native.branchMatrix (KnownZero.phase m n positive oracles a00).binaryMatrix
          (KnownZero.phase m n positive oracles a01).binaryMatrix)
        (Native.branchMatrix (KnownZero.phase m n positive oracles a10).binaryMatrix
          (KnownZero.phase m n positive oracles a11).binaryMatrix) := by
  rw [phase, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix]
  change _ * (_ * _) = _
  rw [Gate.Rotation.Multiplex.Four.fourRotation_prefix_binaryMatrix]
  have identityMatrix : ((1 : UnitaryOperator (Qubits 1)) :
      HilbertOperator (Qubits 1)) = 1 := rfl
  simp only [UnitaryOperator.coe_tensor, identityMatrix]
  change HilbertOperator.tensor 1 (HilbertOperator.tensor 1 _) *
    (Native.branchMatrix (Native.branchMatrix _ _) (Native.branchMatrix _ _) *
      HilbertOperator.tensor 1 (HilbertOperator.tensor 1 _)) = _
  simp only [← Native.branchMatrix_same]
  repeat rw [Native.branchMatrix_mul]
  simp only [KnownZero.phase, ProjectorPhase.circuit_matrix, Submonoid.coe_mul,
    UnitaryOperator.coe_tensor]
  rfl

/-- The physical depth charges both shared flips and all ten native selector operations. -/
theorem fourPhase_depth (m n : Nat) (positive : 0 < n) (oracles : OracleModel)
    (a00 a01 a10 a11 : ℝ) :
    (phase m n positive oracles a00 a01 a10 a11).evaluatedEventDepth (fun _ => 1) =
      2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 10 := by
  simp only [phase, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_unit_depth, KnownZero.flip_depth,
    Gate.Rotation.Multiplex.Four.fourRotation_prefix_depth]
  omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
