/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Phase
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Operator
import all QuantumAlg.Components.Gates.Rotation.Multiplex.Binary

/-!
# Shared native projector flips with branch-selected phases

The selector controls only the rotation angle. Both branches use the same
native projector flips, with the same restored signal work and no source
oracle occurrence [GSLW19, BlockHam.tex:883-890].
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Shared
noncomputable section

/-- Original selector, phase ancilla and complete source suffix. -/
abbrev layout (m n : Nat) :=
  (QuantumSignature.qubits (1 + (1 + (m + n)))).canonicalPlacement.layout

/-- Both branches share each native zero-projector flip. Only the rotation is selected. -/
def phase (m n : Nat) (positive : 0 < n) (oracles : OracleModel) (zero one : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles (layout m n) :=
  let flip := UnitaryCircuit.onBinarySuffix 1 (KnownZero.flip m n positive oracles)
  (flip.seq (Gate.Rotation.Multiplex.circuitAt 0
    (Fin.natAdd 1 (0 : Fin (1 + (m + n)))) (by
      intro same
      have values := congrArg Fin.val same
      change 0 = 1 + 0 at values
      omega) oracles
    (2 * zero) (2 * one))).seq flip

/-- The actual native phase word is the exact direct sum of the two independently chosen phases. -/
theorem phase_matrix (m n : Nat) (positive : 0 < n) (oracles : OracleModel) (zero one : ℝ) :
    ((phase m n positive oracles zero one).binaryMatrix :
      HilbertOperator (Qubits (1 + (1 + (m + n))))) =
      Native.branchMatrix (KnownZero.phase m n positive oracles zero).binaryMatrix
        (KnownZero.phase m n positive oracles one).binaryMatrix := by
  rw [phase, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix]
  change _ * (_ * _) = _
  rw [Gate.Rotation.Multiplex.circuitAt_prefix_binaryMatrix]
  have identityMatrix : ((1 : UnitaryOperator (Qubits 1)) :
      HilbertOperator (Qubits 1)) = 1 := rfl
  simp only [UnitaryOperator.coe_tensor, identityMatrix]
  change HilbertOperator.tensor 1 _ * (Native.branchMatrix _ _ *
    HilbertOperator.tensor 1 _) = _
  rw [← Native.branchMatrix_same, Native.branchMatrix_mul, Native.branchMatrix_mul]
  simp only [KnownZero.phase, ProjectorPhase.circuit_matrix, Submonoid.coe_mul,
    UnitaryOperator.coe_tensor]
  rfl

/-- Both flips and all four selector gates occupy one sequential dependency chain. -/
theorem phase_depth (m n : Nat) (positive : 0 < n) (oracles : OracleModel) (zero one : ℝ) :
    (phase m n positive oracles zero one).evaluatedEventDepth (fun _ => 1) =
      2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 4 := by
  simp only [phase, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_unit_depth, KnownZero.flip_depth,
    Gate.Rotation.Multiplex.circuitAt_depth]
  omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.Shared
