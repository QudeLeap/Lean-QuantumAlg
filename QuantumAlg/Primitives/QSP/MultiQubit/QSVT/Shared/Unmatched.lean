/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Resources
import all QuantumAlg.Components.Oracle.UnitarySource.Conditional.Spectator.Binary

/-!
# One unmatched source slot after a common branch sequence

Only the longer branch executes the final source slot. Inverse control is
expanded through ordinary inverse and controlled forward access, retaining
every native event [GSLW19, BlockHam.tex:883-890].
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Shared
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n))) (positive : 0 < n)

private theorem zero_phase_matrix (oracles : OracleModel) :
    ((KnownZero.phase m n positive oracles 0).binaryMatrix :
      HilbertOperator (Qubits (1 + (m + n)))) = 1 := by
  rw [KnownZero.phase, ProjectorPhase.circuit_projector_matrix _ _
    (KnownZero.flip_matrix m n positive oracles)]
  simp only [mul_zero, neg_zero, rotZStdOp_zero]
  change HilbertOperator.tensor 1 _ + HilbertOperator.tensor 1 _ = _
  rw [← HilbertOperator.tensor_add]
  simp only [OrthogonalProjector.complement, add_sub_cancel]
  exact HilbertOperator.one_tensor_one

/-- The common word is followed by the one extra slot of selector branch one. -/
def unmatched (phases : List (ℝ × ℝ)) (lastAngle : ℝ) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model U true true false) (layout m n) :=
  ((circuit U positive true phases).seq
    (UnitarySource.Conditional.withSpectator U (decide ((phases.length + 1) % 2 = 0)))).seq
    (phase m n positive (UnitarySource.model U true true false) 0 lastAngle)

/-- The shorter branch is unchanged; the longer branch has exactly its additional source slot. -/
theorem unmatched_matrix (phases : List (ℝ × ℝ)) (lastAngle : ℝ) :
    ((unmatched U positive phases lastAngle).binaryMatrix :
      HilbertOperator (Qubits (1 + (1 + (m + n))))) =
      Native.branchMatrix
        (KnownZero.circuit U positive true (phases.map Prod.fst)).binaryMatrix
        (KnownZero.circuit U positive true (lastAngle :: phases.map Prod.snd)).binaryMatrix := by
  rw [unmatched, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]
  change _ * (_ * _) = _
  rw [phase_matrix, UnitarySource.Conditional.withSpectator_binaryMatrix,
    circuit_matrix]
  change Native.branchMatrix _ _ * (Native.branchMatrix 1 _ * Native.branchMatrix _ _) = _
  rw [Native.branchMatrix_mul, Native.branchMatrix_mul, zero_phase_matrix positive]
  simp only [Matrix.one_mul, KnownZero.circuit,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, KnownZero.signal_matrix,
    List.length_map, Submonoid.coe_mul, UnitaryOperator.coe_tensor]
  rfl

/-- Exact depth includes the native selector and, when needed, expanded inverse control. -/
theorem unmatched_depth (phases : List (ℝ × ℝ)) (lastAngle : ℝ) :
    (unmatched U positive phases lastAngle).evaluatedEventDepth (fun _ => 1) =
      (2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 5) * phases.length +
        (if (phases.length + 1) % 2 = 0 then 4 else 1) +
        (2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 4) := by
  simp only [unmatched, UnitaryCircuit.evaluatedEventDepth_seq, circuit_depth,
    UnitarySource.Conditional.withSpectator_depth, phase_depth, decide_eq_true_eq]

end
end QuantumAlg.QSP.MultiQubit.QSVT.Shared
