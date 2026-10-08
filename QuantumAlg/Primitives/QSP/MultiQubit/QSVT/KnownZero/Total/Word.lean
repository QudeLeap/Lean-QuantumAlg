/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Resources

/-!
# Native alternating source words on every original register width

The original source operator is retained when the signal register is empty.
Every known-projector phase is expanded into actual default native gates.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n))) (allowControlled : Bool)

private theorem phase_native_matrix (oracles : OracleModel) (useRight : Bool) (angle : ℝ) :
    (phase m n oracles angle).binaryMatrix =
      (Native.phase U (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) allowControlled useRight angle).binaryMatrix := by
  apply Subtype.ext
  rw [totalPhase_projector_matrix, Native.phase,
    ProjectorPhase.circuit_projector_matrix _ _
      (ProjectedSignal.Circuit.projectorFlip_matrix AlgorithmGate.model U
        (OrthogonalProjector.zeroAncilla m n) (OrthogonalProjector.zeroAncilla m n)
        allowControlled useRight)]
  cases useRight <;> simp only [Bool.false_eq_true, ite_false, ite_true, neg_mul]

/-- Each phase slot follows one alternating ordinary or inverse source occurrence. -/
def circuit : List ℝ →
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model U allowControlled true false)
      (ProjectorPhase.layout (m + n))
  | [] => .identity _ _ _
  | angle :: phases =>
      ((circuit phases).seq
        (KnownZero.signal U allowControlled (decide ((phases.length + 1) % 2 = 0)))).seq
        (phase m n (UnitarySource.model U allowControlled true false) angle)

/-- Native phase expansion preserves the complete original operator on every width. -/
theorem totalCircuit_matrix (phases : List ℝ) :
    (circuit U allowControlled phases).binaryMatrix =
      (Native.circuit U (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) allowControlled phases).binaryMatrix := by
  induction phases with
  | nil =>
      simp only [circuit, Native.circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_identity]
  | cons angle phases ih =>
      simp only [circuit, Native.circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
        ih, KnownZero.signal_matrix, Native.signal_matrix]
      rw [phase_native_matrix U allowControlled]

/-- The full native word realizes both source phase products without a width restriction. -/
theorem totalCircuit_source_matrix (phases : List ℝ) :
    ((circuit U allowControlled phases).binaryMatrix :
      HilbertOperator (Qubits (1 + (m + n)))) =
      Native.branchMatrix
        (Native.sourceWord U (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases)
        (Native.sourceWord U (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) (phases.map fun angle => -angle)) := by
  rw [totalCircuit_matrix]
  exact Native.circuit_source_matrix U _ _ allowControlled phases

/-- Every native phase and each abstract source dependency step are charged. -/
theorem totalCircuit_depth (phases : List ℝ) :
    (circuit U allowControlled phases).evaluatedEventDepth (fun _ => 1) =
      (phaseDepth m n + 1) * phases.length := by
  induction phases with
  | nil => change 0 = _; simp
  | cons angle phases ih =>
      simp only [circuit, UnitaryCircuit.evaluatedEventDepth_seq, ih,
        KnownZero.signal_depth, totalPhase_depth, List.length_cons]
      ring

/-- The uniform depth bound includes the zero-signal-width construction. -/
theorem totalCircuit_depth_le (phases : List ℝ) :
    (circuit U allowControlled phases).evaluatedEventDepth (fun _ => 1) ≤
      (40 * m + 4) * phases.length := by
  rw [totalCircuit_depth]
  exact Nat.mul_le_mul_right phases.length (by have := totalPhaseDepth_le m n; omega)

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total
