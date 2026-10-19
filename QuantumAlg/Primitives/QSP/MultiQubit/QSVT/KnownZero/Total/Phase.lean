/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.ControlWork.ZeroWidth

/-!
# Native known-projector phases on every original register width

Positive signal width uses the restored signal-work construction. At zero
signal width a nonempty control register supplies its own restored work.
With no controls and no signal, one native phase rotation suffices.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total
noncomputable section

/-- One actual native phase on the original phase, block-ancilla and signal wires. -/
def phase (m n : Nat) (oracles : OracleModel) (angle : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles (ProjectorPhase.layout (m + n)) :=
  match m, n with
  | 0, 0 => Gate.singleQubitAt (ProjectorPhase.layout 0) oracles (rotZStdOp (-2 * angle))
      (0 : Fin 1) rfl
  | k + 1, 0 => ControlWork.phase k 0 oracles angle
  | m, n + 1 => KnownZero.phase m (n + 1) (Nat.zero_lt_succ n) oracles angle

/-- Positive-width execution retains the existing restored signal-work word exactly. -/
lemma totalPhase_of_positive (m n : Nat) (positive : 0 < n)
    (oracles : OracleModel) (angle : ℝ) :
    phase m n oracles angle = KnownZero.phase m n positive oracles angle := by
  cases n with
  | zero => omega
  | succ n => cases m <;> rfl

/-- The complete projector-phase operator holds on the original unrestricted width domain. -/
lemma totalPhase_projector_matrix (m n : Nat) (oracles : OracleModel) (angle : ℝ)
    (environment : oracles.Interpretation) :
    (((phase m n oracles angle).binaryMatrix environment) : HilbertOperator (Qubits (1 + (m + n))))
      =
      HilbertOperator.tensor (rotZStdOp (-2 * angle) : HilbertOperator (Qubits 1))
        (OrthogonalProjector.zeroAncilla m n).op +
      HilbertOperator.tensor (rotZStdOp (2 * angle) : HilbertOperator (Qubits 1))
        (OrthogonalProjector.complement (OrthogonalProjector.zeroAncilla m n)) := by
  cases n with
  | zero =>
      cases m with
      | zero =>
          rw [phase, Gate.singleQubitAt_first_binaryMatrix]
          ext row column
          fin_cases row <;> fin_cases column <;>
            simp [OrthogonalProjector.zeroAncilla,
              OrthogonalProjector.tensor, OrthogonalProjector.zero, OrthogonalProjector.basis,
              OrthogonalProjector.basisOp, OrthogonalProjector.identity,
              OrthogonalProjector.complement, HilbertOperator.tensor,
              prodEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat]
      | succ k => exact ControlWork.controlWork_zeroWidth_phase_matrix k oracles angle environment
  | succ n =>
      simpa only [phase, KnownZero.phase, neg_mul] using
        ProjectorPhase.circuit_projector_matrix
          (KnownZero.flip m (n + 1) (Nat.zero_lt_succ n) oracles)
          (OrthogonalProjector.zeroAncilla m (n + 1)) environment
          (KnownZero.flip_matrix m (n + 1) (Nat.zero_lt_succ n) oracles environment) (2 * angle)

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total
