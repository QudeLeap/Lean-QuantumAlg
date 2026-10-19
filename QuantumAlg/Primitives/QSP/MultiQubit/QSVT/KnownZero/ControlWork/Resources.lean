/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.ControlWork

/-!
# Native resources of the control-work phase word

The final original control is restored by each first-control word. All four
such executions, the nine single-qubit gates and both remaining CNOTs are
retained in the resource pool, including when the signal width is zero.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.ControlWork
noncomputable section

private lemma lastFlip_events (k n : Nat) (oracles : OracleModel) :
    (lastFlip k n oracles).eventCost =
      2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) + ResourcePool.singleton
          (model := .quantum AlgorithmGate.model oracles) (.gate .cnot) := by
  simp only [lastFlip, UnitaryCircuit.seq_eventCost, Gate.singleQubitAt_eventCost,
    Gate.cnotAt_eventCost, two_nsmul]
  ac_rfl

/-- The complete constructed word has no uncounted dirty work or source invocation. -/
lemma controlWork_phase_events (k n : Nat) (oracles : OracleModel) (angle : ℝ) :
    (phase k n oracles angle).eventCost =
      4 • ZeroProjector.SourceWork.budget oracles k +
      9 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) +
      2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .cnot) := by
  simp only [phase, intersectionRotation, UnitaryCircuit.seq_eventCost,
    Gate.singleQubitAt_eventCost, firstRotation, ProjectorPhase.controlledRotation_events,
    KnownZero.flip_events, lastFlip_events]
  simp only [show (4 : Nat) = 2 + 2 from rfl,
    show (9 : Nat) = 1 + 2 + 2 + 2 + 2 from rfl, add_nsmul, one_nsmul, two_nsmul]
  ac_rfl

/-- The borrowed final control is preserved by the first-control rotation on the full space. -/
lemma controlWork_firstRotation_matrix (k n : Nat) (oracles : OracleModel) (angle : ℝ)
    (environment : oracles.Interpretation) :
    (((firstRotation k n oracles angle).binaryMatrix environment) :
        HilbertOperator (Qubits (1 + (k + (1 + n))))) =
      HilbertOperator.tensor (rotZStdOp angle : HilbertOperator (Qubits 1))
        (OrthogonalProjector.zeroAncilla k (1 + n)).op +
      HilbertOperator.tensor (1 : HilbertOperator (Qubits 1))
        (OrthogonalProjector.complement (OrthogonalProjector.zeroAncilla k (1 + n))) := by
  exact ProjectorPhase.controlledRotation_matrix _ _ environment
    (KnownZero.flip_matrix k (1 + n) (by omega) oracles environment) angle

end
end QuantumAlg.QSP.MultiQubit.QSVT.ControlWork
