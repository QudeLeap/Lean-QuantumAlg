/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Phase
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Constant.Selected

/-!
# Constant initialization for the four coherent polynomial branches

Only the specified polynomial constants determine these angles. The source
oracle remains untouched, including when a short parity branch has degree zero.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

/-- Actual native initialization of four independently supplied real constant branches. -/
def selectedInitial (oracles : OracleModel) (width : Nat) (c00 c01 c10 c11 : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits (1 + (1 + (1 + width)))).canonicalPlacement.layout :=
  Gate.Rotation.Multiplex.Four.onPrefix oracles width
    (-2 * Real.arccos c00) (-2 * Real.arccos c01)
    (-2 * Real.arccos c10) (-2 * Real.arccos c11)

/-- Every branch is the exact known-constant rotation on the original phase ancilla. -/
theorem fourInitial_matrix (oracles : OracleModel) (width : Nat) (c00 c01 c10 c11 : ℝ) :
    ((selectedInitial oracles width c00 c01 c10 c11).binaryMatrix :
      HilbertOperator (Qubits (1 + (1 + (1 + width))))) =
      Native.branchMatrix
        (Native.branchMatrix (Shared.constantInitial oracles width c00).binaryMatrix
          (Shared.constantInitial oracles width c01).binaryMatrix)
        (Native.branchMatrix (Shared.constantInitial oracles width c10).binaryMatrix
          (Shared.constantInitial oracles width c11).binaryMatrix) := by
  rw [selectedInitial, Gate.Rotation.Multiplex.Four.fourRotation_prefix_binaryMatrix]
  simp only [Shared.rotation_scale, Shared.constantInitial,
    Gate.singleQubitAt_first_binaryMatrix, Native.branchMatrix, UnitaryOperator.coe_tensor]
  rfl

/-- Constant initialization retains the complete ten-gate native word and no source queries. -/
theorem fourInitial_eventTrace (oracles : OracleModel) (width : Nat) (c00 c01 c10 c11 : ℝ) :
    (selectedInitial oracles width c00 c01 c10 c11).eventTrace =
      [.gate .singleQubit, .gate .cnot, .gate .singleQubit, .gate .cnot, .gate .cnot,
        .gate .singleQubit, .gate .cnot, .gate .singleQubit, .gate .cnot, .gate .cnot] := by
  rw [selectedInitial, Gate.Rotation.Multiplex.Four.fourRotation_prefix_eventTrace]

/-- All initialization dependencies are charged even though no source oracle is queried. -/
theorem fourInitial_depth (oracles : OracleModel) (width : Nat) (c00 c01 c10 c11 : ℝ) :
    (selectedInitial oracles width c00 c01 c10 c11).evaluatedEventDepth (fun _ => 1) = 10 := by
  rw [selectedInitial, Gate.Rotation.Multiplex.Four.fourRotation_prefix_depth]

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
