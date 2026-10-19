/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Constant
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Phase

/-!
# Native initialization of independently specified constant branches

The two known constants determine only rotation angles. The physical word
contains two one-qubit gates and two CNOTs, with no access to the source.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Shared
noncomputable section

private lemma rotation_scale (angle : ℝ) : rotZStdOp (-2 * angle) = rotZOp angle := by
  unfold rotZStdOp
  congr 1
  ring

/-- Actual coherent selection between two query-free constant initializations. -/
def selectedInitial (oracles : OracleModel) (width : Nat) (zero one : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits (1 + (1 + width))).canonicalPlacement.layout :=
  Gate.Rotation.Multiplex.circuitAt 0 (Fin.natAdd 1 (0 : Fin (1 + width))) (by
    intro same
    have values := congrArg Fin.val same
    change 0 = 1 + 0 at values
    omega) oracles (-2 * Real.arccos zero) (-2 * Real.arccos one)

/-- The full matrix has exactly the two independently specified constant branches. -/
lemma selectedInitial_matrix (oracles : OracleModel) (width : Nat) (zero one : ℝ)
    (environment : oracles.Interpretation) :
    (((selectedInitial oracles width zero one).binaryMatrix environment) :
      HilbertOperator (Qubits (1 + (1 + width)))) =
      Native.branchMatrix ((constantInitial oracles width zero).binaryMatrix environment)
        ((constantInitial oracles width one).binaryMatrix environment) := by
  rw [selectedInitial, Gate.Rotation.Multiplex.circuitAt_prefix_binaryMatrix,
    rotation_scale, rotation_scale]
  simp only [constantInitial, Gate.singleQubitAt_first_binaryMatrix, Native.branchMatrix,
    UnitaryOperator.coe_tensor]
  rfl

/-- All four native events remain visible even when one supplied constant equals one. -/
lemma selectedInitial_eventTrace (oracles : OracleModel) (width : Nat) (zero one : ℝ) :
    (selectedInitial oracles width zero one).eventTrace =
      [.gate .singleQubit, .gate .cnot, .gate .singleQubit, .gate .cnot] := by
  rw [selectedInitial, Gate.Rotation.Multiplex.circuitAt_eventTrace]

/-- Query-free initialization still occupies four actual native dependency steps. -/
lemma selectedInitial_depth (oracles : OracleModel) (width : Nat) (zero one : ℝ) :
    (selectedInitial oracles width zero one).evaluatedEventDepth (fun _ => 1) = 4 := by
  rw [selectedInitial, Gate.Rotation.Multiplex.circuitAt_depth]

end
end QuantumAlg.QSP.MultiQubit.QSVT.Shared
