/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.Projector.Zero.SourceWork.Matrix
import all QuantumAlg.Components.Oracle.Projector.Zero.SourceWork.Resources
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.ProjectorPhase
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native

/-!
# Native phases for the known block-ancilla projector

The existing signal work bit is restored by each concrete projector flip.
Every phase uses two such native words and one actual one-qubit rotation
[GSLW19, BlockHam.tex:883-887]. No projector query is granted or emitted here.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero
noncomputable section

private def physical (m n : Nat) : QubitLayout (1 + (m + n)) :=
  ⟨Fin.val, Fin.val_injective⟩

/-- The actual zero-controlled flip on the original phase, ancilla and signal wires. -/
def flip (m n : Nat) (positive : 0 < n) (oracles : OracleModel) :
    UnitaryCircuit AlgorithmGate.model oracles (ProjectorPhase.layout (m + n)) :=
  ZeroProjector.SourceWork.program m n positive (physical m n) oracles

/-- The complete concrete operator is the original zero-projector-controlled NOT. -/
lemma flip_matrix (m n : Nat) (positive : 0 < n) (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    ((flip m n positive oracles).binaryMatrix environment) =
      OrthogonalProjector.controlledNotOp (OrthogonalProjector.zeroAncilla m n) :=
  ZeroProjector.SourceWork.program_matrix m n positive (physical m n) oracles environment

/-- Original native gate families and both masks survive the canonical placement. -/
lemma flip_events (m n : Nat) (positive : 0 < n) (oracles : OracleModel) :
    (flip m n positive oracles).eventCost = ZeroProjector.SourceWork.budget oracles m :=
  ZeroProjector.SourceWork.program_events m n positive (physical m n) oracles

/-- The actual sequential flip depth includes the complete restored work schedule. -/
lemma flip_depth (m n : Nat) (positive : 0 < n) (oracles : OracleModel) :
    (flip m n positive oracles).evaluatedEventDepth (fun _ => 1) =
      2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m :=
  ZeroProjector.SourceWork.program_depth m n positive (physical m n) oracles

/-- One native phase slot, with its actual doubled-angle rotation. -/
def phase (m n : Nat) (positive : 0 < n) (oracles : OracleModel) (φ : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles (ProjectorPhase.layout (m + n)) :=
  ProjectorPhase.circuit (flip m n positive oracles) (2 * φ)

/-- Native expansion preserves the full source phase operator, for either parity slot. -/
lemma phase_matrix (m n : Nat) (positive : 0 < n) (oracles : OracleModel)
    (U : UnitaryOperator (Qubits (m + n))) (allowControlled useRight : Bool) (φ : ℝ)
      (environment : oracles.Interpretation) :
    ((phase m n positive oracles φ).binaryMatrix environment) =
      (Native.phase (width := m + n) allowControlled useRight φ).binaryMatrix
        (ProjectedSignal.interpretation U (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) allowControlled) := by
  rw [phase, Native.phase, ProjectorPhase.circuit_matrix, ProjectorPhase.circuit_matrix,
    flip_matrix, ProjectedSignal.Circuit.projectorFlip_matrix]
  cases useRight <;> rfl

/-- Two concrete flip budgets and one native rotation are all charged. -/
lemma phase_events (m n : Nat) (positive : 0 < n) (oracles : OracleModel) (φ : ℝ) :
    (phase m n positive oracles φ).eventCost =
      2 • ZeroProjector.SourceWork.budget oracles m +
        ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
          (.gate .singleQubit) := by
  rw [phase, ProjectorPhase.circuit_events, flip_events, two_nsmul]
  ac_rfl

/-- The native phase's full dependency depth is linear in the original block-ancilla count. -/
lemma phase_depth (m n : Nat) (positive : 0 < n) (oracles : OracleModel) (φ : ℝ) :
    (phase m n positive oracles φ).evaluatedEventDepth (fun _ => 1) =
      2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 1 := by
  rw [phase, ProjectorPhase.circuit_depth, flip_depth]

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero
