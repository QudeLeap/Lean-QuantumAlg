/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Phase
import all QuantumAlg.Components.Oracle.UnitarySource.Binary
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Operator

/-!
# Alternating source words with native zero-projector phases

Only U and its explicitly granted inverse remain source queries. Known
zero-projector phases expand into literal default gates on the same original
signal wires [GSLW19, BlockHam.tex:883-890]. No controlled source is used by a
matching-parity word, even if its surrounding problem grants that capability.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
  (positive : 0 < n) (allowControlled : Bool)

/-- One ordinary or inverse source occurrence, preserving the existing phase ancilla. -/
def signal (inverse : Bool) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true false)
      (ProjectorPhase.layout (m + n)) :=
  UnitaryCircuit.onBinarySuffix 1
    (UnitarySource.Binary.circuit AlgorithmGate.model (m + n) allowControlled inverse)

/-- The query acts exactly on its original suffix. -/
lemma signal_matrix (inverse : Bool) :
    ((signal (m := m) (n := n) allowControlled inverse).binaryMatrix
      (UnitarySource.interpretation U allowControlled true false)) =
      (1 : UnitaryOperator (Qubits 1)).tensor (if inverse then U⁻¹ else U) := by
  rw [signal, UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix,
    UnitarySource.Binary.circuit_matrix]

/-- The concrete source list alternates ordinary and inverse slots in source order. -/
def circuit : List ℝ →
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true false)
      (ProjectorPhase.layout (m + n))
  | [] => .identity _ _ _
  | φ :: phases =>
      ((circuit phases).seq
        (signal (m := m) (n := n) allowControlled (decide ((phases.length + 1) % 2 = 0)))).seq
        (phase m n positive (UnitarySource.model (m + n) allowControlled true false) φ)

/-- Replacing known-projector queries by native words preserves the complete original operator. -/
lemma circuit_matrix (phases : List ℝ) :
    ((circuit (m := m) (n := n) positive allowControlled phases).binaryMatrix
      (UnitarySource.interpretation U allowControlled true false)) =
      ((Native.circuit (width := m + n) allowControlled phases).binaryMatrix
        (ProjectedSignal.interpretation U (OrthogonalProjector.zeroAncilla m n)
      (OrthogonalProjector.zeroAncilla m n) allowControlled)) := by
  induction phases with
  | nil =>
      simp only [circuit, Native.circuit,
        UnitaryCircuit.unitaryCircuit_binaryMatrix_identity]
  | cons φ phases ih =>
      simp only [circuit, Native.circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
        ih, signal_matrix, Native.signal_matrix]
      rw [phase_matrix m n positive (UnitarySource.model (m + n) allowControlled true false)
        U allowControlled (decide ((phases.length + 1) % 2 = 0)) φ
        (UnitarySource.interpretation U allowControlled true false)]

/-- The actual native word realizes both original source phase products on every input. -/
lemma circuit_source_matrix (phases : List ℝ) :
    (((circuit (m := m) (n := n) positive allowControlled phases).binaryMatrix
      (UnitarySource.interpretation U allowControlled true false)) :
      HilbertOperator (Qubits (1 + (m + n)))) =
      Native.branchMatrix
        (Native.sourceWord U (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases)
        (Native.sourceWord U (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) (phases.map fun φ => -φ)) := by
  rw [circuit_matrix]
  exact Native.circuit_source_matrix U _ _ allowControlled phases

/-- Each source query contributes exactly one abstract dependency step. -/
lemma signal_depth (inverse : Bool) :
    (signal (m := m) (n := n) allowControlled inverse).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [signal, UnitaryCircuit.unitaryCircuit_onBinarySuffix_unit_depth,
    UnitarySource.Binary.circuit_depth]

/-- Exact full depth charges each source slot, both restored native flips and the rotation. -/
lemma circuit_depth (phases : List ℝ) :
    (circuit (m := m) (n := n) positive allowControlled phases).evaluatedEventDepth (fun _ => 1) =
      (2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 2) * phases.length := by
  induction phases with
  | nil => change 0 = _; simp
  | cons φ phases ih =>
      simp only [circuit, UnitaryCircuit.evaluatedEventDepth_seq, ih, signal_depth,
        phase_depth, List.length_cons]
      ring

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero
