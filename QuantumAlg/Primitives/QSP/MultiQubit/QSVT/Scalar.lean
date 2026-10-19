/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Oracle.SignalProcessing
public import QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Components.Oracle.SignalProcessing
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Native constant-polynomial dilation

A constant contraction needs one actual single-qubit operation on the transformation
ancilla. The entire source and system suffix is retained, including zero-width
source ancillas. No oracle call is introduced by this constant case.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Scalar

noncomputable section

/-- Canonical phase ancilla followed by the original source and system registers. -/
public abbrev layout (m n : Nat) :=
  (QuantumSignature.qubits (1 + (m + n))).canonicalPlacement.layout

/-- One native dilation gate; no operation touches the original suffix. -/
def circuit (oracles : OracleModel) (m n : Nat) (c : ℂ)
    (hc : Complex.normSq c ≤ 1) : UnitaryCircuit AlgorithmGate.model oracles (layout m n) :=
  Gate.singleQubitAt (layout m n) oracles (scalarDilationOperator c hc)
    (0 : Fin (1 + (m + n))) rfl

/-- The complete matrix is the scalar dilation tensored with the untouched suffix. -/
lemma circuit_matrix (oracles : OracleModel) (m n : Nat) (c : ℂ)
    (hc : Complex.normSq c ≤ 1) (environment : oracles.Interpretation) :
    ((circuit oracles m n c hc).binaryMatrix environment) =
      (scalarDilationOperator c hc).tensor (1 : UnitaryOperator (Qubits (m + n))) :=
  Gate.singleQubitAt_first_binaryMatrix oracles (m + n) (scalarDilationOperator c hc) environment

/-- A constant diagonal dilation is exactly one scalar dilation tensored with identity. -/
lemma constant_diagonal (width : Nat) (c : ℂ) (hc : Complex.normSq c ≤ 1) :
    diagonalScalarDilationOperator (n := width) (fun _ => c) (fun _ => hc) =
      (scalarDilationOperator c hc).tensor (1 : UnitaryOperator (Qubits width)) := by
  ext row column
  obtain ⟨⟨a, i⟩, rfl⟩ := (prodEquiv (m := 1) (n := width)).surjective row
  obtain ⟨⟨b, j⟩, rfl⟩ := (prodEquiv (m := 1) (n := width)).surjective column
  by_cases same : i = j <;>
    simp [diagonalScalarDilationOperator, diagonalScalarDilationQubitOp,
      diagonalScalarDilationOp, UnitaryOperator.tensor_apply, scalarDilationOperator,
      same]

/-- Reassociating physical coordinates gives the existing intrinsic scalar block encoding. -/
lemma circuit_source_matrix (oracles : OracleModel) (m n : Nat) (c : ℂ)
    (hc : Complex.normSq c ≤ 1) (environment : oracles.Interpretation) :
    reassociatePhaseAncillaOperator (m := m) (n := n)
        ((circuit oracles m n c hc).binaryMatrix environment) =
      scalarDilationWithSourceAncillas (m := m) (n := n) c hc := by
  rw [circuit_matrix, scalarDilationWithSourceAncillas, constant_diagonal]

/-- All actual events consist of exactly one default single-qubit gate, including m=0. -/
lemma circuit_events (oracles : OracleModel) (m n : Nat) (c : ℂ)
    (hc : Complex.normSq c ≤ 1) :
    (circuit oracles m n c hc).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) := rfl

/-- The constant case occupies one actual native dependency step. -/
lemma circuit_depth (oracles : OracleModel) (m n : Nat) (c : ℂ)
    (hc : Complex.normSq c ≤ 1) :
    (circuit oracles m n c hc).evaluatedEventDepth (fun _ => 1) = 1 := rfl

end

end QuantumAlg.QSP.MultiQubit.QSVT.Scalar
