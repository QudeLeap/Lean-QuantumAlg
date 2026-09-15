/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Access
import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Preparation

/-!
# Original finite-cyclic literal unitary experiment

The original Algorithm-1 preparations, encoded group-action query and inverse
Fourier readouts retain their definitions and mathematical equivalence. This
owner does not package allocation, classical recovery or fresh repetition.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt

noncomputable section

universe u

variable {G : Type u} [Group G]

open UniformSuperposition

/-- Two literal preparations execute in parallel on consecutive exponent
registers. -/
def exponentPreparationCircuit (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) :
    UnitaryCircuit (Qubits (orderWidth P + orderWidth P)) :=
  pairConsecutiveCircuit (paddedPreparation P B)
    (paddedPreparation_physical_idx P B)

@[simp]
theorem exponentPreparationCircuit_physical_idx (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) :
    (exponentPreparationCircuit P B).physical_idx =
      List.range (orderWidth P + orderWidth P) := by
  exact pairConsecutiveCircuit_physical_idx (paddedPreparation P B)
    (paddedPreparation_physical_idx P B)

/-- The two exponent preparations with an untouched encoded-group workspace. -/
def preparationCircuit (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) :
    UnitaryCircuit (Qubits (totalQubits P)) :=
  withGroupWorkspace (exponentPreparationCircuit P B)
    (exponentPreparationCircuit_physical_idx P B)

@[simp]
theorem preparationCircuit_physical_idx (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) :
    (preparationCircuit P B).physical_idx = List.range (totalQubits P) := by
  unfold preparationCircuit
  simpa only [totalQubits] using
    withGroupWorkspace_physical_idx (exponentPreparationCircuit P B)
      (exponentPreparationCircuit_physical_idx P B)

/-- An analytical witness derived from the matrix of the actual Algorithm-1
circuit.  It reuses the established Born proof without making an opaque
range-preparation operator an input to the gate-level endpoint. -/
def derivedAccess (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    Access P where
  uniform :=
    { operator := (paddedPreparation P B).matrix
      apply_zero := by
        simpa only [UnitaryCircuit.applyNormalized, BornBridge.exponentState] using
          paddedPreparation_apply_zero P B }
  ux := ux

@[simp]
private theorem derivedAccess_ux (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    (derivedAccess P B ux).ux = ux :=
  rfl

/-- Replacing the derived analytical leaf by the literal Algorithm-1 circuit
changes the event tree but not the preparation operator. -/
theorem preparationCircuit_matrix_eq_uniformCircuit
    (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    (preparationCircuit P B).matrix =
      (uniformCircuit (derivedAccess P B ux)).matrix := by
  have uniformMatrix :
      (uniformPreparationCircuit (derivedAccess P B ux)).matrix =
        (paddedPreparation P B).matrix := by
    rfl
  simp only [preparationCircuit, uniformCircuit, withGroupWorkspace,
    UnitaryCircuit.tensorQubits_matrix, exponentPreparationCircuit,
    pairConsecutiveCircuit, UnitaryCircuit.shiftPhysicalIdx_matrix,
    uniformMatrix]

/-! ## One actual gate-level attempt -/

/-- The sealed computational-basis input uses the same group encoding as the
single encoded `U_x` query. -/
def inputPreparation (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    KnownPreparation (totalQubits P) :=
  Canonical.inputPreparation (derivedAccess P B ux)

/-- The complete literal preparation-query-readout circuit for one attempt. -/
def quantumCircuit (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    UnitaryCircuit (Qubits (totalQubits P)) :=
  UnitaryCircuit.seq (preparationCircuit P B)
    (UnitaryCircuit.seq (uxCircuit (derivedAccess P B ux))
      (inverseQFTCircuit P))

@[simp]
theorem quantumCircuit_physical_idx (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    (quantumCircuit P B ux).physical_idx = List.range (totalQubits P) := by
  simp only [quantumCircuit, UnitaryCircuit.seq, preparationCircuit_physical_idx,
    uxCircuit_physical_idx, inverseQFTCircuit_physical_idx,
    UnitaryCircuit.unionPhysicalIdx_self]

/-- The gate-level circuit and the derived analytical circuit have the same
unitary semantics on every input state. -/
theorem quantumCircuit_applyNormalized_eq_analytical
    (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (state : NormalizedVector (Qubits (totalQubits P))) :
    (quantumCircuit P B ux).applyNormalized state =
      (Canonical.quantumCircuit (derivedAccess P B ux)).applyNormalized state := by
  have matrixEquality :
      (quantumCircuit P B ux).matrix =
        (Canonical.quantumCircuit (derivedAccess P B ux)).matrix := by
    apply Subtype.ext
    unfold quantumCircuit Canonical.quantumCircuit
    rw [UnitaryCircuit.seq_matrix, UnitaryCircuit.seq_matrix, UnitaryCircuit.seq_matrix,
      UnitaryCircuit.seq_matrix, preparationCircuit_matrix_eq_uniformCircuit]
  simpa only [UnitaryCircuit.applyNormalized] using congrArg
    (fun operator : UnitaryOperator (Qubits (totalQubits P)) =>
      operator.apply state)
    matrixEquality

end

end QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt
