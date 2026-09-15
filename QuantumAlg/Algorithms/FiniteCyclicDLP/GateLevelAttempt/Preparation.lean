/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation.State
import all QuantumAlg.Primitives.UniformSuperposition

/-!
# Original literal range preparation at the Fourier width

The original binary-expansion width bound and padded Algorithm-1 circuit
prepare the same normalized exponent state. Their mathematical and unitary
bodies are independent of terminal measurement, repetition and recovery.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt

noncomputable section

universe u

variable {G : Type u} [Group G]

open UniformSuperposition

/-- The intrinsic Algorithm-1 carrier fits inside the oversampled Fourier
register.  This follows from the highest genuine binary term, rather than from
an endpoint-supplied padding certificate. -/
theorem binaryExpansion_width_le_orderWidth (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) :
    B.width ≤ orderWidth P := by
  have highestTerm : 2 ^ B.last ≤ P.order := by
    calc
      2 ^ B.last ≤ ∑ index, 2 ^ B.ell index := by
        unfold UniformSuperposition.BinaryExpansion.last
        exact Finset.single_le_sum
          (fun index
              (_member : index ∈ (Finset.univ : Finset (Fin (B.s + 1)))) =>
            Nat.zero_le (2 ^ B.ell index))
          (Finset.mem_univ (Fin.last B.s))
      _ = P.order := B.sum_powers.symm
  have intrinsicPower : 2 ^ B.width ≤ oversampledOrder P := by
    unfold UniformSuperposition.BinaryExpansion.width
    rw [pow_succ]
    unfold oversampledOrder fourierOversamplingFactor
    omega
  have powerBound : 2 ^ B.width ≤ 2 ^ orderWidth P :=
    intrinsicPower.trans (oversampledOrder_le_fourierModulus P)
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp powerBound

/-- A binary expansion with at least two set bits represents a nontrivial
order, so the standard fixed-width modular recovery specification applies. -/
theorem binaryExpansion_two_le (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) : 2 ≤ P.order := by
  have lastPositive : 1 ≤ B.last := by
    have firstBeforeLast :
        (0 : Fin (B.s + 1)) < Fin.last B.s := by
      change 0 < B.s
      have sPositive := B.s_pos
      omega
    have strict := B.ell_strict firstBeforeLast
    unfold UniformSuperposition.BinaryExpansion.last
    omega
  have highestTerm : 2 ^ B.last ≤ P.order := by
    calc
      2 ^ B.last ≤ ∑ index, 2 ^ B.ell index := by
        unfold UniformSuperposition.BinaryExpansion.last
        exact Finset.single_le_sum
          (fun index
              (_member : index ∈ (Finset.univ : Finset (Fin (B.s + 1)))) =>
            Nat.zero_le (2 ^ B.ell index))
          (Finset.mem_univ (Fin.last B.s))
      _ = P.order := B.sum_powers.symm
  have twoLeHighest : 2 ^ 1 ≤ 2 ^ B.last :=
    Nat.pow_le_pow_right (by norm_num) lastPositive
  norm_num at twoLeHighest
  exact twoLeHighest.trans highestTerm

/-- The Algorithm-1 target vector is definitionally the range-uniform vector
used by the established Born analysis, after unfolding their two local names
for the same reciprocal square-root amplitude. -/
theorem uniformState_eq_rangeUniformState (order width : Nat)
    (order_pos : 0 < order) (fits : order ≤ 2 ^ width) :
    UniformSuperposition.uniformState order width order_pos fits =
      rangeUniformState order width order_pos fits := by
  apply NormalizedVector.ext
  intro index
  simp only [UniformSuperposition.uniformState_apply, rangeUniformState_apply]
  rfl

/-! ## Literal preparation and analytical bridge -/

/-- The source Algorithm-1 circuit, padded only by high zero wires to the
oversampled Fourier width used by the finite-cyclic DLP experiment. -/
def paddedPreparation (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) :
    UnitaryCircuit (Qubits (orderWidth P)) :=
  B.algorithm1CircuitPadded (binaryExpansion_width_le_orderWidth P B)

@[simp]
theorem paddedPreparation_physical_idx (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) :
    (paddedPreparation P B).physical_idx = List.range (orderWidth P) := by
  exact B.algorithm1CircuitPadded_physical_idx
    (binaryExpansion_width_le_orderWidth P B)

/-- The padded literal circuit prepares exactly the range-uniform exponent
state consumed by the established finite-cyclic DLP Born analysis. -/
theorem paddedPreparation_apply_zero (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) :
    (paddedPreparation P B).applyNormalized
        (NormalizedVector.ket (R := Qubits (orderWidth P)) 0) =
      BornBridge.exponentState P := by
  rw [paddedPreparation,
    B.algorithm1CircuitPadded_apply_zero
      (binaryExpansion_width_le_orderWidth P B)]
  exact uniformState_eq_rangeUniformState P.order (orderWidth P)
    P.order_pos (order_le_fourierModulus P)

end

end QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt
