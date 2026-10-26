/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Fourier.Probability
import all QuantumAlg.Core.Base.State.Density.Vector.Unitary

/-!
# Complete coherent Fourier slices of the original branch effect

The original group-output experiment is partitioned only by its two emitted
frequencies. Each slice retains the full group label and external Reference,
so its squared norm includes every colliding branch cross term. The source
vector keeps its original subnormalization, including zero.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open FiniteCyclicDLP ConcreteCircuitAccess
open scoped BigOperators

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private def readoutCoordinates (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (Reference : Register) :
    ((idealBranchRegister problem).Index × ((idealGroupRegister problem seed).prod
      Reference).Index) ≃
      (((Qubits (orderWidth problem + orderWidth problem)).prod
        (idealGroupRegister problem seed)).prod Reference).Index where
  toFun label :=
    (((prodEquiv (m := orderWidth problem) (n := orderWidth problem)) label.1,
      label.2.1), label.2.2)
  invFun label :=
    ((prodEquiv (m := orderWidth problem) (n := orderWidth problem)).symm label.1.1,
      label.1.2, label.2)
  left_inv := by
    rintro ⟨frequency, group, reference⟩
    exact congrArg (fun original => (original, group, reference))
      ((prodEquiv (m := orderWidth problem) (n := orderWidth problem)).symm_apply_apply
        frequency)
  right_inv := by
    rintro ⟨⟨frequency, group⟩, reference⟩
    exact congrArg (fun original => ((original, group), reference))
      ((prodEquiv (m := orderWidth problem) (n := orderWidth problem)).apply_symm_apply
        frequency)

/-- One original frequency slice retains the entire coherent group and Reference vector. -/
def idealReadoutSlice (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    (Reference : Register)
    (state : HilbertVector (((Qubits (orderWidth problem + orderWidth problem)).prod
      (idealGroupRegister problem seed)).prod Reference))
    (frequency : (idealBranchRegister problem).Index) :
    HilbertVector ((idealGroupRegister problem seed).prod Reference) :=
  WithLp.toLp 2 fun label => state
    (((prodEquiv (m := orderWidth problem) (n := orderWidth problem)) frequency,
      label.1), label.2)

/-- A raw-vector readout weight is the sum of its complete coherent frequency-slice weights. -/
lemma idealReadoutEffect_weight_slices (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (Reference : Register)
    (state : HilbertVector (((Qubits (orderWidth problem + orderWidth problem)).prod
      (idealGroupRegister problem seed)).prod Reference)) (bounded : ‖state‖ ≤ 1) :
    (idealReadoutEffect problem seed event Reference).weight
        (DensityOperator.ofSubnormalizedVector state bounded) =
      ∑ frequency : (idealBranchRegister problem).Index,
        if event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
            frequency) = true then
          ‖idealReadoutSlice problem seed Reference state frequency‖ ^ 2 else 0 := by
  rw [idealReadoutEffect_weight_subnormalized,
    ← Equiv.sum_comp (readoutCoordinates problem seed Reference), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro frequency _
  have unpacked :=
    (prodEquiv (m := orderWidth problem) (n := orderWidth problem)).symm_apply_apply
      frequency
  change (∑ label : ((idealGroupRegister problem seed).prod Reference).Index,
    if event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
        ((prodEquiv (m := orderWidth problem) (n := orderWidth problem)).symm
          ((prodEquiv (m := orderWidth problem) (n := orderWidth problem)) frequency))) = true
      then ‖state (((prodEquiv (m := orderWidth problem) (n := orderWidth problem))
        frequency, label.1), label.2)‖ ^ 2 else 0) = _
  rw [unpacked]
  by_cases accepted : event
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) frequency) = true
  · simp only [if_pos accepted]
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  · simp only [if_neg accepted, Finset.sum_const_zero]

/-- The original branch effect keeps exactly those same slice norms after its actual unitary. -/
lemma idealBranchEffect_weight_slices (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (Reference : Register)
    (state : HilbertVector ((idealBranchRegister problem).prod Reference))
    (bounded : ‖state‖ ≤ 1) :
    (idealBranchEffect problem seed event Reference).weight
        (DensityOperator.ofSubnormalizedVector state bounded) =
      ∑ frequency : (idealBranchRegister problem).Index,
        if event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
            frequency) = true then
          ‖idealReadoutSlice problem seed Reference
            ((idealReadoutOperator problem seed Reference).applyVec
              (Effect.extensionVector (idealOracleEmbedding problem seed Reference) state))
            frequency‖ ^ 2 else 0 := by
  rw [idealBranchEffect_weight, ← DensityOperator.ofSubnormalizedVector_apply]
  exact idealReadoutEffect_weight_slices problem seed event Reference
    ((idealReadoutOperator problem seed Reference).applyVec
      (Effect.extensionVector (idealOracleEmbedding problem seed Reference) state))
    (by
      rw [UnitaryOperator.norm_applyVec,
        Effect.norm_extensionVector _ (idealOracleEmbedding_injective problem seed Reference)]
      exact bounded)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
