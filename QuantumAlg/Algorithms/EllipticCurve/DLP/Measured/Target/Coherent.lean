/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Target
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Support.Input

/-!
# Complete coherent good output of the actual allocated scalar target

Every original good branch and every reference amplitude is carried to the
exact allocated Montgomery output label. The resulting vector retains all
complex cross terms and its original subnormalization. Actual initialized
converted execution has precisely this rank-one density.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open ScalarMultiplication.MeasuredPlacement.Encoding
open GenericPointAddition.InPlace FiniteCyclicDLP

private def extensionLinear {R S : Register} (embedding : S.Index → R.Index) :
    HilbertVector S →ₗ[ℂ] HilbertVector R where
  toFun := Effect.extensionVector embedding
  map_add' left right := by
    simp [Effect.extensionVector, PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' scalar vector := by
    simp [Effect.extensionVector, PiLp.smul_apply, smul_smul, Finset.smul_sum]

private theorem extensionVector_sum {R S : Register} (embedding : S.Index → R.Index)
    {Index : Type} (indices : Finset Index) (vectors : Index → HilbertVector S) :
    Effect.extensionVector embedding (∑ index ∈ indices, vectors index) =
      ∑ index ∈ indices, Effect.extensionVector embedding (vectors index) :=
  map_sum (extensionLinear embedding) vectors indices

private theorem extensionVector_smul {R S : Register} (embedding : S.Index → R.Index)
    (scalar : ℂ) (vector : HilbertVector S) :
    Effect.extensionVector embedding (scalar • vector) =
      scalar • Effect.extensionVector embedding vector :=
  (extensionLinear embedding).map_smul scalar vector

private theorem extensionVector_ket {R S : Register} (embedding : S.Index → R.Index)
    (input : S.Index) :
    Effect.extensionVector embedding (NormalizedVector.ket input).vec =
      (NormalizedVector.ket (embedding input)).vec := by
  classical
  simp [Effect.extensionVector, NormalizedVector.ket_apply]

private theorem referenceFrame_sum_ket {R Reference : Register} {Branch : Type}
    (branches : Finset Branch) (source : Branch → R.Index) (amplitude : Branch → ℂ)
    (reference : HilbertVector Reference) :
    referenceFrame (∑ branch ∈ branches,
      amplitude branch • (NormalizedVector.ket (source branch) : HilbertVector R)) reference =
      ∑ branch ∈ branches, ∑ label : Reference.Index,
        (amplitude branch * reference label) •
          (NormalizedVector.ket (R := Register.prod R Reference) (source branch, label)).vec := by
  classical
  apply WithLp.ofLp_injective
  funext output
  have paired (branch : Branch) (label : Reference.Index) :
      output = (source branch, label) ↔ output.1 = source branch ∧ output.2 = label := by
    change (output.1, output.2) = (source branch, label) ↔ _
    simp only [Prod.mk.injEq]
  simp only [referenceFrame_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul, NormalizedVector.ket_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_mul, ite_mul, zero_mul, paired]
  apply Finset.sum_congr rfl
  intro branch _
  by_cases same : output.1 = source branch <;> simp [same]

private theorem unitary_finite_sum {R : Register} (operator : UnitaryOperator R)
    {Index : Type} (indices : Finset Index) (vectors : Index → HilbertVector R) :
    operator.applyVec (∑ index ∈ indices, vectors index) =
      ∑ index ∈ indices, operator.applyVec (vectors index) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      apply WithLp.ofLp_injective
      funext label
      simp [UnitaryOperator.applyVec, HilbertOperator.applyVec_apply]
  | @insert index indices absent induction =>
      simp only [Finset.sum_insert absent, UnitaryOperator.applyVec_add, induction]

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]

/-- The full scalar output keeps every original good-branch and coherent reference amplitude. -/
def convertedGoodVector (problem : KnownOrderProblem (GroupPoint E)) (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    HilbertVector (Register.prod (after p.size (2 * orderWidth problem)).register Reference) :=
  ∑ branch ∈ preparedAdmissibleBranches problem points seed, ∑ label : Reference.Index,
    (preparedBranchAmplitude problem branch * reference label) •
      (NormalizedVector.ket (initializedOutputEmbedding p (2 * orderWidth problem) Reference
        (pairedMontgomeryInput fieldTail (orderWidth problem) sameWidth fits
          (ScalarMultiplication.AffineTrajectory.path E points
            (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) branch)
            (List.finRange (2 * orderWidth problem)) seed) branch, label)) :
        HilbertVector (Register.prod (after p.size (2 * orderWidth problem)).register Reference))

/-- Exact placed good-column actions extend to the entire coherent good vector and reference. -/
theorem placedConvertedTarget_goodVector (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (odd : Odd p) (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    (placedConvertedTarget E points (List.finRange (2 * orderWidth problem))
      (Semantics.radixUnit p fieldTail.succ odd) Reference).applyVec
        (Effect.extensionVector (initializedOutputEmbedding p (2 * orderWidth problem) Reference)
          (preparedGoodVector problem fieldTail sameWidth fits points seed reference)) =
      convertedGoodVector problem fieldTail sameWidth fits points seed reference := by
  classical
  rw [preparedGoodVector, referenceFrame_sum_ket, extensionVector_sum, unitary_finite_sum]
  apply Finset.sum_congr rfl
  intro branch member
  rw [extensionVector_sum, unitary_finite_sum]
  apply Finset.sum_congr rfl
  intro label _
  rw [extensionVector_smul, extensionVector_ket, UnitaryOperator.applyVec_smul,
    placedConvertedTarget_pairedMontgomery E fieldTail sameWidth fits odd points seed branch
      (Finset.mem_filter.mp member).2 label]

/-- The complete original good output has its original subnormalized norm. -/
theorem convertedGoodVector_norm_le_one (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (odd : Odd p) (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    ‖convertedGoodVector problem fieldTail sameWidth fits points seed reference‖ ≤ 1 := by
  rw [← placedConvertedTarget_goodVector problem fieldTail sameWidth fits odd,
    UnitaryOperator.norm_applyVec,
    Effect.norm_extensionVector _ (initializedOutputEmbedding_injective _ _ _)]
  exact preparedGoodVector_norm_le_one problem fieldTail sameWidth fits points seed reference

/-- The complete independently prescribed converted density retains all coherent good terms. -/
theorem convertedResultDensity_preparedGood (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (odd : Odd p) (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    convertedResultDensity E points (List.finRange (2 * orderWidth problem))
      (Semantics.radixUnit p fieldTail.succ odd) Reference
      (DensityOperator.ofSubnormalizedVector
        (preparedGoodVector problem fieldTail sameWidth fits points seed reference)
        (preparedGoodVector_norm_le_one problem fieldTail sameWidth fits points seed reference)) =
      DensityOperator.ofSubnormalizedVector
        (convertedGoodVector problem fieldTail sameWidth fits points seed reference)
        (convertedGoodVector_norm_le_one problem fieldTail sameWidth fits odd
          points seed reference) := by
  rw [convertedResultDensity, initializedDensity_subnormalizedVector]
  have transformed := applyUnitary_subnormalizedVector
    (placedConvertedTarget E points (List.finRange (2 * orderWidth problem))
      (Semantics.radixUnit p fieldTail.succ odd) Reference)
    (Effect.extensionVector (initializedOutputEmbedding p (2 * orderWidth problem) Reference)
      (preparedGoodVector problem fieldTail sameWidth fits points seed reference))
    (by
      rw [Effect.norm_extensionVector _ (initializedOutputEmbedding_injective _ _ _)]
      exact preparedGoodVector_norm_le_one problem fieldTail sameWidth fits points seed reference)
  apply DensityOperator.ext
  refine (congrArg DensityOperator.matrix transformed).trans ?_
  ext row column
  simp only [DensityOperator.ofSubnormalizedVector_matrix, placedConvertedTarget_goodVector]

/-- Actual initialized measured scalar execution realizes the complete coherent good density. -/
theorem convertedCircuit_goodDensity (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (odd : Odd p) (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference)
    {History : Type} [Fintype History]
    (stored : Store (before p.size (2 * orderWidth problem)))
    (hidden : ClassicalOracleModel.empty.HiddenState) (history : History) :
    ((convertedCircuit E points (List.finRange (2 * orderWidth problem))
      (Semantics.radixUnit p fieldTail.succ odd)).execute Reference
      (ExecutionState.ofValue (stored, (hidden, history)) (DensityOperator.ofSubnormalizedVector
        (preparedGoodVector problem fieldTail sameWidth fits points seed reference)
        (preparedGoodVector_norm_le_one problem fieldTail sameWidth fits
          points seed reference)))).quantumMarginal =
      DensityOperator.ofSubnormalizedVector
        (convertedGoodVector problem fieldTail sameWidth fits points seed reference)
        (convertedGoodVector_norm_le_one problem fieldTail sameWidth fits odd
          points seed reference) := by
  have supported : ∀ input :
      (Register.prod (before p.size (2 * orderWidth problem)).register Reference).Index,
      ¬pairedMontgomeryAllowed E fieldTail sameWidth fits points seed input.1 →
        (ExecutionState.ofValue (stored, (hidden, history)) (DensityOperator.ofSubnormalizedVector
          (preparedGoodVector problem fieldTail sameWidth fits points seed reference)
          (preparedGoodVector_norm_le_one problem fieldTail sameWidth fits
            points seed reference))).quantumMarginal.matrix input input = 0 := by
    rw [ExecutionState.ofValue_quantumMarginal]
    exact preparedGoodDensity_supported problem fieldTail sameWidth fits points seed reference
  rw [convertedCircuit_density_of_pairedMontgomery_admissible E fieldTail sameWidth fits odd
    points seed _ supported, ExecutionState.ofValue_quantumMarginal,
    convertedResultDensity_preparedGood]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
