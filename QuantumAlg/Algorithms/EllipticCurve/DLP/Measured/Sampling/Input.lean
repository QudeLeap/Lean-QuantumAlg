/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Support.Input
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Target.Coherent

/-!
# The original coherent input and error in the resident sampling workspace

The existing initialization embedding places the same original input and
good component on the already allocated systems. Its original isometry
preserves normalization and the exact exceptional omitted norm. The good
density is the existing initialization target without renormalization.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open ScalarMultiplication.MeasuredPlacement.Encoding MAU.Inversion.SharedEEA
open FiniteCyclicDLP

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]

/-- The same normalized original input occupies its existing initialized coordinates. -/
def samplingInputVector (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (seed : AffinePoint E) {Reference : Register} (reference : NormalizedVector Reference) :
    NormalizedVector (Register.prod (after p.size (2 * orderWidth problem)).register Reference) :=
  NormalizedVector.ofVector
    (Effect.extensionVector (initializedOutputEmbedding p (2 * orderWidth problem) Reference)
      (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference).vec)
    (by
      rw [Effect.norm_extensionVector _ (initializedOutputEmbedding_injective _ _ _)]
      exact (originalMontgomeryInputVector problem fieldTail sameWidth fits seed
        reference).norm_eq_one)

/-- The same unrenormalized good component occupies the original fixed preparation subspace. -/
def samplingGoodVector (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    HilbertVector (Register.prod (after p.size (2 * orderWidth problem)).register Reference) :=
  Effect.extensionVector (initializedOutputEmbedding p (2 * orderWidth problem) Reference)
    (goodInputVector problem fieldTail sameWidth fits points seed reference)

/-- The original good component keeps its subnormalized bound on the resident systems. -/
theorem samplingGoodVector_norm_le_one (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    ‖samplingGoodVector problem fieldTail sameWidth fits points seed reference‖ ≤ 1 := by
  rw [samplingGoodVector,
    Effect.norm_extensionVector _ (initializedOutputEmbedding_injective _ _ _)]
  exact goodInputVector_norm_le_one problem fieldTail sameWidth fits points seed reference

/-- The resident good density is precisely the original independent initialization target. -/
theorem samplingGoodVector_density (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    DensityOperator.ofSubnormalizedVector
        (samplingGoodVector problem fieldTail sameWidth fits points seed reference)
        (samplingGoodVector_norm_le_one problem fieldTail sameWidth fits points seed reference) =
      initializedDensity p (2 * orderWidth problem) Reference
        (DensityOperator.ofSubnormalizedVector
          (goodInputVector problem fieldTail sameWidth fits points seed reference)
          (goodInputVector_norm_le_one problem fieldTail sameWidth fits points seed reference)) :=
  (initializedDensity_subnormalizedVector p (2 * orderWidth problem) Reference
    (goodInputVector problem fieldTail sameWidth fits points seed reference)
    (goodInputVector_norm_le_one problem fieldTail sameWidth fits points seed reference)).symm

/-- Reusing the initialized systems preserves the exact original exceptional omitted norm. -/
theorem norm_samplingInput_sub_good (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    ‖(samplingInputVector problem fieldTail sameWidth fits seed reference).vec -
        samplingGoodVector problem fieldTail sameWidth fits points seed reference‖ =
      Real.sqrt (preparedExceptionalMass problem points seed) := by
  change ‖Effect.extensionVector (initializedOutputEmbedding p (2 * orderWidth problem) Reference)
      (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference).vec -
    Effect.extensionVector (initializedOutputEmbedding p (2 * orderWidth problem) Reference)
      (goodInputVector problem fieldTail sameWidth fits points seed reference)‖ = _
  have subtraction :=
    (extensionLinear (initializedOutputEmbedding p (2 * orderWidth problem) Reference)).map_sub
      (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference).vec
      (goodInputVector problem fieldTail sameWidth fits points seed reference)
  change Effect.extensionVector _ _ =
    Effect.extensionVector _ _ - Effect.extensionVector _ _ at subtraction
  rw [← subtraction,
    Effect.norm_extensionVector _ (initializedOutputEmbedding_injective _ _ _)]
  exact norm_originalMontgomeryInput_sub_good problem fieldTail sameWidth fits points seed reference

/-- Every amplitude has the actual fixed local ket and the unchanged complete reference. -/
theorem samplingInputVector_entry (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (seed : AffinePoint E) {Reference : Register} (reference : NormalizedVector Reference)
    (localBasis : (after p.size (2 * orderWidth problem)).register.Index)
    (external : Reference.Index) :
    samplingInputVector problem fieldTail sameWidth fits seed reference (localBasis, external) =
      NormalizedVector.ket (R := (after p.size (2 * orderWidth problem)).register)
        (initializedAssembly p (2 * orderWidth problem)
          ((BasisPreparation.zero (indexedLayout p.size (2 * orderWidth problem))).value,
            (InPlacePreparation.preparation p).value,
            pairedMontgomeryInput fieldTail (orderWidth problem) sameWidth fits seed (0, 0)))
        localBasis * reference external := by
  obtain ⟨⟨selector, auxiliary, original⟩, rfl⟩ :=
    (initializedAssembly p (2 * orderWidth problem)).surjective localBasis
  change Effect.extensionVector _ _
    (initializedJointAssembly p (2 * orderWidth problem) Reference
      (selector, auxiliary, original, external)) = _
  rw [initializedOutputVector_entry]
  simp only [BasisPreparation.normalized, NormalizedVector.ket_apply,
    originalMontgomeryInputVector, normalizedReferenceFrame, NormalizedVector.ofVector,
    referenceFrame_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases first : selector =
      (BasisPreparation.zero (indexedLayout p.size (2 * orderWidth problem))).value <;>
    by_cases second : auxiliary = (InPlacePreparation.preparation p).value <;>
      by_cases third : original =
          pairedMontgomeryInput fieldTail (orderWidth problem) sameWidth fits seed (0, 0) <;>
        simp [first, second, third]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
