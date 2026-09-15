/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Support
import all QuantumAlg.Core.Base.Gate.Effect.Extension

/-!
# Actual initialized output coordinates of the Montgomery scalar target

The actual initialization embedding inserts precisely the charged auxiliary
and selector bases, keeping every supplied coordinate and reference label.
Its full rank-one density is the actual initialized density. The placed scalar
target then has the exact original-admissible branch action on the allocated
context, without changing any complex amplitude or adding a circuit.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open ScalarMultiplication.MeasuredPlacement.Encoding
open MAU.Inversion.SharedEEA GenericPointAddition.InPlace

/-- Actual initialization inserts its two fixed factors and retains the complete old reference. -/
def initializedOutputEmbedding (modulus count : Nat) (Reference : Register) :
    (Register.prod (before modulus.size count).register Reference).Index →
      (Register.prod (after modulus.size count).register Reference).Index :=
  fun input => initializedJointAssembly modulus count Reference
    ((BasisPreparation.zero (indexedLayout modulus.size count)).value,
      (InPlacePreparation.preparation modulus).value, input)

/-- The complete original input is retained injectively by actual initialization. -/
theorem initializedOutputEmbedding_injective (modulus count : Nat) (Reference : Register) :
    Function.Injective (initializedOutputEmbedding modulus count Reference) := by
  intro left right same
  exact congrArg (fun label => label.2.2)
    ((initializedJointAssembly modulus count Reference).injective same)

/-- Ready-context coordinates and allocated output coordinates denote the same initialized basis. -/
theorem initializedOutputEmbedding_ready (modulus count : Nat) (Reference : Register)
    (input : (Register.prod (before modulus.size count).register Reference).Index) :
    ContextPermutation.referenceBasis (body_entries modulus.size count) Reference
      (initializedReadyBasis modulus count input.1, input.2) =
      initializedOutputEmbedding modulus count Reference input := by
  change ((ContextPermutation.basis (body_entries modulus.size count))
    ((ContextPermutation.basis (body_entries modulus.size count)).symm
      (initializedAssembly modulus count
        ((BasisPreparation.zero (indexedLayout modulus.size count)).value,
          (InPlacePreparation.preparation modulus).value, input.1))), input.2) = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem extensionVector_twoFixed_entry {A B R S : Register}
    (coordinates : (Register.prod A (Register.prod B R)).Index ≃ S.Index)
    (fixedA : A.Index) (fixedB : B.Index) (vector : HilbertVector R)
    (labelA : A.Index) (labelB : B.Index) (input : R.Index) :
    Effect.extensionVector (fun original => coordinates (fixedA, fixedB, original)) vector
      (coordinates (labelA, labelB, input)) =
      (NormalizedVector.ket fixedA).vec labelA *
        (NormalizedVector.ket fixedB).vec labelB * vector input := by
  classical
  rw [Effect.extensionVector_apply]
  have labels (original : R.Index) :
      coordinates (fixedA, fixedB, original) = coordinates (labelA, labelB, input) ↔
        fixedA = labelA ∧ fixedB = labelB ∧ original = input := by
    rw [coordinates.injective.eq_iff]
    change (fixedA, fixedB, original) = (labelA, labelB, input) ↔ _
    simp only [Prod.mk.injEq]
  simp only [labels]
  by_cases first : fixedA = labelA
  · by_cases second : fixedB = labelB
    · simp [NormalizedVector.ket_apply, first, second]
    · simp [NormalizedVector.ket_apply, first, second, Ne.symm second]
  · simp [NormalizedVector.ket_apply, first, Ne.symm first]

/-- Every initialized vector amplitude has exactly the actual fixed preparation factors. -/
theorem initializedOutputVector_entry (modulus count : Nat) (Reference : Register)
    (vector : HilbertVector (Register.prod (before modulus.size count).register Reference))
    (selector : (indexedLayout modulus.size count).register.Index)
    (auxiliary : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (input : (Register.prod (before modulus.size count).register Reference).Index) :
    Effect.extensionVector (initializedOutputEmbedding modulus count Reference) vector
      (initializedJointAssembly modulus count Reference (selector, auxiliary, input)) =
      (BasisPreparation.zero (indexedLayout modulus.size count)).normalized.vec selector *
        (InPlacePreparation.preparation modulus).normalized.vec auxiliary * vector input := by
  exact extensionVector_twoFixed_entry (initializedJointAssembly modulus count Reference)
    (BasisPreparation.zero (indexedLayout modulus.size count)).value
    (InPlacePreparation.preparation modulus).value vector selector auxiliary input

/-- Full coherent subnormalized initialization is exactly the actual injected rank-one density. -/
theorem initializedDensity_subnormalizedVector (modulus count : Nat) (Reference : Register)
    (vector : HilbertVector (Register.prod (before modulus.size count).register Reference))
    (bounded : ‖vector‖ ≤ 1) :
    initializedDensity modulus count Reference
      (DensityOperator.ofSubnormalizedVector vector bounded) =
      DensityOperator.ofSubnormalizedVector
        (Effect.extensionVector (initializedOutputEmbedding modulus count Reference) vector)
        (by
          rw [Effect.norm_extensionVector _ (initializedOutputEmbedding_injective _ _ _)]
          exact bounded) := by
  apply DensityOperator.ext
  ext row column
  obtain ⟨⟨selectorRow, auxiliaryRow, originalRow⟩, rfl⟩ :=
    (initializedJointAssembly modulus count Reference).surjective row
  obtain ⟨⟨selectorColumn, auxiliaryColumn, originalColumn⟩, rfl⟩ :=
    (initializedJointAssembly modulus count Reference).surjective column
  have entry := initializedDensity_entry modulus count Reference
    (DensityOperator.ofSubnormalizedVector vector bounded)
    selectorRow selectorColumn auxiliaryRow auxiliaryColumn originalRow originalColumn
  refine entry.trans ?_
  rw [DensityOperator.ofSubnormalizedVector_matrix,
    DensityOperator.ofSubnormalizedVector_matrix,
    initializedOutputVector_entry, initializedOutputVector_entry]
  simp only [star_mul]
  ring

/-- Every original admissible branch has its exact Montgomery output on the allocated context. -/
theorem placedConvertedTarget_pairedMontgomery {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) {exponentWidth : Nat}
    (points : Fin (2 * exponentWidth) → AffinePoint E) (seed : AffinePoint E)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (admissible : ExceptionalOffsetAveraging.Admissible (2 * exponentWidth)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth)
      (fun index => (points index).toGroupPoint) seed.toGroupPoint branch)
    {Reference : Register} (reference : Reference.Index) :
    (placedConvertedTarget E points (List.finRange (2 * exponentWidth))
      (Semantics.radixUnit p fieldTail.succ odd) Reference).applyVec
        (NormalizedVector.ket (initializedOutputEmbedding p (2 * exponentWidth) Reference
          (pairedMontgomeryInput fieldTail exponentWidth sameWidth fits seed branch,
            reference))).vec =
      (NormalizedVector.ket (initializedOutputEmbedding p (2 * exponentWidth) Reference
        (pairedMontgomeryInput fieldTail exponentWidth sameWidth fits
          (ScalarMultiplication.AffineTrajectory.path E points
            (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch)
            (List.finRange (2 * exponentWidth)) seed) branch, reference))).vec := by
  have original := convertedCascadeTarget_pairedMontgomeryInput E fieldTail sameWidth fits odd
    points seed branch admissible reference
  have placed := MeasuredPointAddition.operator_reindex_ket
    (ContextPermutation.referenceBasis (body_entries p.size (2 * exponentWidth)) Reference)
    _ _ _ original
  rw [← initializedOutputEmbedding_ready p (2 * exponentWidth) Reference
    (pairedMontgomeryInput fieldTail exponentWidth sameWidth fits seed branch, reference),
    ← initializedOutputEmbedding_ready p (2 * exponentWidth) Reference
      (pairedMontgomeryInput fieldTail exponentWidth sameWidth fits
        (ScalarMultiplication.AffineTrajectory.path E points
          (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch)
          (List.finRange (2 * exponentWidth)) seed) branch, reference)]
  exact placed

/-- The same allocated column denotes the original offset and two-exponent group value. -/
theorem placedConvertedTarget_pairedMontgomery_group {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    {exponentWidth : Nat} (points : Fin (2 * exponentWidth) → AffinePoint E)
    (seed : AffinePoint E) (leftBase rightBase : E.GroupPoint)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend exponentWidth leftBase rightBase)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (admissible : ExceptionalOffsetAveraging.Admissible (2 * exponentWidth)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth)
      (fun index => (points index).toGroupPoint) seed.toGroupPoint branch)
    {Reference : Register} (reference : Reference.Index) :
    ∃ final : AffinePoint E,
      final.toGroupPoint =
        seed.toGroupPoint * (leftBase ^ branch.1.val * (rightBase ^ branch.2.val)⁻¹) ∧
      (placedConvertedTarget E points (List.finRange (2 * exponentWidth))
        (Semantics.radixUnit p fieldTail.succ odd) Reference).applyVec
          (NormalizedVector.ket (initializedOutputEmbedding p (2 * exponentWidth) Reference
            (pairedMontgomeryInput fieldTail exponentWidth sameWidth fits seed branch,
              reference))).vec =
        (NormalizedVector.ket (initializedOutputEmbedding p (2 * exponentWidth) Reference
          (pairedMontgomeryInput fieldTail exponentWidth sameWidth fits final branch,
            reference))).vec := by
  obtain ⟨final, value, original⟩ := convertedCascadeTarget_pairedMontgomery_group E fieldTail
    sameWidth fits odd points seed leftBase rightBase addends branch admissible reference
  refine ⟨final, value, ?_⟩
  have placed := MeasuredPointAddition.operator_reindex_ket
    (ContextPermutation.referenceBasis (body_entries p.size (2 * exponentWidth)) Reference)
    _ _ _ original
  rw [← initializedOutputEmbedding_ready p (2 * exponentWidth) Reference
    (pairedMontgomeryInput fieldTail exponentWidth sameWidth fits seed branch, reference),
    ← initializedOutputEmbedding_ready p (2 * exponentWidth) Reference
      (pairedMontgomeryInput fieldTail exponentWidth sameWidth fits final branch, reference)]
  exact placed

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
