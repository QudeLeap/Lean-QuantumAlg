/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Frequency

/-!
# Orthogonality of both complete native inverse Fourier frequency columns

The actual fullRows use the certified complete native inverse circuit, including
its physical swaps. Its column Gram gives the one-block identity. The product
of the second and first block rows has the full two-block column identity.

All frequency labels and all recursive source tuples are retained, including
zero width. These are mathematical identities of the existing native Fourier
rows; no register, execution step, packing instruction or caller premise is
introduced. Actual point words and legal path identification remain separate.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace FullFrequencyOrthogonality

noncomputable section

open QuantumAlg QuantumAlg.QuantumFourierTransform
open QuantumFourierTransform.Semiclassical
open scoped BigOperators

private lemma unitary_columns {R : Register} (operator : UnitaryOperator R)
    (source target : R.Index) :
    (∑ frequency, star (operator frequency source) * operator frequency target) =
      if source = target then 1 else 0 := by
  have gram : (operator : HilbertOperator R).conjTranspose *
      (operator : HilbertOperator R) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp operator.property
  have entry := congrArg (fun matrix : HilbertOperator R => matrix source target) gram
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using entry

/-- Every full canonical inverse frequency is summed once, at every width. -/
lemma fullRows_orthogonal (m : Nat) (source target : Bits m) :
    (∑ frequency : Fin (2 ^ m),
      star (Partner.fullRows true m frequency source) *
        Partner.fullRows true m frequency target) =
      if source = target then 1 else 0 := by
  simpa only [Partner.fullRows, if_true, Equiv.apply_eq_iff_eq] using
    unitary_columns (R := Qubits m)
      (Native.onBinaryLabels (Native.inverseCircuit .empty m) OracleModel.emptyInterpretation)
      (binaryEquiv m source) (binaryEquiv m target)

/-- The scalar order is exactly the second physical block times the first physical block. -/
def pairRows (m : Nat) (frequency : Fin (2 ^ m) × Fin (2 ^ m))
    (source : Bits m × Bits m) : ℂ :=
  Partner.fullRows true m frequency.2 source.2 *
    Partner.fullRows true m frequency.1 source.1

/-- Complete two-block frequency summation removes every distinct-source Gram entry. -/
lemma pairRows_orthogonal (m : Nat) (source target : Bits m × Bits m) :
    (∑ frequency : Fin (2 ^ m) × Fin (2 ^ m),
      star (pairRows m frequency source) * pairRows m frequency target) =
      if source = target then 1 else 0 := by
  calc
    _ = ∑ first : Fin (2 ^ m), ∑ second : Fin (2 ^ m),
        (star (Partner.fullRows true m first source.1) *
          Partner.fullRows true m first target.1) *
        (star (Partner.fullRows true m second source.2) *
          Partner.fullRows true m second target.2) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      dsimp only [pairRows]
      rw [star_mul]
      ring
    _ = (∑ first : Fin (2 ^ m), star (Partner.fullRows true m first source.1) *
          Partner.fullRows true m first target.1) *
        (∑ second : Fin (2 ^ m), star (Partner.fullRows true m second source.2) *
          Partner.fullRows true m second target.2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro first _
      rw [Finset.mul_sum]
    _ = _ := by
      rw [fullRows_orthogonal, fullRows_orthogonal]
      by_cases first : source.1 = target.1
      · by_cases second : source.2 = target.2
        · have same : source = target := Prod.ext first second
          rw [if_pos first, if_pos second, if_pos same, one_mul]
        · have distinct : source ≠ target := fun same => second (congrArg Prod.snd same)
          rw [if_pos first, if_neg second, if_neg distinct, mul_zero]
      · have distinct : source ≠ target := fun same => first (congrArg Prod.fst same)
        rw [if_neg first, if_neg distinct, zero_mul]

end

end FullFrequencyOrthogonality
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
