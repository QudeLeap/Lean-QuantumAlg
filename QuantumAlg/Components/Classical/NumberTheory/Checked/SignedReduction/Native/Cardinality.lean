/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Bounds

/-!
# Cardinality of actual signed reduction

The original two coordinatewise branch maxima remain unchanged. Their sizes
are bounded by the sum of both branch sizes, not by a maximum of those sizes.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native

open Modular.Reduce.Native

private theorem max_card_le_add {kind : ProblemKind} (left right : ResourcePool kind) :
    (ResourcePool.max left right).card ≤ left.card + right.card :=
  (Multiset.card_le_card (Multiset.union_le_add left right)).trans_eq
    (Multiset.card_add left right)

/-- Both original branch sites fit the same constant sixteen-instruction allowance. -/
theorem signedReductionEnvelope_card_le (kind : ProblemKind) (width : Nat) :
    (signedReductionEnvelope kind width).card ≤ 16 := by
  have magnitude :
      (ResourcePool.max (ResourcePool.ofList (signedMagnitudeEvents kind width true))
        (ResourcePool.ofList (signedMagnitudeEvents kind width false))).card ≤ 4 :=
    (max_card_le_add _ _).trans_eq (by rfl)
  have correction :
      (ResourcePool.max (ResourcePool.ofList (finalCorrectionEvents kind width true))
        (ResourcePool.ofList (finalCorrectionEvents kind width false))).card ≤ 5 :=
    (max_card_le_add _ _).trans_eq (by rfl)
  unfold signedReductionEnvelope
  simp only [Multiset.card_add]
  change 5 + _ + 2 + _ ≤ 16
  omega

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
