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

open Execution Modular.Reduce.Native

private lemma max_card_le_add {model : ExecutionModel} (left right : ResourcePool model) :
    (ResourcePool.max left right).card ≤ left.card + right.card :=
  (Multiset.card_le_card (Multiset.union_le_add left right)).trans_eq
    (Multiset.card_add left right)

/-- Both original branch sites fit the same constant sixteen-instruction allowance. -/
lemma signedReductionEnvelope_card_le (model : ExecutionModel) [BitWord.Selected model] (width
  : Nat) :
    (signedReductionEnvelope model width).card ≤ 16 := by
  have magnitude :
      (ResourcePool.max (ResourcePool.ofList (signedMagnitudeEvents model width true))
        (ResourcePool.ofList (signedMagnitudeEvents model width false))).card ≤ 4 :=
    (max_card_le_add _ _).trans_eq (by rfl)
  have correction :
      (ResourcePool.max (ResourcePool.ofList (finalCorrectionEvents model width true))
        (ResourcePool.ofList (finalCorrectionEvents model width false))).card ≤ 5 :=
    (max_card_le_add _ _).trans_eq (by rfl)
  unfold signedReductionEnvelope
  simp only [Multiset.card_add]
  change 5 + _ + 2 + _ ≤ 16
  omega

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
