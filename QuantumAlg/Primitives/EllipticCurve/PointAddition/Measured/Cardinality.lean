/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Resources
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Cardinality

/-!
# Scalar native allowances of the actual measured point addition

These identities expand the existing independent event pools and serial
depth formula. Both measured calls, every offset and selector, the square,
and the real control exchanges remain included. Pool cardinality counts
all allowed native coordinates; it is distinct from the unit-depth bound.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

noncomputable section

open MAU.Inversion.SharedEEA MeasuredUncompute

private theorem controlled_card (control : OffsetControl) (count : Nat) :
    (controlledBudget control count).card =
      match control with | .supplied => 5 * count | .exceptional => 16 * count + 2 := by
  cases control <;>
    simp only [controlledBudget, cnotBudget, Multiset.card_add, Multiset.card_nsmul,
      ResourcePool.singleton, Multiset.card_replicate] <;> ring

/-- The scalar allowance includes every literal control expansion and exceptional toggle. -/
theorem measuredPointAddition_budget_card (width : Nat) :
    (events width).card = 20 * ForwardResources.inPlaceBound width +
      27 * MAU.Multiplication.VariableGidney.eventBound width +
      41 * MAU.Addition.Gidney.modularOffsetEventBound width +
      5 * MAU.Addition.Gidney.pivotEventBound width +
      10 * MAU.Addition.Gidney.comparisonEventBound width + 28 * width + 18 := by
  simp only [events, Multiset.card_add,
    InPlaceControlled.controlledMeasuredArithmetic_budget_card]
  simp only [beforeBudget, middleBudget, afterBudget, offsetBudget, squareBudget,
    selectorBudget, comparisonBudget, pivotBudget, Multiset.card_add,
    Multiset.card_nsmul, controlled_card, cnotBudget,
    ResourcePool.singleton, Multiset.card_replicate]
  ring

/-- Accepted measured depths retain their parallel Hadamards; all native stages are serial. -/
theorem measuredPointAddition_depthBound_eq (width : Nat) :
    depthBound width = 20 * ForwardResources.inPlaceBound width +
      27 * MAU.Multiplication.VariableGidney.eventBound width +
      41 * MAU.Addition.Gidney.modularOffsetEventBound width +
      5 * MAU.Addition.Gidney.pivotEventBound width +
      10 * MAU.Addition.Gidney.comparisonEventBound width + 26 * width + 20 := by
  simp only [depthBound, InPlaceControlled.controlledMeasuredArithmetic_depthBound_eq,
    beforeBudget, middleBudget, afterBudget, offsetBudget, squareBudget,
    selectorBudget, comparisonBudget, pivotBudget, Multiset.card_add,
    Multiset.card_nsmul, controlled_card, cnotBudget,
    ResourcePool.singleton, Multiset.card_replicate]
  ring

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
