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

private theorem controlled_card (dimension : Nat) (pool : ResourcePool .quantum) :
    (ResourcePool.controlForDimension dimension pool).card = pool.card :=
  Multiset.card_map _ _

private theorem offset_card : MAU.Addition.Gidney.offsetAlphabet.card = 6 := by
  rw [MAU.Addition.Gidney.offsetAlphabet, Multiset.card_add, controlled_card]
  rfl

private theorem primitive_card : EncodedBit.GateSpec.primitiveAlphabet.card = 3 := rfl

private theorem variable_card (width : Nat) :
    (MAU.Multiplication.VariableGidney.nativeBudget width).card =
      6 * MAU.Multiplication.VariableGidney.eventBound width := by
  simp only [MAU.Multiplication.VariableGidney.nativeBudget,
    MAU.Multiplication.VariableGidney.stageBudget, Multiset.card_nsmul, controlled_card,
    MAU.Multiplication.Accumulate.Gidney.nativeBudget,
    MAU.Multiplication.Accumulate.Gidney.nativeAlphabet, offset_card,
    MAU.Multiplication.VariableGidney.eventBound]
  ring

/-- The original five-stage independent event allowance has this scalar cardinality. -/
theorem measuredPointAddition_budget_card (width : Nat) :
    (events width).card = 24 * ForwardResources.inPlaceBound width +
      42 * MAU.Multiplication.VariableGidney.eventBound width +
      36 * MAU.Addition.Gidney.modularOffsetEventBound width +
      6 * MAU.Addition.Gidney.pivotEventBound width +
      6 * MAU.Addition.Gidney.comparisonEventBound width + 20 * width + 8 := by
  simp only [events, Multiset.card_add,
    InPlaceControlled.controlledMeasuredArithmetic_budget_card]
  simp only [beforeBudget, middleBudget, afterBudget, offsetBudget, squareBudget,
    selectorBudget, comparisonBudget, pivotBudget, cnotBudget, Multiset.card_add,
    Multiset.card_nsmul, controlled_card, variable_card,
    MAU.Addition.Gidney.modularOffsetNativeBudget, offset_card, primitive_card,
    ResourcePool.singleton, Multiset.card_replicate]
  ring

/-- The same serial depth allowance retains the parallel Hadamards inside each measured call. -/
theorem measuredPointAddition_depthBound_eq (width : Nat) :
    depthBound width = 24 * ForwardResources.inPlaceBound width +
      37 * MAU.Multiplication.VariableGidney.eventBound width +
      6 * MAU.Addition.Gidney.modularOffsetEventBound width +
      MAU.Addition.Gidney.pivotEventBound width +
      2 * MAU.Addition.Gidney.comparisonEventBound width + 18 * width + 10 := by
  simp only [depthBound, InPlaceControlled.controlledMeasuredArithmetic_depthBound_eq]
  ring

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
