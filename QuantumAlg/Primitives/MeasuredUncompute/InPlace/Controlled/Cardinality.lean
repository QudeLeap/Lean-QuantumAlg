/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Resources

/-!
# Scalar coordinates of the controlled measured arithmetic allowance

The same independent native pools have explicit cardinalities. Quantum
control preserves cardinality while changing labels. Each complete body
charges two shared EEA passes, three variable product passes, all retained
measurement operations, both selected phase corrections and the final swap.
These are allowance identities, not claims that every branch attains them.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceControlled

noncomputable section

open MAU.Multiplication MAU.Inversion.SharedEEA

private theorem controlled_card (dimension : Nat) (pool : ResourcePool .quantum) :
    (ResourcePool.controlForDimension dimension pool).card = pool.card :=
  Multiset.card_map _ _

private theorem primitive_card : EncodedBit.GateSpec.primitiveAlphabet.card = 3 := rfl

private theorem offset_card : MAU.Addition.Gidney.offsetAlphabet.card = 6 := by
  rw [MAU.Addition.Gidney.offsetAlphabet, Multiset.card_add, controlled_card, primitive_card]

private theorem variable_card (width : Nat) :
    (VariableGidney.nativeBudget width).card = 6 * VariableGidney.eventBound width := by
  simp only [VariableGidney.nativeBudget, VariableGidney.stageBudget, Multiset.card_nsmul,
    controlled_card, Accumulate.Gidney.nativeBudget, Accumulate.Gidney.nativeAlphabet,
    offset_card, VariableGidney.eventBound]
  ring

private theorem inverse_card (width : Nat) :
    (NativeBudget.inPlace width).card = 6 * ForwardResources.inPlaceBound width := by
  simp only [NativeBudget.inPlace, Multiset.card_nsmul, offset_card]
  omega

private theorem correction_card (width : Nat) :
    (NativeProductCorrection.nativeBudget width).card =
      12 * VariableGidney.eventBound width + width := by
  simp only [NativeProductCorrection.nativeBudget, Multiset.card_add, Multiset.card_nsmul,
    variable_card, ResourcePool.singleton, Multiset.card_replicate]
  ring

/-- Both original operations have the same complete independent native-pool cardinality. -/
theorem controlledMeasuredArithmetic_budget_card (operation : InPlaceTarget.Operation)
    (width : Nat) :
    (events operation width).card = 12 * ForwardResources.inPlaceBound width +
      18 * VariableGidney.eventBound width + 9 * width := by
  cases operation <;>
    simp only [events, beforeBudget, afterBudget, saveBudget, correctionBudget,
      copyBudget, maskBudget, NumeratorReset.budget, Multiset.card_add,
      Multiset.card_nsmul, controlled_card, inverse_card, variable_card, correction_card,
      ResourcePool.singleton, Multiset.card_replicate] <;> ring

/-- The original parallel Hadamard layer contributes one unit to the serial depth allowance. -/
theorem controlledMeasuredArithmetic_depthBound_eq (operation : InPlaceTarget.Operation)
    (width : Nat) :
    depthBound operation width = 12 * ForwardResources.inPlaceBound width +
      18 * VariableGidney.eventBound width + 8 * width + 1 := by
  cases operation <;>
    simp only [depthBound, beforeBudget, afterBudget, saveBudget, correctionBudget,
      copyBudget, maskBudget, Multiset.card_add, Multiset.card_nsmul,
      controlled_card, inverse_card, variable_card, correction_card,
      ResourcePool.singleton, Multiset.card_replicate] <;> ring

end

end QuantumAlg.MeasuredUncompute.InPlaceControlled
