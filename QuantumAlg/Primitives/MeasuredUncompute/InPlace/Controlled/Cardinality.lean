/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Resources

/-!
# Scalar coordinates of the controlled measured arithmetic allowance

The independent pools charge literal controlled-gate expansion and the
actual H-CNOT-H phase sequences. Each complete body allows two shared EEA
passes, one controlled product pass, two unconditional product passes, all
measurement operations, both selected phase corrections, and the final swap.
These are allowance identities, not claims that every branch attains them.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceControlled

noncomputable section

open MAU.Multiplication MAU.Inversion.SharedEEA

private theorem primitive_card : EncodedBit.GateSpec.primitiveAlphabet.card = 3 := rfl

private theorem variable_card (width : Nat) :
    (VariableGidney.nativeBudget width).card = 3 * VariableGidney.eventBound width := by
  simp only [VariableGidney.nativeBudget, VariableGidney.stageBudget, Multiset.card_nsmul,
    primitive_card, VariableGidney.eventBound]
  ring

private theorem controlled_card (count : Nat) :
    (controlledBudget count true).card = 5 * count := by
  simp only [controlledBudget, ↓reduceIte, Multiset.card_add,
    Multiset.card_nsmul, ResourcePool.singleton, Multiset.card_replicate]
  omega

/-- Both original operations have the same complete independent native-pool cardinality. -/
theorem controlledMeasuredArithmetic_budget_card (operation : InPlaceTarget.Operation)
    (width : Nat) :
    (events operation width).card = 10 * ForwardResources.inPlaceBound width +
      11 * VariableGidney.eventBound width + 13 * width + 4 := by
  cases operation <;>
    simp only [events, beforeBudget, afterBudget, saveBudget, correctionBudget,
      copyBudget, maskBudget, NumeratorReset.budget, Multiset.card_add,
      Multiset.card_nsmul, controlled_card, variable_card,
      ResourcePool.singleton, Multiset.card_replicate] <;> ring

/-- The original parallel Hadamard layer contributes one unit to the serial depth allowance. -/
theorem controlledMeasuredArithmetic_depthBound_eq (operation : InPlaceTarget.Operation)
    (width : Nat) :
    depthBound operation width = 10 * ForwardResources.inPlaceBound width +
      11 * VariableGidney.eventBound width + 12 * width + 5 := by
  cases operation <;>
    simp only [depthBound, beforeBudget, afterBudget, saveBudget, correctionBudget,
      copyBudget, maskBudget, Multiset.card_add, Multiset.card_nsmul,
      controlled_card, variable_card,
      ResourcePool.singleton, Multiset.card_replicate] <;> ring

end

end QuantumAlg.MeasuredUncompute.InPlaceControlled
