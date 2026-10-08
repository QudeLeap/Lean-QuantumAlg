/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Cardinality
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Cardinality
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Cardinality

/-!
# Cardinality of actual checked inversion

One actual modulus loader, widening, raw XGCD, gcd-one decision and selected
signed reduction supply the original linear allowance without a success premise.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native

open ClassicalAlgorithms.Modular XGCD.Native SignedReduction.Native

/-- The original real decision and signed branch require at most eighteen instructions. -/
theorem checkedSelectionEnvelope_card_le (model : ExecutionModel) [BitWord.Selected model] (width
  : Nat) :
    (checkedSelectionEnvelope model width).card ≤ 18 := by
  have signed := signedReductionEnvelope_card_le model width
  simpa only [checkedSelectionEnvelope, Multiset.card_add, ResourcePool.max,
    Multiset.union_zero, ResourcePool.ofList, checkedDecisionEvents, Multiset.coe_card,
    List.length_cons, List.length_nil] using Nat.add_le_add_left signed 2

/-- The actual independent checked-inverse pool obeys the original width-linear ceiling. -/
theorem checkedInverseEnvelope_card_le {width : Nat}
    (model : ExecutionModel) [BitWord.Selected model] (spec : ModulusSpec width) :
    (checkedInverseEnvelope model spec).card ≤ 30 * width + 72 := by
  have loaded := ConstantWord.constantLoader_length_le model (width + 1) spec.modulus
  have raw := rawEnvelope_card model (width + 1)
  have selected := checkedSelectionEnvelope_card_le model width
  unfold checkedInverseEnvelope
  simp only [Multiset.card_add, ResourcePool.ofList, Multiset.coe_card,
    List.length_cons, List.length_nil]
  omega

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native
