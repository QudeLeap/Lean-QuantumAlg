/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Exponentiation
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Resources

/-!
# Independent native event envelopes for the new short-DLP exponentiation member

The independent pool bounds the three actual default-model coordinates.
Its per-bit cap includes the native expansion of each controlled multiplier
instruction. Summing the three coordinate caps is distinct from the tighter
bound on all actual gate occurrences. Invalid compilation parameters retain
their zero-event identity extension.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

/-- Three coordinate caps include the complete native control expansion at every bit. -/
def exponentiationPrimitiveWidthBound (bits width : Nat) : Nat :=
  3 * MAU.Exponentiation.Gidney.eventBound bits width

private theorem exponentiationBudget_card (bits width : Nat) :
    (MAU.Exponentiation.Gidney.nativeBudget bits width).card =
      exponentiationPrimitiveWidthBound bits width := by
  have alphabet : EncodedBit.GateSpec.primitiveAlphabet.card = 3 := rfl
  simp only [MAU.Exponentiation.Gidney.nativeBudget,
    MAU.Exponentiation.Gidney.stageNativeBudget, Multiset.card_nsmul, alphabet,
    exponentiationPrimitiveWidthBound, MAU.Exponentiation.Gidney.eventBound]
  ring

/-- Independent native coordinates for every compiled unit base on the admitted modulus branch. -/
def exponentiationEventEnvelope (bits width N : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  if 0 < N ∧ N ≤ 2 ^ width then MAU.Exponentiation.Gidney.nativeBudget bits width else 0

/-- Cardinality of the independently capped pool, not an equality with actual gate occurrences. -/
def exponentiationPrimitiveBound (bits width N : Nat) : Nat :=
  if 0 < N ∧ N ≤ 2 ^ width then exponentiationPrimitiveWidthBound bits width else 0

@[simp] theorem exponentiationEventEnvelope_card (bits width N : Nat) :
    (exponentiationEventEnvelope bits width N).card =
      exponentiationPrimitiveBound bits width N := by
  unfold exponentiationEventEnvelope exponentiationPrimitiveBound
  split
  · exact exponentiationBudget_card bits width
  · rfl

theorem exponentiationPrimitiveBound_le_widthBound (bits width N : Nat) :
    exponentiationPrimitiveBound bits width N ≤ exponentiationPrimitiveWidthBound bits width := by
  unfold exponentiationPrimitiveBound
  split
  · exact Nat.le_refl _
  · exact Nat.zero_le _

/-- Every actual controlled native coordinate obeys the independent family envelope. -/
theorem exponentiationProgram_eventCost_le (bits width N : Nat) (unit : (ZMod N)ˣ) :
    (exponentiationProgram bits width N unit).eventCost ≤
      exponentiationEventEnvelope bits width N := by
  unfold exponentiationEventEnvelope
  by_cases positive : 0 < N
  · by_cases fitted : N ≤ 2 ^ width
    · rw [exponentiationProgram_valid bits width N positive fitted unit]
      rw [if_pos ⟨positive, fitted⟩]
      exact MAU.Exponentiation.Gidney.gidneyExponent_native_bound bits width
        ⟨N, Nat.lt_succ_of_le fitted⟩ unit
    · rw [exponentiationProgram_unfitted bits width N positive fitted unit]
      rw [if_neg (fun valid => fitted valid.2)]
      exact le_refl (0 : ResourcePool (.quantum AlgorithmGate.model .empty))
  · rw [exponentiationProgram_nonpositive bits width N positive unit]
    rw [if_neg (fun valid => positive valid.1)]
    exact le_refl (0 : ResourcePool (.quantum AlgorithmGate.model .empty))

/-- The actual event count is also bounded by the independent pool's closed cardinality. -/
theorem exponentiationProgram_eventCost_card_le (bits width N : Nat) (unit : (ZMod N)ˣ) :
    (exponentiationProgram bits width N unit).eventCost.card ≤
      exponentiationPrimitiveBound bits width N :=
  (Multiset.card_le_card (exponentiationProgram_eventCost_le bits width N unit)).trans_eq
    (exponentiationEventEnvelope_card bits width N)

/-- Tighter total-event bound, before summing the separate native coordinate caps. -/
theorem exponentiationProgram_actual_event_bound (bits width N : Nat) (unit : (ZMod N)ˣ) :
    (exponentiationProgram bits width N unit).eventCost.card ≤
      MAU.Exponentiation.Gidney.eventBound bits width := by
  by_cases positive : 0 < N
  · by_cases fitted : N ≤ 2 ^ width
    · rw [exponentiationProgram_valid bits width N positive fitted unit]
      exact MAU.Exponentiation.Gidney.gidneyExponent_event_count_bound bits width
        ⟨N, Nat.lt_succ_of_le fitted⟩ unit
    · rw [exponentiationProgram_unfitted bits width N positive fitted unit]
      exact Nat.zero_le _
  · rw [exponentiationProgram_nonpositive bits width N positive unit]
    exact Nat.zero_le _

end

end QuantumAlg.ShortDLP.CompiledMAU
