/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Exponentiation
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.NativeResources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Native.Alphabet
import all QuantumAlg.Components.Encoded.BitGates.Resources

/-!
# Independent native event envelopes for the new short-DLP exponentiation member

The independent pool retains all six controlled primitive coordinates and
the controlled swap-CNOT coordinate. Its cardinality sums the separate
coordinate caps; it is deliberately distinguished from the sharper bound
on the total actual gate occurrences. Every branch uses its literal actual
program and the same source modulus domain.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

private theorem control_card (pool : ResourcePool .quantum) :
    (ResourcePool.controlForDimension 2 pool).card = pool.card := by
  simp only [ResourcePool.controlForDimension, ResourcePool.controlForDimensions, Multiset.card_map]

private theorem accumulateAlphabet_card :
    MAU.Multiplication.Accumulate.Gidney.nativeAlphabet.card = 6 := by
  have primitive : EncodedBit.GateSpec.primitiveAlphabet.card = 3 := rfl
  unfold MAU.Multiplication.Accumulate.Gidney.nativeAlphabet
  rw [control_card]
  unfold MAU.Addition.Gidney.offsetAlphabet
  rw [Multiset.card_add, control_card, primitive]

/-- The independent width-only pool sums six caps for each MAC and the exact word-swap CNOTs. -/
def exponentiationPrimitiveWidthBound (bits width : Nat) : Nat :=
  bits * (12 * (width * MAU.Multiplication.Accumulate.Gidney.stageEventBound width) + 3 * width)

private theorem exponentiationBudget_card (bits width : Nat) :
    (MAU.Exponentiation.Gidney.nativeBudget bits width).card =
      exponentiationPrimitiveWidthBound bits width := by
  have accumulation : (MAU.Multiplication.Accumulate.Gidney.nativeBudget width).card =
      (width * MAU.Multiplication.Accumulate.Gidney.stageEventBound width) * 6 := by
    rw [MAU.Multiplication.Accumulate.Gidney.nativeBudget, Multiset.card_nsmul,
      accumulateAlphabet_card]
  have swap : (MAU.Multiplication.Gidney.wordSwapBudget width).card = 3 * width := by
    simp only [MAU.Multiplication.Gidney.wordSwapBudget, ResourcePool.ofList,
      Multiset.coe_card, List.length_replicate]
  have multiplication : (MAU.Multiplication.Gidney.nativeBudget width).card =
      12 * (width * MAU.Multiplication.Accumulate.Gidney.stageEventBound width) + 3 * width := by
    rw [MAU.Multiplication.Gidney.nativeBudget, Multiset.card_add, Multiset.card_add,
      accumulation, swap]
    omega
  rw [MAU.Exponentiation.Gidney.nativeBudget, Multiset.card_nsmul,
    MAU.Exponentiation.Gidney.stageNativeBudget, control_card, multiplication]
  rfl

/-- Independent native coordinates for every compiled unit base on the admitted modulus branch. -/
def exponentiationEventEnvelope (bits width N : Nat) : ResourcePool .quantum :=
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
      exact le_refl (0 : ResourcePool .quantum)
  · rw [exponentiationProgram_nonpositive bits width N positive unit]
    rw [if_neg (fun valid => positive valid.1)]
    exact le_refl (0 : ResourcePool .quantum)

/-- The actual event count is also bounded by the independent pool's closed cardinality. -/
theorem exponentiationProgram_eventCost_card_le (bits width N : Nat) (unit : (ZMod N)ˣ) :
    (exponentiationProgram bits width N unit).eventCost.card ≤
      exponentiationPrimitiveBound bits width N :=
  (Multiset.card_le_card (exponentiationProgram_eventCost_le bits width N unit)).trans_eq
    (exponentiationEventEnvelope_card bits width N)

/-- Tighter total-event bound, before summing the separate native coordinate caps. -/
theorem exponentiationProgram_actual_event_bound (bits width N : Nat) (unit : (ZMod N)ˣ) :
    (exponentiationProgram bits width N unit).eventCost.card ≤
      bits * MAU.Multiplication.Gidney.eventBound width := by
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
