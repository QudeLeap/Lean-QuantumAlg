/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Resources
import all QuantumAlg.Components.Encoded.BitGates.Resources
import all QuantumAlg.Core.Base.Accounting.Support

/-!
# Native-coordinate support and independent budget for the HRS adder

The actual recursion emits only the primitive X, CNOT, and Toffoli labels.
This follows from its proved recursive counts and its literal gate-list
leaves. The independent logarithmic numerical envelope then bounds each
coordinate of the explicit alphabet, including all small-width branches.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

open EncodedBit.GateSpec

private lemma hrs_count_zero (width : Nat) (constant : Fin (2 ^ width))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (outside : focus ∉ primitiveAlphabet) :
    ResourcePool.count focus (oneDirtyProgram width constant).eventCost = 0 := by
  have hx : (.gate .singleQubit :
      Resource.Event (.quantum AlgorithmGate.model .empty)) ≠ focus := by
    intro equality
    apply outside
    rw [← equality]
    simp [primitiveAlphabet, ResourcePool.ofList]
  have hc : (.gate .cnot : Resource.Event (.quantum AlgorithmGate.model .empty)) ≠ focus := by
    intro equality
    apply outside
    rw [← equality]
    simp [primitiveAlphabet, ResourcePool.ofList]
  induction width using Nat.strong_induction_on with
  | h width ih =>
      rw [hrsOneDirty_native_count]
      by_cases base : width ≤ 1
      · rw [if_pos base, if_neg hx, Nat.mul_zero]
      · rw [if_neg base]
        have decrease := hrsSplit_decreases width (by omega)
        have hincrement : ResourcePool.count focus
            (controlledBorrowedIncrementProgram (highWidth width)).eventCost = 0 :=
          programList_count_zero_of_not_mem_primitiveAlphabet
            (QubitLayout.canonical _)
            (controlledBorrowedIncrementGates (highWidth width))
            focus outside
        have hcarry : ResourcePool.count focus
            (carryProgram (lowWidth width) ((splitWord width) constant).1).eventCost =
              0 :=
          programList_count_zero_of_not_mem_primitiveAlphabet
            (QubitLayout.canonical _)
            (carryGates (lowWidth width) ((splitWord width) constant).1) focus outside
        have hbridge : ResourcePool.count focus
            (recursiveBridgeProgram
              width ((splitWord width) constant).1).eventCost = 0 := by
          rw [hrsRecursiveBridge_native_count, hincrement, hcarry, if_neg hc]
          omega
        rw [hbridge, ih (lowWidth width) decrease.1 ((splitWord width) constant).1,
          ih (highWidth width) decrease.2 ((splitWord width) constant).2]

/-- The actual recursive HRS program contains only the three native primitive coordinates. -/
lemma hrsOneDirty_native_support (width : Nat) (constant : Fin (2 ^ width))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (oneDirtyProgram width constant).eventCost) :
    focus ∈ primitiveAlphabet := by
  by_contra outside
  have zero := hrs_count_zero width constant focus outside
  have positive := Multiset.count_pos.mpr present
  change 0 < ResourcePool.count focus (oneDirtyProgram width constant).eventCost at positive
  omega
/-- The independent all-width envelope at each of the three native primitive coordinates. -/
def nativeBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  (width * (39 * Nat.clog 2 width + 1)) • primitiveAlphabet

/-- The actual one-dirty circuit meets the independently specified finite native pool. -/
lemma hrsOneDirty_native_bound (width : Nat) (constant : Fin (2 ^ width)) :
    (oneDirtyProgram width constant).eventCost ≤ nativeBudget width :=
  ResourcePool.le_scaled_of_support_card_le _ _ _
    (hrsOneDirty_native_support width constant)
    (hrsOneDirty_event_count_bound width constant)

end

end QuantumAlg.MAU.Addition.HRS
