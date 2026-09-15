/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Native.Resources

/-!
# Independent finite native resource pool for modular accumulation

The source selector adds one actual control to the offset alphabet. The
resulting six coordinates are X, CNOT, and Toffoli with respectively one or
two additional dimension-two controls. Each is independently capped by the
closed all-width event envelope. The actual program's support proof is
required before that cardinality estimate implies a coordinatewise budget.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

/-- Six strict coordinates: the primitive labels with one or two additional qubit controls. -/
def nativeAlphabet : ResourcePool .quantum :=
  ResourcePool.controlForDimension 2 Addition.Gidney.offsetAlphabet

/-- Independent budget with the same explicit cap at each of the six native coordinates. -/
def nativeBudget (width : Nat) : ResourcePool .quantum :=
  (width * stageEventBound width) • nativeAlphabet

theorem gidneyCanonicalStage_native_support (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1))
    (focus : Resource.Event .quantum)
    (present : focus ∈ (canonicalProgram extra modulus constant).eventCost) :
    focus ∈ nativeAlphabet := by
  rw [gidneyCanonicalStage_eventCost] at present
  change focus ∈ Multiset.map (fun event => event.controlForDimension 2)
    (Addition.Gidney.modularOffsetProgram (extra + 3) modulus constant).eventCost at present
  obtain ⟨event, membership, rfl⟩ := Multiset.mem_map.mp present
  exact Multiset.mem_map.mpr ⟨event,
    Addition.Gidney.gidneyModularOffset_native_support
      (extra + 3) modulus constant event membership,
    rfl⟩

theorem gidneyPlacedStage_native_support (extra : Nat) (selected : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1))
    (focus : Resource.Event .quantum)
    (present : focus ∈ (placedStageProgram extra selected modulus constant).eventCost) :
    focus ∈ nativeAlphabet := by
  rw [(gidneyPlacedStage_resources extra selected modulus constant (fun _ => 1)).1] at present
  exact gidneyCanonicalStage_native_support extra modulus constant focus present

theorem gidneySmallStage_native_support (width : Nat) (small : width ≤ 2)
    (selected : Fin width) (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1))
    (focus : Resource.Event .quantum)
    (present : focus ∈ (smallStageProgram width small selected modulus constant).eventCost) :
    focus ∈ nativeAlphabet := by
  rw [gidneySmallStage_eventCost] at present
  change focus ∈ Multiset.map (fun event => event.controlForDimension 2)
    (Addition.Gidney.Small.modularOffsetProgram width small modulus constant).eventCost at present
  obtain ⟨event, membership, rfl⟩ := Multiset.mem_map.mp present
  change event.controlForDimension 2 ∈ Multiset.map
    (fun current => current.controlForDimension 2) Addition.Gidney.offsetAlphabet
  apply Multiset.mem_map.mpr
  refine ⟨event, ?_, rfl⟩
  exact Multiset.mem_add.mpr (Or.inl
    (Addition.Gidney.gidneySmallModularOffset_native_support
      width small modulus constant event membership))

theorem gidneyStage_native_support : (width : Nat) → (selected : Fin width) →
    (modulus : Fin (2 ^ width + 1)) → (constant : Fin (modulus.val + 1)) →
    (focus : Resource.Event .quantum) →
    focus ∈ (stageProgram width selected modulus constant).eventCost →
      focus ∈ nativeAlphabet
  | 0, selected, _, _, _, _ => Fin.elim0 selected
  | 1, selected, modulus, constant, focus, present =>
      gidneySmallStage_native_support 1 (by decide) selected modulus constant focus present
  | 2, selected, modulus, constant, focus, present =>
      gidneySmallStage_native_support 2 (by decide) selected modulus constant focus present
  | extra + 3, selected, modulus, constant, focus, present =>
      gidneyPlacedStage_native_support extra selected modulus constant focus present

theorem gidneyAccumulatePrefix_native_support (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient count : Nat) (within : count ≤ width)
    (focus : Resource.Event .quantum)
    (present : focus ∈ (prefixProgram width modulus coefficient count within).eventCost) :
    focus ∈ nativeAlphabet := by
  induction count with
  | zero =>
      change focus ∈ (0 : ResourcePool .quantum) at present
      simp at present
  | succ index ih =>
      change focus ∈ ((prefixProgram width modulus coefficient index (by omega)).seq
        (stageProgram width ⟨index, by omega⟩ modulus
          (Nat.FixedWidth.accumulateConstant modulus coefficient index))).eventCost at present
      rw [UnitaryCircuit.seq_eventCost] at present
      rcases Multiset.mem_add.mp present with before | current
      · exact ih (by omega) before
      · exact gidneyStage_native_support width ⟨index, by omega⟩ modulus
          (Nat.FixedWidth.accumulateConstant modulus coefficient index) focus current

/-- Every actual event belongs to the explicit six-coordinate alphabet. -/
theorem gidneyAccumulate_native_support (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (focus : Resource.Event .quantum)
    (present : focus ∈ (program width modulus coefficient).eventCost) :
    focus ∈ nativeAlphabet := by
  change focus ∈ ((prefixProgram width modulus coefficient width (Nat.le_refl width)).seq
    (UnitaryCircuit.identity (Qubits (encoding width).width)
      (List.range (2 * width)) List.nodup_range)).eventCost at present
  rw [UnitaryCircuit.seq_eventCost, UnitaryCircuit.identity_eventCost, add_zero] at present
  exact gidneyAccumulatePrefix_native_support width modulus coefficient width
    (Nat.le_refl width) focus present

/-- The complete actual circuit meets the independent finite native-resource budget. -/
theorem gidneyAccumulate_native_bound (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) :
    (program width modulus coefficient).eventCost ≤ nativeBudget width :=
  ResourcePool.le_scaled_of_support_card_le _ _ _
    (gidneyAccumulate_native_support width modulus coefficient)
    (gidneyAccumulate_event_count_bound width modulus coefficient)

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
