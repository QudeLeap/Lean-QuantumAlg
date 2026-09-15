/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.NativeResources

/-!
# Independent resources for the actual two-word unit multiplier

Two accumulation budgets and the exact `3 * width` native CNOT swap ledger
give an independent coordinatewise pool. The actual adjoint preserves its
source circuit's strict event coordinates. Unit-duration serial depth is
bounded by twice the accumulation envelope plus the literal swap length.
-/

namespace QuantumAlg.MAU.Multiplication.Gidney

noncomputable section

open Accumulate.Gidney

/-- The independent literal CNOT pool needed for exchanging the two words. -/
def wordSwapBudget (width : Nat) : ResourcePool .quantum :=
  ResourcePool.ofList (List.replicate (3 * width) (.gate (.builtin "cnot")))

/-- Two independent accumulation pools and the literal word-swap pool. -/
def nativeBudget (width : Nat) : ResourcePool .quantum :=
  Accumulate.Gidney.nativeBudget width + wordSwapBudget width +
    Accumulate.Gidney.nativeBudget width

/-- The independent total-event and unit-duration serial-depth envelope. -/
def eventBound (width : Nat) : Nat :=
  2 * (width * stageEventBound width) + 3 * width

/-- The actual program retains both MAC ledgers and the precise native CNOT swap coordinates. -/
theorem gidneyUnitMultiplication_eventCost (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (program width modulus coefficient).eventCost =
      (Accumulate.Gidney.program width modulus (coefficient : ZMod modulus.val).val).eventCost +
        wordSwapBudget width +
          (Accumulate.Gidney.program width modulus
            ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val).eventCost := by
  simp only [program, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.dagger_eventCost, gidneyWordSwap_eventCost, wordSwapBudget]

/-- Every actual event coordinate is bounded by the independent finite native pool. -/
theorem gidneyUnitMultiplication_native_bound (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (program width modulus coefficient).eventCost ≤ nativeBudget width := by
  rw [gidneyUnitMultiplication_eventCost]
  exact add_le_add
    (add_le_add (gidneyAccumulate_native_bound width modulus
      (coefficient : ZMod modulus.val).val) (le_refl (wordSwapBudget width)))
    (gidneyAccumulate_native_bound width modulus
      ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val)

theorem gidneyUnitMultiplication_event_count_bound (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ) :
    (program width modulus coefficient).eventCost.card ≤ eventBound width := by
  rw [gidneyUnitMultiplication_eventCost, Multiset.card_add, Multiset.card_add]
  have swapCount : (wordSwapBudget width).card = 3 * width := by
    simp [wordSwapBudget, ResourcePool.ofList]
  rw [swapCount]
  have forward := gidneyAccumulate_event_count_bound width modulus
    (coefficient : ZMod modulus.val).val
  have inverse := gidneyAccumulate_event_count_bound width modulus
    ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val
  unfold eventBound
  omega

/-- The actual serial schedule has one unit-duration step for each native event occurrence. -/
theorem gidneyUnitMultiplication_depth_eq_events (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ) :
    (program width modulus coefficient).evaluatedEventDepth (fun _ => 1) =
      (program width modulus coefficient).eventCost.card := by
  unfold program
  simp only [UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.evaluatedEventDepth_dagger,
    gidneyAccumulate_depth_eq_events, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.dagger_eventCost, Multiset.card_add]
  rw [(gidneyWordSwap_serial_resources width).1, (gidneyWordSwap_serial_resources width).2]

theorem gidneyUnitMultiplication_depth_bound (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ) :
    (program width modulus coefficient).evaluatedEventDepth (fun _ => 1) ≤ eventBound width := by
  rw [gidneyUnitMultiplication_depth_eq_events]
  exact gidneyUnitMultiplication_event_count_bound width modulus coefficient

/-- The full existing two-word carrier supplies every physical system used by the multiplier. -/
theorem gidneyUnitMultiplication_qubit_count (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ) :
    (encoding width).width = 2 * width ∧
      (program width modulus coefficient).physical_idx.length = 2 * width := by
  constructor
  · change width + width = 2 * width
    omega
  · rw [gidneyUnitMultiplication_physical, List.length_range]

end

end QuantumAlg.MAU.Multiplication.Gidney
