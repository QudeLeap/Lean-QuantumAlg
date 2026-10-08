/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Components.GateModel.Algorithm
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

open Accumulate.Gidney EncodedBit.GateSpec

/-- The independent literal CNOT pool needed for exchanging the two words. -/
def wordSwapBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ResourcePool.ofList (List.replicate (3 * width) (.gate .cnot))

/-- Two independent accumulation pools and the literal word-swap pool. -/
public def nativeBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  Accumulate.Gidney.nativeBudget width + wordSwapBudget width +
    Accumulate.Gidney.nativeBudget width

theorem nativeBudget_singleQubit_count_symbolic (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit) (nativeBudget width) =
      2 * (width * Accumulate.Gidney.stageEventBound width) := by
  simp [nativeBudget, wordSwapBudget, Accumulate.Gidney.nativeBudget,
    Accumulate.Gidney.nativeAlphabet, primitiveAlphabet, List.count_replicate]
  omega

theorem nativeBudget_cnot_count_symbolic (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .cnot) (nativeBudget width) =
      2 * (width * Accumulate.Gidney.stageEventBound width) + 3 * width := by
  simp [nativeBudget, wordSwapBudget, Accumulate.Gidney.nativeBudget,
    Accumulate.Gidney.nativeAlphabet, primitiveAlphabet]
  omega

theorem nativeBudget_toffoli_count_symbolic (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .toffoli) (nativeBudget width) =
      2 * (width * Accumulate.Gidney.stageEventBound width) := by
  simp [nativeBudget, wordSwapBudget, Accumulate.Gidney.nativeBudget,
    Accumulate.Gidney.nativeAlphabet, primitiveAlphabet, List.count_replicate]
  omega

/-- The independent 256-bit two-word multiplier budget reserves this many one-qubit gates. -/
public theorem nativeBudget_singleQubit_count_256 :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit) (nativeBudget 256) = 6047305728 := by
  rw [nativeBudget_singleQubit_count_symbolic]
  decide

/-- The same budget includes 768 literal CNOTs for the 256-bit word exchange. -/
public theorem nativeBudget_cnot_count_256 :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .cnot) (nativeBudget 256) = 6047306496 := by
  rw [nativeBudget_cnot_count_symbolic]
  decide

/-- The independent 256-bit multiplier's Toffoli allowance comes from both accumulations. -/
public theorem nativeBudget_toffoli_count_256 :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .toffoli) (nativeBudget 256) = 6047305728 := by
  rw [nativeBudget_toffoli_count_symbolic]
  decide

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
  have reversed (source : List (EncodedBit.GateSpec (encoding width))) :
      ResourcePool.ofList (source.reverse.map (event .empty)) =
        ResourcePool.ofList (source.map (event .empty)) := by
    simp [List.map_reverse, ResourcePool.ofList]
  have swapEvents : ResourcePool.ofList ((wordSwapGates width).map (event .empty)) =
      wordSwapBudget width :=
    (programList_eventCost (QubitLayout.canonical _) .empty (wordSwapGates width)).symm.trans
      (gidneyWordSwap_eventCost width)
  rw [program, programList_eventCost, gates]
  simp only [List.map_append, ResourcePool.ofList_append, reversed,
    gidneyAccumulateGates_eventCost, swapEvents]

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
  rw [program, programList_evaluatedEventDepth_unit, programList_eventCost_card]

theorem gidneyUnitMultiplication_depth_bound (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ) :
    (program width modulus coefficient).evaluatedEventDepth (fun _ => 1) ≤ eventBound width := by
  rw [gidneyUnitMultiplication_depth_eq_events]
  exact gidneyUnitMultiplication_event_count_bound width modulus coefficient

/-- The literal multiplication list satisfies the independent arithmetic event envelope. -/
theorem gidneyUnitMultiplicationGates_length_bound (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ) :
    (gates width modulus coefficient).length ≤ eventBound width := by
  have actual := gidneyUnitMultiplication_event_count_bound width modulus coefficient
  rw [program, programList_eventCost_card] at actual
  exact actual

/-- The full existing two-word carrier supplies every physical system used by the multiplier. -/
theorem gidneyUnitMultiplication_qubit_count (width : Nat) :
    (encoding width).width = 2 * width ∧
      (QubitLayout.canonical (encoding width).width).systemIdx.length = 2 * width := by
  constructor
  · change width + width = 2 * width
    omega
  · rw [(gidneyUnitMultiplication_interface width).2, List.length_range]

end

end QuantumAlg.MAU.Multiplication.Gidney
