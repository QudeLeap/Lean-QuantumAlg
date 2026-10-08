/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Resources
import all QuantumAlg.Primitives.MAU.Addition.HRS.Recursive.Gates

/-!
# Literal HRS recursive addition gates

Retain the bridge and both recursively placed child lists on the original word
and one dirty bit. Their native events are those of the actual HRS construction,
and their action restores the dirty value on every input [HRS16, paper.tex:232-260].
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

open EncodedBit GateSpec

/-- The bridge and both children, joined on the original word and dirty bit. -/
def recursiveStepGates (width : Nat) (constant : Fin (2 ^ width))
    (lowGates : List (GateSpec (oneDirtyEncoding (lowWidth width))))
    (highGates : List (GateSpec (oneDirtyEncoding (highWidth width)))) :
    List (GateSpec (oneDirtyEncoding width)) :=
  joinGates width
    ((recursiveBridgeGates width ((splitWord width) constant).1 ++
      lowChildGates (lowWidth width) (highWidth width) lowGates) ++
      highChildGates (lowWidth width) (highWidth width) highGates)

/-- Exact recursive child additions imply exact full-word addition for the literal list. -/
theorem hrsRecursiveStepGates_step (width : Nat) (constant : Fin (2 ^ width))
    (lowGates : List (GateSpec (oneDirtyEncoding (lowWidth width))))
    (highGates : List (GateSpec (oneDirtyEncoding (highWidth width))))
    (lowAction : ∀ state, stepList lowGates state =
      oneDirtyOutput ((splitWord width) constant).1 state)
    (highAction : ∀ state, stepList highGates state =
      oneDirtyOutput ((splitWord width) constant).2 state)
    (state : OneDirtyRegisters width) :
    stepList (recursiveStepGates width constant lowGates highGates) state =
      oneDirtyOutput constant state := by
  rw [recursiveStepGates, hrsJoinGates_step]
  simp only [stepList_append, hrsRecursiveBridgeGates_step,
    hrsLowChildGates_step, hrsHighChildGates_step, lowAction, highAction]
  apply Prod.ext
  · exact hrsJoin_recursive_addition width constant state.1
  · rfl

/-- The ordered events are precisely the original bridge followed by the two children. -/
theorem hrsRecursiveStepGates_events (width : Nat) (constant : Fin (2 ^ width))
    (lowGates : List (GateSpec (oneDirtyEncoding (lowWidth width))))
    (highGates : List (GateSpec (oneDirtyEncoding (highWidth width)))) :
    (recursiveStepGates width constant lowGates highGates).map (event .empty) =
      ((recursiveBridgeProgram width ((splitWord width) constant).1).eventTrace ++
        lowGates.map (event .empty)) ++ highGates.map (event .empty) := by
  rw [recursiveStepGates, hrsJoinGates_events]
  simp only [List.map_append, hrsRecursiveBridgeGates_events,
    hrsLowChildGates_events, hrsHighChildGates_events]

/-- Literal native instructions for all widths and compile-time constants. -/
def oneDirtyGates (width : Nat) (constant : Fin (2 ^ width)) :
    List (GateSpec (oneDirtyEncoding width)) :=
  if _base : width ≤ 1 then
    oneDirtyBaseGates width constant
  else
    recursiveStepGates width constant
      (oneDirtyGates (lowWidth width) ((splitWord width) constant).1)
      (oneDirtyGates (highWidth width) ((splitWord width) constant).2)
termination_by width
decreasing_by
  all_goals
    have two : 2 ≤ width := by omega
    first
    | exact (hrsSplit_decreases width two).1
    | exact (hrsSplit_decreases width two).2

/-- Exact all-input addition, including restoration of the arbitrary dirty value. -/
theorem hrsOneDirtyGates_step (width : Nat) (constant : Fin (2 ^ width))
    (state : OneDirtyRegisters width) :
    stepList (oneDirtyGates width constant) state = oneDirtyOutput constant state := by
  induction width using Nat.strong_induction_on with
  | h width ih =>
      by_cases base : width ≤ 1
      · rw [oneDirtyGates, dif_pos base]
        exact hrsOneDirtyBase_step width base constant state
      · rw [oneDirtyGates, dif_neg base]
        have decrease := hrsSplit_decreases width (by omega)
        exact hrsRecursiveStepGates_step width constant _ _
          (ih (lowWidth width) decrease.1 ((splitWord width) constant).1)
          (ih (highWidth width) decrease.2 ((splitWord width) constant).2) state

/-- The explicit instructions retain every native multiplicity of the HRS source program. -/
theorem hrsOneDirtyGates_eventCost (width : Nat) (constant : Fin (2 ^ width)) :
    ResourcePool.ofList ((oneDirtyGates width constant).map (event .empty)) =
      (oneDirtyProgram width constant).eventCost := by
  induction width using Nat.strong_induction_on with
  | h width ih =>
      by_cases base : width ≤ 1
      · rw [oneDirtyGates, dif_pos base, oneDirtyProgram, dif_pos base,
          oneDirtyBaseProgram, programList_eventCost]
      · rw [oneDirtyGates, dif_neg base, hrsRecursiveStepGates_events,
          ResourcePool.ofList_append, ResourcePool.ofList_append,
          UnitaryCircuit.ofList_eventTrace_eq_eventCost]
        have decrease := hrsSplit_decreases width (by omega)
        rw [ih (lowWidth width) decrease.1, ih (highWidth width) decrease.2]
        conv_rhs => rw [oneDirtyProgram, dif_neg base]
        rw [hrsRecursiveStep_eventCost]

/-- The original native gate count is exactly the length of the exposed list. -/
theorem hrsOneDirtyGates_length (width : Nat) (constant : Fin (2 ^ width)) :
    (oneDirtyGates width constant).length = (oneDirtyProgram width constant).eventCost.card := by
  rw [← hrsOneDirtyGates_eventCost]
  simp [ResourcePool.ofList]

/-- The actual literal gate count satisfies the independent logarithmic HRS envelope. -/
theorem hrsOneDirtyGates_length_bound (width : Nat) (constant : Fin (2 ^ width)) :
    (oneDirtyGates width constant).length ≤ width * (39 * Nat.clog 2 width + 1) := by
  rw [hrsOneDirtyGates_length]
  exact hrsOneDirty_event_count_bound width constant

/-- The explicit native program implements the exact original word/dirty contract. -/
theorem hrsOneDirtyGates_realizes (width : Nat) (constant : Fin (2 ^ width))
    (oracles : OracleModel) :
    UnitaryCircuit.Realizes (oneDirtyEncoding width)
      (programList (QubitLayout.canonical _) oracles (oneDirtyGates width constant))
      (oneDirtyOutput constant) :=
  realizesList_congrStep _ _ _ (hrsOneDirtyGates_step width constant)

end

end QuantumAlg.MAU.Addition.HRS
