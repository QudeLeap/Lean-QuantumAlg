/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Resources

/-!
# Explicit native instructions of modular accumulation

Retain every selected-add stage in a single ordered list. Its exact action and
native multiplicities coincide with the composed accumulator, so multiplication
and exponentiation can control or reverse the actual instructions.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

open EncodedBit GateSpec Nat.FixedWidth

private lemma smallStageGates_step (width : Nat) (small : width ≤ 2)
    (selected : Fin width) (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1))
    (state : Registers width) :
    stepList (smallStageGates width small selected modulus constant) state =
      selectedOutput selected modulus constant state := by
  have actual := controlSmallList_step (sourceBit width selected) small
    (Addition.Gidney.Small.modularOffsetGates width small modulus constant) state
  rw [gidneySourceBit_get, Addition.Gidney.Small.modularOffsetGates_step] at actual
  exact actual

/-- The exact native list of the selected stage at each supported width. -/
def stageGates : (width : Nat) → Fin width → (modulus : Fin (2 ^ width + 1)) →
    Fin (modulus.val + 1) → List (GateSpec (encoding width))
  | 0, selected, _, _ => Fin.elim0 selected
  | 1, selected, modulus, constant => smallStageGates 1 (by decide) selected modulus constant
  | 2, selected, modulus, constant => smallStageGates 2 (by decide) selected modulus constant
  | extra + 3, selected, modulus, constant => placedStageGates extra selected modulus constant

/-- The full source is retained while its selected bit controls the exact target offset. -/
lemma gidneyStageGates_step : (width : Nat) → (selected : Fin width) →
    (modulus : Fin (2 ^ width + 1)) → (constant : Fin (modulus.val + 1)) →
    (state : Registers width) →
    stepList (stageGates width selected modulus constant) state =
      selectedOutput selected modulus constant state
  | 0, selected, _, _, _ => Fin.elim0 selected
  | 1, selected, modulus, constant, state =>
      smallStageGates_step 1 (by decide) selected modulus constant state
  | 2, selected, modulus, constant, state =>
      smallStageGates_step 2 (by decide) selected modulus constant state
  | extra + 3, selected, modulus, constant, state =>
      gidneyPlacedStageGates_step extra selected modulus constant state

/-- The literal stage preserves every native multiplicity of the actual selected program. -/
lemma gidneyStageGates_eventCost : (width : Nat) → (selected : Fin width) →
    (modulus : Fin (2 ^ width + 1)) → (constant : Fin (modulus.val + 1)) →
    ResourcePool.ofList ((stageGates width selected modulus constant).map (event .empty)) =
      (stageProgram width selected modulus constant).eventCost
  | 0, selected, _, _ => Fin.elim0 selected
  | 1, _, _, _ => (programList_eventCost _ _ _).symm
  | 2, _, _, _ => (programList_eventCost _ _ _).symm
  | _ + 3, _, _, _ => (programList_eventCost _ _ _).symm

/-- Concatenate the selected source-bit additions in their actual execution order. -/
def prefixGates (width : Nat) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    (count : Nat) → count ≤ width → List (GateSpec (encoding width))
  | 0, _ => []
  | index + 1, within => prefixGates width modulus coefficient index (by omega) ++
      stageGates width ⟨index, by omega⟩ modulus (accumulateConstant modulus coefficient index)

/-- Exact arithmetic action of an executed instruction prefix. -/
lemma gidneyAccumulatePrefixGates_step (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient count : Nat) (within : count ≤ width) (state : Registers width) :
    stepList (prefixGates width modulus coefficient count within) state =
      prefixOutput modulus coefficient count state := by
  induction count with
  | zero => rfl
  | succ index ih =>
      rw [prefixGates, stepList_append, ih (by omega), gidneyStageGates_step]
      rfl

/-- Concatenation retains the resource pool of the original sequential program. -/
lemma gidneyAccumulatePrefixGates_eventCost (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient count : Nat) (within : count ≤ width) :
    ResourcePool.ofList ((prefixGates width modulus coefficient count within).map (event .empty)) =
      (prefixProgram width modulus coefficient count within).eventCost := by
  induction count with
  | zero => rfl
  | succ index ih =>
      rw [prefixGates, List.map_append, ResourcePool.ofList_append,
        ih (by omega), gidneyStageGates_eventCost]
      exact (UnitaryCircuit.seq_eventCost _ _).symm

/-- The complete accumulator as an actual default-model instruction list. -/
def gates (width : Nat) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    List (GateSpec (encoding width)) :=
  prefixGates width modulus coefficient width (Nat.le_refl width)

/-- Exact all-label multiply-accumulate, with complete source preservation. -/
lemma gidneyAccumulateGates_step (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (state : Registers width) :
    stepList (gates width modulus coefficient) state =
      prefixOutput modulus coefficient width state :=
  gidneyAccumulatePrefixGates_step width modulus coefficient width (Nat.le_refl width) state

/-- The exposed list has the complete native ledger of the actual accumulator. -/
lemma gidneyAccumulateGates_eventCost (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) :
    ResourcePool.ofList ((gates width modulus coefficient).map (event .empty)) =
      (program width modulus coefficient).eventCost :=
  gidneyAccumulatePrefixGates_eventCost width modulus coefficient width (Nat.le_refl width)

/-- The independent all-width bound applies to the actual instruction list. -/
lemma gidneyAccumulateGates_length_bound (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) :
    (gates width modulus coefficient).length ≤ width * stageEventBound width := by
  have count := congrArg Multiset.card (gidneyAccumulateGates_eventCost width modulus coefficient)
  simp only [ResourcePool.ofList, Multiset.coe_card, List.length_map] at count
  rw [count]
  exact gidneyAccumulate_event_count_bound width modulus coefficient

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
