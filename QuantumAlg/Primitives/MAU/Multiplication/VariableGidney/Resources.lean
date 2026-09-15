/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.NativeResources
import all QuantumAlg.Components.Encoded.BitGates.Control.Resources

/-!
# Independent native resources of three-word variable multiplication

Each first-input bit controls one full existing MAC. Its native event
coordinates retain the additional control, and its shared selector
serializes all body occurrences. The full static schedule uses one stage
per first-input bit. Its explicit count bound is quadratic in the number
of bit pairs times the existing modular-offset bound, with no claim that
this upper bound is attained on every modulus or constant.
-/

namespace QuantumAlg.MAU.Multiplication.VariableGidney

noncomputable section

/-- Independent native budget for each actual selected MAC. -/
def stageBudget (width : Nat) : ResourcePool .quantum :=
  ResourcePool.controlForDimension 2 (Accumulate.Gidney.nativeBudget width)

/-- Independent coordinatewise budget for the complete bit-pair program. -/
def nativeBudget (width : Nat) : ResourcePool .quantum := width • stageBudget width

/-- Explicit native-event and serial unit-depth upper bound. -/
def eventBound (width : Nat) : Nat := width * (width * Accumulate.Gidney.stageEventBound width)

theorem variableGidney_stage_pool (width : Nat) (modulus : Fin (2 ^ width + 1))
    (index : Fin width) :
    (stageProgram width modulus index).eventCost =
      ResourcePool.controlForDimension 2
        (Accumulate.Gidney.program width modulus (2 ^ index.val)).eventCost :=
  UnitaryCircuit.controlAtEncodedBit_native_pool (inputBit width index)
    (Accumulate.Gidney.program width modulus (2 ^ index.val))

theorem variableGidney_stage_budget (width : Nat) (modulus : Fin (2 ^ width + 1))
    (index : Fin width) :
    (stageProgram width modulus index).eventCost ≤ stageBudget width := by
  rw [variableGidney_stage_pool]
  exact (ResourcePool.controlForDimension_le_controlForDimension_iff 2).mpr
    (Accumulate.Gidney.gidneyAccumulate_native_bound width modulus (2 ^ index.val))

theorem variableGidney_stage_count (width : Nat) (modulus : Fin (2 ^ width + 1))
    (index : Fin width) :
    (stageProgram width modulus index).eventCost.card ≤
      width * Accumulate.Gidney.stageEventBound width := by
  rw [variableGidney_stage_pool]
  simp only [ResourcePool.controlForDimension, ResourcePool.controlForDimensions, Multiset.card_map]
  exact Accumulate.Gidney.gidneyAccumulate_event_count_bound width modulus (2 ^ index.val)

theorem variableGidney_stage_depth (width : Nat) (modulus : Fin (2 ^ width + 1))
    (index : Fin width) :
    (stageProgram width modulus index).evaluatedEventDepth (fun _ => 1) =
      (stageProgram width modulus index).eventCost.card := by
  have depth : (stageProgram width modulus index).evaluatedEventDepth (fun _ => 1) =
      (Accumulate.Gidney.program width modulus (2 ^ index.val)).eventCost.card :=
    UnitaryCircuit.controlAtEncodedBit_unit_depth (inputBit width index)
      (Accumulate.Gidney.program width modulus (2 ^ index.val))
  rw [depth, variableGidney_stage_pool]
  simp only [ResourcePool.controlForDimension, ResourcePool.controlForDimensions, Multiset.card_map]

theorem variableGidney_prefix_budget (width : Nat) (modulus : Fin (2 ^ width + 1))
    (count : Nat) (within : count ≤ width) :
    (prefixProgram width modulus count within).eventCost ≤ count • stageBudget width := by
  induction count with
  | zero => exact le_of_eq (zero_nsmul _).symm
  | succ index inductionHypothesis =>
      change ((prefixProgram width modulus index (by omega)).seq
        (stageProgram width modulus ⟨index, by omega⟩)).eventCost ≤ _
      rw [UnitaryCircuit.seq_eventCost, add_nsmul, one_nsmul]
      exact add_le_add (inductionHypothesis (by omega))
        (variableGidney_stage_budget width modulus ⟨index, by omega⟩)

theorem variableGidney_prefix_count (width : Nat) (modulus : Fin (2 ^ width + 1))
    (count : Nat) (within : count ≤ width) :
    (prefixProgram width modulus count within).eventCost.card ≤
      count * (width * Accumulate.Gidney.stageEventBound width) := by
  induction count with
  | zero => exact Nat.zero_le _
  | succ index inductionHypothesis =>
      change ((prefixProgram width modulus index (by omega)).seq
        (stageProgram width modulus ⟨index, by omega⟩)).eventCost.card ≤ _
      rw [UnitaryCircuit.seq_eventCost, Multiset.card_add, Nat.succ_mul]
      exact Nat.add_le_add (inductionHypothesis (by omega))
        (variableGidney_stage_count width modulus ⟨index, by omega⟩)

theorem variableGidney_prefix_depth (width : Nat) (modulus : Fin (2 ^ width + 1))
    (count : Nat) (within : count ≤ width) :
    (prefixProgram width modulus count within).evaluatedEventDepth (fun _ => 1) =
      (prefixProgram width modulus count within).eventCost.card := by
  induction count with
  | zero => rfl
  | succ index inductionHypothesis =>
      change ((prefixProgram width modulus index (by omega)).seq
        (stageProgram width modulus ⟨index, by omega⟩)).evaluatedEventDepth (fun _ => 1) =
          ((prefixProgram width modulus index (by omega)).seq
            (stageProgram width modulus ⟨index, by omega⟩)).eventCost.card
      rw [UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.seq_eventCost,
        Multiset.card_add, inductionHypothesis, variableGidney_stage_depth]

/-- The complete actual program meets the independent coordinatewise budget. -/
theorem variableGidney_native_budget (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (program width modulus).eventCost ≤ nativeBudget width := by
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.identity_eventCost, add_zero]
  exact variableGidney_prefix_budget width modulus width (Nat.le_refl width)

/-- The actual complete event count has the explicit polynomial upper bound. -/
theorem variableGidney_event_count (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (program width modulus).eventCost.card ≤ eventBound width := by
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.identity_eventCost, add_zero]
  exact variableGidney_prefix_count width modulus width (Nat.le_refl width)

/-- The actual sequential critical path counts the same controlled native events. -/
theorem variableGidney_unit_depth (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (program width modulus).evaluatedEventDepth (fun _ => 1) ≤ eventBound width := by
  have complete : (program width modulus).evaluatedEventDepth (fun _ => 1) =
      (program width modulus).eventCost.card := by
    rw [program, UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.seq_eventCost,
      UnitaryCircuit.identity_eventCost, add_zero, variableGidney_prefix_depth]
    rfl
  exact complete.trans_le (variableGidney_event_count width modulus)

end

end QuantumAlg.MAU.Multiplication.VariableGidney
