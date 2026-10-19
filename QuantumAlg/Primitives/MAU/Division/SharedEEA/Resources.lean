/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Division.SharedEEA.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Budget
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Resources
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources

/-!
# Independent resources of actual shared-EEA division accumulation

The width-only envelope charges both complete corrected EEA passes and
all stages of the actual variable-product Gidney accumulator. Its entire
shared frame, numerator, and independent target remain live. This word-only native
core excludes fixed preparation and any supplied flag; runtime composition
must charge those actual additional retained systems and preparation event.
-/

namespace QuantumAlg.MAU.Division.SharedEEA

noncomputable section

open Inversion.SharedEEA
open Multiplication

/-- Independent native-coordinate envelope for both EEA passes and the modular accumulator. -/
def nativeBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  NativeBudget.corrected width + (VariableGidney.nativeBudget width + NativeBudget.corrected width)

/-- Independent count/depth cap without projecting the circuit under verification. -/
def eventBound (width : Nat) : Nat :=
  2 * ForwardResources.correctedBound width + VariableGidney.eventBound width

/-- Placement and retention preserve every actual middle-program event in order. -/
lemma divisionMiddle_trace (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (middleProgram width modulus).eventTrace =
      (VariableGidney.program width modulus).eventTrace := by
  rw [middleProgram, EncodedBit.FullPlacement.place_eventTrace]
  exact UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventTrace _ _

/-- The placed middle has precisely the existing native accumulator's event pool. -/
lemma divisionMiddle_cost (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (middleProgram width modulus).eventCost = (VariableGidney.program width modulus).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, divisionMiddle_trace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

private lemma forward_trace (modulus : Nat) (nontrivial : 1 < modulus) :
    (forwardProgram modulus nontrivial).eventTrace =
      (CorrectedSchedule.program modulus nontrivial).eventTrace :=
  UnitaryCircuit.prodLeft_eventTrace (n := modulus.size + modulus.size) _

private lemma forward_cost (modulus : Nat) (nontrivial : 1 < modulus) :
    (forwardProgram modulus nontrivial).eventCost =
      (CorrectedSchedule.program modulus nontrivial).eventCost :=
  UnitaryCircuit.prodLeft_eventCost (n := modulus.size + modulus.size) _

private lemma oracleFreePool_empty
    (pool : ResourcePool (.quantum AlgorithmGate.model .empty)) :
    AlgorithmGate.oracleFreePool .empty pool = pool := by
  have identity : AlgorithmGate.oracleFreeEvent .empty = id := by
    funext event
    cases event with
    | classicalOperation coordinate => cases coordinate
    | classicalQuery coordinate => cases coordinate
    | gate coordinate => rfl
    | oracle coordinate => cases coordinate
    | preparation dimension => rfl
    | measurement dimension => rfl
  change Multiset.map (AlgorithmGate.oracleFreeEvent .empty) pool = pool
  rw [identity, Multiset.map_id]

/-- The full actual event trace includes the same corrected forward and its complete reversal. -/
lemma divisionProgram_trace (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventTrace =
      (CorrectedSchedule.program modulus nontrivial).eventTrace ++
        ((VariableGidney.program modulus.size
          (Inversion.SharedEEA.Accumulate.fittedModulus modulus)).eventTrace ++
          ((forwardProgram modulus nontrivial).dagger
            (AlgorithmGate.oracleFreeAdjoints .empty)).eventTrace) := by
  rw [program, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.seq_eventTrace,
    divisionMiddle_trace, forward_trace]

/-- Coordinatewise native multiplicities account for the same full compute and uncompute. -/
lemma divisionProgram_native_budget (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventCost ≤ nativeBudget modulus.size := by
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    AlgorithmGate.algorithmGate_oracleFreeAdjoints_eventCost,
    oracleFreePool_empty, divisionMiddle_cost, forward_cost]
  exact add_le_add (NativeBudget.corrected_bound modulus nontrivial)
    (add_le_add (VariableGidney.variableGidney_native_budget modulus.size
      (Inversion.SharedEEA.Accumulate.fittedModulus modulus))
      (NativeBudget.corrected_bound modulus nontrivial))

/-- Actual emitted event cardinality meets the independent two-pass arithmetic envelope. -/
lemma divisionProgram_event_count (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventCost.card ≤ eventBound modulus.size := by
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    AlgorithmGate.algorithmGate_oracleFreeAdjoints_eventCost,
    oracleFreePool_empty, divisionMiddle_cost, forward_cost,
    Multiset.card_add, Multiset.card_add]
  have forward := ForwardResources.corrected_count modulus nontrivial
  have middle := VariableGidney.variableGidney_event_count modulus.size
    (Inversion.SharedEEA.Accumulate.fittedModulus modulus)
  unfold eventBound
  omega

/-- Strict unit depth is bounded from the same actual event pool, including the full adjoint. -/
lemma divisionProgram_depth (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).evaluatedEventDepth (fun _ => 1) ≤ eventBound modulus.size :=
  (ShiftResources.unitDepth_le_count _).trans (divisionProgram_event_count modulus nontrivial)

/-- The native circuit occupies the full declared frame and independent target layout. -/
lemma divisionProgram_qubit_count (modulus : Nat) :
    (frameEncoding modulus.size).width =
      4 * modulus.size + 11 + 4 * modulus.size.size :=
  divisionFrame_width modulus.size

end

end QuantumAlg.MAU.Division.SharedEEA
