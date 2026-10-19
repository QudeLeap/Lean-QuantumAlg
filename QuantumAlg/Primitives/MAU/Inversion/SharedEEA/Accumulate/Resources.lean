/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Budget
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.NativeResources
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources

/-!
# Independent resources of actual shared-EEA modular accumulation

The width-only envelope charges both complete corrected EEA passes and
all stages of the actual coefficient-one Gidney accumulator. Its entire
shared frame and independent target remain live. This word-only native
core excludes fixed preparation and any supplied flag; runtime composition
must charge those actual additional retained systems and preparation event.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Accumulate

noncomputable section

open Multiplication.Accumulate

/-- Independent native-coordinate envelope for both EEA passes and the modular accumulator. -/
def nativeBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  NativeBudget.corrected width + (Gidney.nativeBudget width + NativeBudget.corrected width)

/-- Independent count/depth cap without projecting the circuit under verification. -/
def eventBound (width : Nat) : Nat :=
  2 * ForwardResources.correctedBound width + width * Gidney.stageEventBound width

/-- Placement and retention preserve every actual middle-program event in order. -/
lemma accumulateMiddle_trace (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (middleProgram width modulus).eventTrace = (Gidney.program width modulus 1).eventTrace := by
  rw [middleProgram, EncodedBit.FullPlacement.place_eventTrace]
  exact UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventTrace _ _

/-- The placed middle has precisely the existing native accumulator's event pool. -/
lemma accumulateMiddle_cost (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (middleProgram width modulus).eventCost = (Gidney.program width modulus 1).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, accumulateMiddle_trace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

private lemma forward_trace (modulus : Nat) (nontrivial : 1 < modulus) :
    (forwardProgram modulus nontrivial).eventTrace =
      (CorrectedSchedule.program modulus nontrivial).eventTrace :=
  UnitaryCircuit.prodLeft_eventTrace (n := modulus.size) _

private lemma forward_cost (modulus : Nat) (nontrivial : 1 < modulus) :
    (forwardProgram modulus nontrivial).eventCost =
      (CorrectedSchedule.program modulus nontrivial).eventCost :=
  UnitaryCircuit.prodLeft_eventCost (n := modulus.size) _

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
lemma accumulateProgram_trace (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventTrace =
      (CorrectedSchedule.program modulus nontrivial).eventTrace ++
        ((Gidney.program modulus.size (fittedModulus modulus) 1).eventTrace ++
          ((forwardProgram modulus nontrivial).dagger
            (AlgorithmGate.oracleFreeAdjoints .empty)).eventTrace) := by
  rw [program, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.seq_eventTrace,
    accumulateMiddle_trace, forward_trace]

/-- Coordinatewise native multiplicities account for the same full compute and uncompute. -/
lemma accumulateProgram_native_budget (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventCost ≤ nativeBudget modulus.size := by
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    AlgorithmGate.algorithmGate_oracleFreeAdjoints_eventCost,
    oracleFreePool_empty, accumulateMiddle_cost, forward_cost]
  exact add_le_add (NativeBudget.corrected_bound modulus nontrivial)
    (add_le_add (Gidney.gidneyAccumulate_native_bound modulus.size (fittedModulus modulus) 1)
      (NativeBudget.corrected_bound modulus nontrivial))

/-- Actual emitted event cardinality meets the independent two-pass arithmetic envelope. -/
lemma accumulateProgram_event_count (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventCost.card ≤ eventBound modulus.size := by
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    AlgorithmGate.algorithmGate_oracleFreeAdjoints_eventCost,
    oracleFreePool_empty, accumulateMiddle_cost, forward_cost,
    Multiset.card_add, Multiset.card_add]
  have forward := ForwardResources.corrected_count modulus nontrivial
  have middle := Gidney.gidneyAccumulate_event_count_bound modulus.size (fittedModulus modulus) 1
  unfold eventBound
  omega

/-- Strict unit depth is bounded from the same actual event pool, including the full adjoint. -/
lemma accumulateProgram_depth (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).evaluatedEventDepth (fun _ => 1) ≤ eventBound modulus.size :=
  (ShiftResources.unitDepth_le_count _).trans (accumulateProgram_event_count modulus nontrivial)

/-- The native circuit occupies the full declared frame and independent target layout. -/
lemma accumulateProgram_qubit_count (modulus : Nat) :
    (frameEncoding modulus.size).width =
      3 * modulus.size + 11 + 4 * modulus.size.size :=
  accumulateFrame_width modulus.size

end

end QuantumAlg.MAU.Inversion.SharedEEA.Accumulate
