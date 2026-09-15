/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.InPlace.Placement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Budget
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.NativeResources

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
def nativeBudget (width : Nat) : ResourcePool .quantum :=
  NativeBudget.corrected width + (Gidney.nativeBudget width + NativeBudget.corrected width)

/-- Independent count/depth cap without projecting the circuit under verification. -/
def eventBound (width : Nat) : Nat :=
  2 * ForwardResources.correctedBound width + width * Gidney.stageEventBound width

/-- Placement and retention preserve every actual middle-program event in order. -/
theorem accumulateMiddle_trace (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (middleProgram width modulus).eventTrace = (Gidney.program width modulus 1).eventTrace := by
  rw [middleProgram, EncodedBit.FullPlacement.place_eventTrace]
  exact UnitaryCircuit.prodLeft_eventTrace _

/-- The actual placed middle contains every original frame and target wire, with no addition. -/
theorem accumulateMiddle_physical (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (middleProgram width modulus).physical_idx = List.range (frameEncoding width).width := by
  rw [middleProgram, EncodedBit.FullPlacement.place_physical]

/-- The placed middle has precisely the existing native accumulator's event pool. -/
theorem accumulateMiddle_cost (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (middleProgram width modulus).eventCost = (Gidney.program width modulus 1).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, accumulateMiddle_trace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

private theorem forward_trace (modulus : Nat) (nontrivial : 1 < modulus) :
    (forwardProgram modulus nontrivial).eventTrace =
      (CorrectedSchedule.program modulus nontrivial).eventTrace :=
  UnitaryCircuit.prodLeft_eventTrace (n := modulus.size) _

private theorem forward_cost (modulus : Nat) (nontrivial : 1 < modulus) :
    (forwardProgram modulus nontrivial).eventCost =
      (CorrectedSchedule.program modulus nontrivial).eventCost :=
  UnitaryCircuit.prodLeft_eventCost (n := modulus.size) _

/-- The full actual event trace includes the same corrected forward and its complete reversal. -/
theorem accumulateProgram_trace (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventTrace =
      (CorrectedSchedule.program modulus nontrivial).eventTrace ++
        ((Gidney.program modulus.size (fittedModulus modulus) 1).eventTrace ++
          (CorrectedSchedule.program modulus nontrivial).eventTrace.reverse) := by
  rw [program, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.seq_eventTrace,
    UnitaryCircuit.dagger_eventTrace, accumulateMiddle_trace, forward_trace]

/-- Coordinatewise native multiplicities account for the same full compute and uncompute. -/
theorem accumulateProgram_native_budget (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventCost ≤ nativeBudget modulus.size := by
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.dagger_eventCost, accumulateMiddle_cost, forward_cost]
  exact add_le_add (NativeBudget.corrected_bound modulus nontrivial)
    (add_le_add (Gidney.gidneyAccumulate_native_bound modulus.size (fittedModulus modulus) 1)
      (NativeBudget.corrected_bound modulus nontrivial))

/-- Actual emitted event cardinality meets the independent two-pass arithmetic envelope. -/
theorem accumulateProgram_event_count (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventCost.card ≤ eventBound modulus.size := by
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.dagger_eventCost, accumulateMiddle_cost, forward_cost,
    Multiset.card_add, Multiset.card_add]
  have forward := ForwardResources.corrected_count modulus nontrivial
  have middle := Gidney.gidneyAccumulate_event_count_bound modulus.size (fittedModulus modulus) 1
  unfold eventBound
  omega

/-- Strict unit depth is bounded from the same actual event pool, including the full adjoint. -/
theorem accumulateProgram_depth (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).evaluatedEventDepth (fun _ => 1) ≤ eventBound modulus.size :=
  (ShiftResources.unitDepth_le_count _).trans (accumulateProgram_event_count modulus nontrivial)

private theorem forward_within (modulus : Nat) (nontrivial : 1 < modulus) :
    (forwardProgram modulus nontrivial).physical_idx ⊆
      List.range (frameEncoding modulus.size).width :=
  UnitaryCircuit.prodLeft_physical_idx_subset_range _
    (InPlacePlacement.corrected_within modulus nontrivial)

/-- Every original frame/target coordinate is present and no outside coordinate is addressed. -/
theorem accumulateProgram_physical (modulus : Nat) (nontrivial : 1 < modulus) (wire : Nat) :
    wire ∈ (program modulus nontrivial).physical_idx ↔
      wire < (frameEncoding modulus.size).width := by
  have forward := forward_within modulus nontrivial
  have backward := UnitaryCircuit.dagger_physical_idx_subset _ forward
  constructor
  · intro present
    change wire ∈ (forwardProgram modulus nontrivial).physical_idx ∪
      ((middleProgram modulus.size (fittedModulus modulus)).physical_idx ∪
        (forwardProgram modulus nontrivial).dagger.physical_idx) at present
    rcases List.mem_union_iff.mp present with first | later
    · exact List.mem_range.mp (forward first)
    · rcases List.mem_union_iff.mp later with middle | last
      · rw [accumulateMiddle_physical] at middle
        exact List.mem_range.mp middle
      · exact List.mem_range.mp (backward last)
  · intro within
    change wire ∈ (forwardProgram modulus nontrivial).physical_idx ∪
      ((middleProgram modulus.size (fittedModulus modulus)).physical_idx ∪
        (forwardProgram modulus nontrivial).dagger.physical_idx)
    apply List.mem_union_right
    apply List.mem_union_left
    rw [accumulateMiddle_physical]
    exact List.mem_range.mpr within

/-- The declared physical systems are exactly the full shared frame and separate target. -/
theorem accumulateProgram_qubit_count (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).physical_idx.length =
      3 * modulus.size + 11 + 4 * modulus.size.size := by
  have same : (program modulus nontrivial).physical_idx.Perm
      (List.range (frameEncoding modulus.size).width) :=
    (List.perm_ext_iff_of_nodup (program modulus nontrivial).physical_idx_nodup
      List.nodup_range).mpr (fun wire =>
        (accumulateProgram_physical modulus nontrivial wire).trans List.mem_range.symm)
  exact same.length_eq.trans
    (List.length_range.trans (accumulateFrame_width modulus.size))

end

end QuantumAlg.MAU.Inversion.SharedEEA.Accumulate
