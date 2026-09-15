/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Division.SharedEEA.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.InPlace.Placement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Budget
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Resources

/-!
# Independent resources of actual shared-EEA division accumulation

The width-only envelope charges both complete corrected EEA passes and
all stages of the actual variable-product Gidney accumulator. Its entire
shared frame, numerator, and target remain live. This word-only native core
excludes fixed preparation and any supplied flag; runtime composition
must charge those actual additional retained systems and preparation event.
-/

namespace QuantumAlg.MAU.Division.SharedEEA

noncomputable section

open Inversion.SharedEEA
open Multiplication

/-- Independent native-coordinate envelope for both EEA passes and the modular accumulator. -/
def nativeBudget (width : Nat) : ResourcePool .quantum :=
  NativeBudget.corrected width + (VariableGidney.nativeBudget width + NativeBudget.corrected width)

/-- Independent count/depth cap without projecting the circuit under verification. -/
def eventBound (width : Nat) : Nat :=
  2 * ForwardResources.correctedBound width + VariableGidney.eventBound width

/-- Placement and retention preserve every actual middle-program event in order. -/
theorem divisionMiddle_trace (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (middleProgram width modulus).eventTrace =
      (VariableGidney.program width modulus).eventTrace := by
  rw [middleProgram, EncodedBit.FullPlacement.place_eventTrace]
  exact UnitaryCircuit.prodLeft_eventTrace _

/-- The actual placed middle contains every frame, numerator, and target wire, with no addition. -/
theorem divisionMiddle_physical (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (middleProgram width modulus).physical_idx = List.range (frameEncoding width).width := by
  rw [middleProgram, EncodedBit.FullPlacement.place_physical]

/-- The placed middle has precisely the existing native accumulator's event pool. -/
theorem divisionMiddle_cost (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (middleProgram width modulus).eventCost = (VariableGidney.program width modulus).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, divisionMiddle_trace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

private theorem forward_trace (modulus : Nat) (nontrivial : 1 < modulus) :
    (forwardProgram modulus nontrivial).eventTrace =
      (CorrectedSchedule.program modulus nontrivial).eventTrace :=
  UnitaryCircuit.prodLeft_eventTrace (n := modulus.size + modulus.size) _

private theorem forward_cost (modulus : Nat) (nontrivial : 1 < modulus) :
    (forwardProgram modulus nontrivial).eventCost =
      (CorrectedSchedule.program modulus nontrivial).eventCost :=
  UnitaryCircuit.prodLeft_eventCost (n := modulus.size + modulus.size) _

/-- The full actual event trace includes the same corrected forward and its complete reversal. -/
theorem divisionProgram_trace (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventTrace =
      (CorrectedSchedule.program modulus nontrivial).eventTrace ++
        ((VariableGidney.program modulus.size
          (Inversion.SharedEEA.Accumulate.fittedModulus modulus)).eventTrace ++
          (CorrectedSchedule.program modulus nontrivial).eventTrace.reverse) := by
  rw [program, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.seq_eventTrace,
    UnitaryCircuit.dagger_eventTrace, divisionMiddle_trace, forward_trace]

/-- Coordinatewise native multiplicities account for the same full compute and uncompute. -/
theorem divisionProgram_native_budget (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventCost ≤ nativeBudget modulus.size := by
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.dagger_eventCost, divisionMiddle_cost, forward_cost]
  exact add_le_add (NativeBudget.corrected_bound modulus nontrivial)
    (add_le_add (VariableGidney.variableGidney_native_budget modulus.size
      (Inversion.SharedEEA.Accumulate.fittedModulus modulus))
      (NativeBudget.corrected_bound modulus nontrivial))

/-- Actual emitted event cardinality meets the independent two-pass arithmetic envelope. -/
theorem divisionProgram_event_count (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventCost.card ≤ eventBound modulus.size := by
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.dagger_eventCost, divisionMiddle_cost, forward_cost,
    Multiset.card_add, Multiset.card_add]
  have forward := ForwardResources.corrected_count modulus nontrivial
  have middle := VariableGidney.variableGidney_event_count modulus.size
    (Inversion.SharedEEA.Accumulate.fittedModulus modulus)
  unfold eventBound
  omega

/-- Strict unit depth is bounded from the same actual event pool, including the full adjoint. -/
theorem divisionProgram_depth (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).evaluatedEventDepth (fun _ => 1) ≤ eventBound modulus.size :=
  (ShiftResources.unitDepth_le_count _).trans (divisionProgram_event_count modulus nontrivial)

private theorem forward_within (modulus : Nat) (nontrivial : 1 < modulus) :
    (forwardProgram modulus nontrivial).physical_idx ⊆
      List.range (frameEncoding modulus.size).width :=
  UnitaryCircuit.prodLeft_physical_idx_subset_range _
    (InPlacePlacement.corrected_within modulus nontrivial)

/-- Every frame, numerator, and target coordinate is present; no outside coordinate is addressed. -/
theorem divisionProgram_physical (modulus : Nat) (nontrivial : 1 < modulus) (wire : Nat) :
    wire ∈ (program modulus nontrivial).physical_idx ↔
      wire < (frameEncoding modulus.size).width := by
  have forward := forward_within modulus nontrivial
  have backward := UnitaryCircuit.dagger_physical_idx_subset _ forward
  constructor
  · intro present
    change wire ∈ (forwardProgram modulus nontrivial).physical_idx ∪
      ((middleProgram modulus.size
        (Inversion.SharedEEA.Accumulate.fittedModulus modulus)).physical_idx ∪
        (forwardProgram modulus nontrivial).dagger.physical_idx) at present
    rcases List.mem_union_iff.mp present with first | later
    · exact List.mem_range.mp (forward first)
    · rcases List.mem_union_iff.mp later with middle | last
      · rw [divisionMiddle_physical] at middle
        exact List.mem_range.mp middle
      · exact List.mem_range.mp (backward last)
  · intro within
    change wire ∈ (forwardProgram modulus nontrivial).physical_idx ∪
      ((middleProgram modulus.size
        (Inversion.SharedEEA.Accumulate.fittedModulus modulus)).physical_idx ∪
        (forwardProgram modulus nontrivial).dagger.physical_idx)
    apply List.mem_union_right
    apply List.mem_union_left
    rw [divisionMiddle_physical]
    exact List.mem_range.mpr within

/-- Declared physical systems are exactly the complete shared frame, numerator, and target. -/
theorem divisionProgram_qubit_count (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).physical_idx.length =
      4 * modulus.size + 11 + 4 * modulus.size.size := by
  have same : (program modulus nontrivial).physical_idx.Perm
      (List.range (frameEncoding modulus.size).width) :=
    (List.perm_ext_iff_of_nodup (program modulus nontrivial).physical_idx_nodup
      List.nodup_range).mpr (fun wire =>
        (divisionProgram_physical modulus nontrivial wire).trans List.mem_range.symm)
  exact same.length_eq.trans
    (List.length_range.trans (divisionFrame_width modulus.size))

end

end QuantumAlg.MAU.Division.SharedEEA
