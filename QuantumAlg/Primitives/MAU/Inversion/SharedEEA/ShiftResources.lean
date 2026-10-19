/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Guarded.Shift
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.LowShift.Increment
import all QuantumAlg.Primitives.MAU.Addition.HRS.IncrementPlacement
import all QuantumAlg.Primitives.MAU.Addition.HRS.Controlled.BorrowedIncrement.Resources
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources
import all QuantumAlg.Core.Base.Depth.EventCount

/-!
# Independent counts for the actual guarded word and complete-clock shifts

The two source shift fragments each execute their real predicate
computation, one forward pair, and two inverse pairs
[LYL+26, sec_EEA/sub_opt.tex:37-40,68-70]. Every pair includes both the
physical word sweep and the actually placed HRS increment or decrement.
The complete clock has its original low field and the two existing
retained high positions; neither controls nor zero payloads discount gates.

The bounds below are closed arithmetic functions of the original width.
Their evidence comes from the same native trace and gate lists, including
the real inverse cleanup. They are not projections chosen as budgets from
the circuit being checked.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ShiftResources

noncomputable section

open EncodedBit

/-- Exact all-width HRS elementary count, independently stated as finite arithmetic. -/
def incrementCount (width : Nat) : Nat :=
  4 * width + 20 * (width - 1) + 4 * (width - 2)

/-- One original guarded fragment has three pairs and at most ten actual predicate gates. -/
def guardedBound (width : Nat) : Nat :=
  9 * (width + 2) + 3 * incrementCount (2 + width.size) + 10

private lemma trace_count {gates : GateModel} {oracles : OracleModel}
    {count : Nat} {layout : QuantumLayout count}
    (body : UnitaryCircuit gates oracles layout) :
    body.eventTrace.length = body.eventCost.card := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  rfl

private lemma dagger_trace_count {count : Nat} {layout : QuantumLayout count}
    (body : UnitaryCircuit AlgorithmGate.model .empty layout) :
    (body.dagger (AlgorithmGate.oracleFreeAdjoints .empty)).eventTrace.length =
      body.eventTrace.length := by
  rw [trace_count, trace_count,
    AlgorithmGate.algorithmGate_oracleFreeAdjoints_eventCost]
  change (Multiset.map (AlgorithmGate.oracleFreeEvent .empty) body.eventCost).card = _
  exact Multiset.card_map _ _

lemma unitDepth_le_count {gates : GateModel} {oracles : OracleModel}
    {count : Nat} {layout : QuantumLayout count}
    (body : UnitaryCircuit gates oracles layout) :
    body.evaluatedEventDepth (fun _ => 1) ≤ body.eventCost.card := by
  calc
    _ ≤ DepthExpr.costEval (fun _ => (1 : Nat)) body.eventDepth :=
      DepthExpr.depthEval_le_costEval (fun _ => 1) body.eventDepth
    _ = _ := (DepthExpr.unitCost_eq_eventPool_card body.eventDepth).trans
      (congrArg Multiset.card (UnitaryCircuit.resourcesFromEventDepth_eq_eventCost body))

private lemma placed_count (extra width : Nat) :
    (Addition.HRS.placedIncrementProgram extra width).eventTrace.length = incrementCount width := by
  rw [trace_count, (Addition.HRS.hrsPlacedIncrement_resources extra width (fun _ => 1)).1]
  exact Addition.HRS.hrsControlledBorrowedIncrement_event_count width

/-- The original low quotient incrementer executes every actual HRS occurrence. -/
lemma low_count (width : Nat) :
    (LowShiftIncrement.program width).eventTrace.length = incrementCount width.size := by
  rw [LowShiftIncrement.program_eventTrace]
  exact placed_count _ _

/-- The enlarged counter's actual placed HRS count includes both original reused high bits. -/
lemma clock_count (width : Nat) :
    (ExtendedClockIncrement.program width).eventTrace.length =
      incrementCount (2 + width.size) := by
  rw [ExtendedClockIncrement.program_eventTrace]
  exact placed_count _ _

private lemma word_count (width : Nat) :
    (Work2PhaseRotation.leftGates width).length = 3 * (width + 2) := by
  have actual := Word.controlledAdjacentShiftLeftGates_length (phase2Bit width)
    (Work2Rotation.word width) (Work2PhaseRotation.separate width)
    (Work2Rotation.word_distinct width)
  change (Work2PhaseRotation.leftGates width).length = 3 * (width + 3 - 1) at actual
  exact actual.trans (congrArg (fun value => 3 * value) (show width + 3 - 1 = width + 2 by omega))

/-- A forward pair includes the complete controlled word sweep and complete HRS clock update. -/
lemma left_count (width : Nat) :
    (ControlledShift.leftProgram width).eventTrace.length =
      3 * (width + 2) + incrementCount (2 + width.size) := by
  rw [ControlledShift.left_eventTrace, List.length_append, List.length_map,
    word_count, clock_count]

/-- The inverse pair retains the same complete occurrence count in the opposite execution order. -/
lemma right_count (width : Nat) :
    (ControlledShift.rightProgram width).eventTrace.length =
      3 * (width + 2) + incrementCount (2 + width.size) := by
  have inverseCount :
      ((ControlledShift.incrementProgram width).dagger
        (AlgorithmGate.oracleFreeAdjoints .empty)).eventTrace.length =
        incrementCount (2 + width.size) := by
    rw [dagger_trace_count]
    rw [ControlledShift.incrementProgram, ControlPlacement.place_eventTrace]
    exact clock_count width
  rw [ControlledShift.right_eventTrace, List.length_append, List.length_map,
    Work2PhaseRotation.rightGates, List.length_reverse, word_count, inverseCount]

/-- Exact counts distinguish the two emitted phase-guard lists without runtime branch discounts. -/
lemma guarded_count (width : Nat) (selected : Bool) :
    (GuardedShift.program width selected).eventTrace.length =
      9 * (width + 2) + 3 * incrementCount (2 + width.size) +
        if selected then 4 else 10 := by
  rw [GuardedShift.program_eventTrace]
  simp only [List.length_append, List.length_map, List.length_reverse,
    left_count, right_count, PhaseGuard.first_length, PhaseGuard.descending_length]
  cases selected <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

/-- The independent common envelope covers either actual guarded shift fragment. -/
lemma guarded_trace_le (width : Nat) (selected : Bool) :
    (GuardedShift.program width selected).eventTrace.length ≤ guardedBound width := by
  rw [guarded_count, guardedBound]
  cases selected <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

/-- The same independent bound covers the actual event pool and its strict unit depth. -/
lemma guarded_resources (width : Nat) (selected : Bool) :
    (GuardedShift.program width selected).eventCost.card ≤ guardedBound width ∧
      (GuardedShift.program width selected).evaluatedEventDepth (fun _ => 1) ≤
        guardedBound width := by
  have count := (trace_count (GuardedShift.program width selected)).symm.le.trans
    (guarded_trace_le width selected)
  exact ⟨count, (unitDepth_le_count (GuardedShift.program width selected)).trans count⟩

end

end QuantumAlg.MAU.Inversion.SharedEEA.ShiftResources
