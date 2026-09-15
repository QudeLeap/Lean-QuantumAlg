/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Terminal.Boundary
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Controlled.Length.Resources

/-!
# Actual resources of the complete-clock native boundary

Both predicate passes, every complete-word swap Toffoli, the four full
Ctrl-source length schedules, and the Iter CNOT are counted in their
actual source order [LYL+26, sec_EEA/sub_regshare.tex:309-313]. The new
predicate masks and longer source controls contribute their real events.
No input-dependent skip is used to lower the native list count or depth.

The formulas use the existing original physical frame, including the two
reused Work1 clock positions. They neither allocate hidden work nor assert
the source paper's gate constant for this repaired implementation.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.TerminalBoundaryResources

noncomputable section

open EncodedBit

/-- Independent envelope for all three actual boundary conjunctions. -/
def predicateBound (width : Nat) : Nat :=
  NativePredicate.gateCount (2 * width.size - 2) +
    (10 * (3 * width.size) + 1) + (10 * (3 * width.size + 2) + 1)

/-- Independent complete-boundary envelope includes both predicate passes and all length writes. -/
def boundaryBound (width : Nat) : Nat :=
  2 * predicateBound width + 3 * (width + 3) +
    ControlledLengthResources.refreshBound width + 1

/-- Both new all-zero patterns satisfy their actual negative-mask and dirty-conjunction bounds. -/
theorem predicate_length_le (width : Nat) (enough : 2 ≤ width.size) :
    (BoundaryPredicate.gates width enough).length ≤ predicateBound width := by
  have low := BoundaryPredicate.regionGates_length_le width false
  have high := BoundaryPredicate.regionGates_length_le width true
  change (BoundaryPredicate.regionGates width false).length ≤ 10 * (3 * width.size + 0) + 1
    at low
  change (BoundaryPredicate.regionGates width true).length ≤ 10 * (3 * width.size + 2) + 1
    at high
  rw [BoundaryPredicate.gates_length]
  unfold predicateBound
  omega

private theorem word_length (width : Nat) :
    (WorkWordExchange.gates width).length = 3 * (width + 3) := by
  have actual := congrArg List.length (WorkWordExchange.program_eventTrace width)
  simpa only [WorkWordExchange.program, GateSpec.programList_eventTrace,
    List.length_map, List.length_replicate] using actual

/-- Literal length includes both exact predicate passes and the actual controlled body. -/
theorem gates_length (width : Nat) (enough : 2 ≤ width.size) :
    (TerminalBoundary.gates width enough).length =
      2 * (BoundaryPredicate.gates width enough).length + 3 * (width + 3) +
        (ControlledLengthRefresh.gates width).length + 1 := by
  have parity : (BoundaryExchange.parityGates width).length = 1 := rfl
  simp only [TerminalBoundary.gates, List.length_append, List.length_reverse, word_length, parity]
  omega

/-- The actual boundary list satisfies its independent finite envelope. -/
theorem gates_length_le (width : Nat) (enough : 2 ≤ width.size) :
    (TerminalBoundary.gates width enough).length ≤ boundaryBound width := by
  rw [gates_length]
  have predicate := predicate_length_le width enough
  have refresh := ControlledLengthResources.refresh_length_le width
  unfold boundaryBound
  omega

/-- Actual event-pool cardinality uses the same complete emitted list. -/
theorem eventCount_le (width : Nat) (enough : 2 ≤ width.size) :
    (TerminalBoundary.program width enough).eventCost.card ≤ boundaryBound width := by
  rw [TerminalBoundary.program, GateSpec.programList_eventCost_card]
  exact gates_length_le width enough

/-- Strict unit depth has no control-off discount or omitted predicate-cleanup events. -/
theorem unitDepth_le (width : Nat) (enough : 2 ≤ width.size) :
    (TerminalBoundary.program width enough).evaluatedEventDepth (fun _ => 1) ≤
      boundaryBound width := by
  rw [TerminalBoundary.program_unitDepth]
  exact gates_length_le width enough

/-- The actual reverse also executes the entire boundary list in the opposite order. -/
theorem reverse_length (width : Nat) (enough : 2 ≤ width.size) :
    (TerminalBoundary.gates width enough).reverse.length =
      (TerminalBoundary.gates width enough).length :=
  List.length_reverse

end

end QuantumAlg.MAU.Inversion.SharedEEA.TerminalBoundaryResources
