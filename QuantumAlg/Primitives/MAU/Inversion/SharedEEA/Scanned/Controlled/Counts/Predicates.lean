/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Control
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Terminal.Predicate
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Boundary.Predicate
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern.Counts

/-!
# Native coordinates of the complete original finite-clock predicates

Every source mask and arbitrary-work conjunction is included. The
terminal predicate tests the complete retained clock and divisor; the
boundary predicate additionally retains the actual quotient-zero test.
No reachable-state constant or inactive-branch discount enters a count.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts

noncomputable section

open EncodedBit

private lemma zero_masks_events {Data : Type} {frame : BinaryLabelEncoding Data} {tail : Nat}
    (layout : Word.ZeroTestLayout (encoding := frame) tail) :
    layout.sourceXGates.map (GateSpec.event .empty) =
      List.replicate (tail + 2) (.gate .singleQubit) := by
  rw [Word.ZeroTestLayout.sourceXGates, List.map_ofFn]
  change (List.ofFn fun _ : Fin (tail + 2) =>
    (.gate .singleQubit : Resource.Event (.quantum AlgorithmGate.model .empty))) = _
  exact List.ofFn_const _ _

private lemma zero_conjunction_events {Data : Type} {frame : BinaryLabelEncoding Data}
    {tail : Nat} (layout : Word.ZeroTestLayout (encoding := frame) tail) :
    layout.borrowedAndGates.map (GateSpec.event .empty) =
      List.replicate (if tail = 0 then 1 else 4 * tail) (.gate .toffoli) := by
  apply List.eq_replicate_iff.mpr
  constructor
  · have complete := layout.borrowedZeroGates_length
    simp only [Word.ZeroTestLayout.borrowedZeroGates, List.length_append,
      List.length_reverse, Word.ZeroTestLayout.sourceXGates, List.length_ofFn] at complete
    rw [List.length_map]
    omega
  · intro event present
    obtain ⟨gate, member, rfl⟩ := List.mem_map.mp present
    exact layout.borrowedAndGates_event .empty gate member

private lemma borrowed_zero_events {Data : Type} {frame : BinaryLabelEncoding Data}
    {tail : Nat} (layout : Word.ZeroTestLayout (encoding := frame) tail) :
    layout.borrowedZeroGates.map (GateSpec.event .empty) =
      List.replicate (tail + 2) (.gate .singleQubit) ++
        List.replicate (if tail = 0 then 1 else 4 * tail) (.gate .toffoli) ++
          List.replicate (tail + 2) (.gate .singleQubit) := by
  rw [Word.ZeroTestLayout.borrowedZeroGates, List.map_append, List.map_append,
    List.map_reverse, zero_masks_events, zero_conjunction_events, List.reverse_replicate]

private lemma borrowed_zero_counts {Data : Type} {frame : BinaryLabelEncoding Data}
    {tail : Nat} (layout : Word.ZeroTestLayout (encoding := frame) tail) :
    (layout.borrowedZeroGates.map GateSpec.toffoliMultiplicity).sum =
        (if tail = 0 then 1 else 4 * tail) ∧
      (layout.borrowedZeroGates.map GateSpec.cnotMultiplicity).sum = 0 ∧
      (layout.borrowedZeroGates.map GateSpec.xMultiplicity).sum = 2 * (tail + 2) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← GateSpec.programList_toffoli_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, borrowed_zero_events, ResourcePool.count_ofList]
    simp [List.count_replicate, beq_iff_eq]
  · rw [← GateSpec.programList_cnot_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, borrowed_zero_events, ResourcePool.count_ofList]
    simp [List.count_replicate, beq_iff_eq]
  · rw [← GateSpec.programList_x_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, borrowed_zero_events, ResourcePool.count_ofList]
    simp [List.count_replicate, beq_iff_eq, two_mul]

private lemma single_counts (width : Nat) (field : PredicateLayout.LengthField)
    (enough : 2 ≤ width.size) :
    ((NativePredicate.singleGates width field enough).map GateSpec.toffoliMultiplicity).sum =
        (if width.size - 2 = 0 then 1 else 4 * (width.size - 2)) ∧
      ((NativePredicate.singleGates width field enough).map GateSpec.cnotMultiplicity).sum = 0 ∧
      ((NativePredicate.singleGates width field enough).map GateSpec.xMultiplicity).sum =
        2 * (width.size - 2 + 2) :=
  borrowed_zero_counts (PredicateLayout.single width field enough)

private lemma pair_counts (width : Nat) (first second : PredicateLayout.LengthField)
    (different : first ≠ second) (enough : 2 ≤ width.size) :
    ((NativePredicate.pairGates width first second different enough).map
        GateSpec.toffoliMultiplicity).sum =
        (if 2 * width.size - 2 = 0 then 1 else 4 * (2 * width.size - 2)) ∧
      ((NativePredicate.pairGates width first second different enough).map
        GateSpec.cnotMultiplicity).sum = 0 ∧
      ((NativePredicate.pairGates width first second different enough).map
        GateSpec.xMultiplicity).sum = 2 * (2 * width.size - 2 + 2) :=
  borrowed_zero_counts (PredicateLayout.pair width first second different enough)

private lemma pattern_zero_counts {Data : Type} {frame : BinaryLabelEncoding Data}
    {controls : Nat} (layout : Word.OneDirtyLayout (encoding := frame) controls)
    (enough : 2 ≤ controls) :
    ((layout.patternGates (fun _ => false)).map GateSpec.toffoliMultiplicity).sum =
        Word.OneDirtyLayout.gateCount controls ∧
      ((layout.patternGates (fun _ => false)).map GateSpec.cnotMultiplicity).sum = 0 ∧
      ((layout.patternGates (fun _ => false)).map GateSpec.xMultiplicity).sum = 2 * controls := by
  simpa [Word.OneDirtyLayout.patternMaskIndices] using
    layout.patternGates_native_counts enough (fun _ => false)

/-- Both original zero tests remain in the ordered P-256 phase predicate. -/
lemma p256_ordered_source_counts :
    ((NativeControl.conditionGates 256 (by decide)).map GateSpec.toffoliMultiplicity).sum = 92 ∧
      ((NativeControl.conditionGates 256 (by decide)).map GateSpec.cnotMultiplicity).sum = 0 ∧
      ((NativeControl.conditionGates 256 (by decide)).map GateSpec.xMultiplicity).sum = 54 := by
  have first := single_counts 256 .quotient (by decide)
  have second := pair_counts 256 .quotient .divisor (by decide) (by decide)
  simp only [NativeControl.conditionGates, List.map_append, List.sum_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [first.1, second.1]
    decide
  · rw [first.2.1, second.2.1]
  · rw [first.2.2, second.2.2]
    decide

/-- The complete high-clock repair is paid in addition to the two original low-field tests. -/
lemma p256_terminal_source_counts :
    ((TerminalPredicate.gates 256 (by decide)).map GateSpec.toffoliMultiplicity).sum = 228 ∧
      ((TerminalPredicate.gates 256 (by decide)).map GateSpec.cnotMultiplicity).sum = 0 ∧
      ((TerminalPredicate.gates 256 (by decide)).map GateSpec.xMultiplicity).sum = 94 := by
  have first := single_counts 256 .shift (by decide)
  have second := pair_counts 256 .shift .divisor (by decide) (by decide)
  have third := pattern_zero_counts (TerminalPredicateLayout.layout 256) (by decide)
  simp only [TerminalPredicate.gates, TerminalPredicate.clockDivisorGates,
    List.map_append, List.sum_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [first.1, second.1, third.1]
    decide
  · rw [first.2.1, second.2.1, third.2.1]
  · rw [first.2.2, second.2.2, third.2.2]
    decide

/-- All three actual boundary regions retain their full masks and arbitrary-work conjunctions. -/
lemma p256_boundary_source_counts :
    ((BoundaryPredicate.gates 256 (by decide)).map GateSpec.toffoliMultiplicity).sum = 464 ∧
      ((BoundaryPredicate.gates 256 (by decide)).map GateSpec.cnotMultiplicity).sum = 0 ∧
      ((BoundaryPredicate.gates 256 (by decide)).map GateSpec.xMultiplicity).sum = 148 := by
  have first := pair_counts 256 .quotient .shift (by decide) (by decide)
  have second := pattern_zero_counts (BoundaryPredicateLayout.layout 256 false) (by decide)
  have third := pattern_zero_counts (BoundaryPredicateLayout.layout 256 true) (by decide)
  simp only [BoundaryPredicate.gates, BoundaryPredicate.regionGates,
    List.map_append, List.sum_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [first.1, second.1, third.1]
    decide
  · rw [first.2.1, second.2.1, third.2.1]
  · rw [first.2.2, second.2.2, third.2.2]
    decide

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts
