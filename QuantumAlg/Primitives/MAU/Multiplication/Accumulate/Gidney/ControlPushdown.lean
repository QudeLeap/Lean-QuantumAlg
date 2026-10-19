/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Carrier
import all QuantumAlg.Components.Encoded.BitGates.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.BiFlip
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Arithmetic

/-!
# Control on comparisons in the actual canonical BCBC offset

The bi-flip involution cancels on the unselected branch. Controlling only
the comparison blocks therefore implements the same exact permutation,
including both arbitrary borrowed bits [G17, paper.tex:276-293,319-334].
The native counts and time savings refer to these same emitted lists.
The independent CNOT envelope counts the arithmetic body's X gates and
the selected comparisons separately; it is not a Toffoli allowance.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney.ControlPushdown

noncomputable section

open Nat.FixedWidth BinaryLabelEncoding EncodedBit GateSpec

/-- Place the real offset instructions beside all untouched source coordinates. -/
def unusedLift (extra : Nat)
    (gates : List (GateSpec (Addition.Gidney.encoding (extra + 3)))) :
    List (GateSpec (bodyEncoding extra)) :=
  gates.map (GateSpec.prodRight (finIdentity extra))

/-- Execute an offset block independently of the source selector. -/
def unselected (extra : Nat)
    (gates : List (GateSpec (Addition.Gidney.encoding (extra + 3)))) :
    List (GateSpec (canonicalEncoding extra)) :=
  (unusedLift extra gates).map (GateSpec.prodRight bool)

/-- Expand a block controlled by the existing source selector into native gates. -/
def selected (extra : Nat)
    (gates : List (GateSpec (Addition.Gidney.encoding (extra + 3)))) :
    List (GateSpec (canonicalEncoding extra)) :=
  controlRightList (fun _ => boolBit) (bodyBits extra)
    singleBit_wire (bodyBits_wire extra) (bodyCapacity extra) boolBit
    (unusedLift extra gates)

/-- An unselected block preserves both the selector and unused source prefix. -/
lemma unselected_step (extra : Nat)
    (gates : List (GateSpec (Addition.Gidney.encoding (extra + 3))))
    (state : CanonicalRegisters extra) :
    stepList (unselected extra gates) state =
      (state.1, (state.2.1, stepList gates state.2.2)) := by
  exact (stepList_prodRight bool (unusedLift extra gates) state).trans
    (congrArg (fun output => (state.1, output))
      (stepList_prodRight (finIdentity extra) gates state.2))

/-- The emitted control expansion has its exact two-branch action. -/
lemma selected_step (extra : Nat)
    (gates : List (GateSpec (Addition.Gidney.encoding (extra + 3))))
    (state : CanonicalRegisters extra) :
    stepList (selected extra gates) state =
      (state.1, (state.2.1, if state.1 then stepList gates state.2.2 else state.2.2)) := by
  have actual := controlRightList_step (fun _ => boolBit) (bodyBits extra)
    singleBit_wire (bodyBits_wire extra) (bodyCapacity extra) boolBit
    (unusedLift extra gates) state
  rw [unusedLift, stepList_prodRight] at actual
  apply actual.trans
  rcases state with ⟨selector, unused, body⟩
  cases selector <;> rfl

/-- The actual BCBC list controls only the two comparison blocks. -/
def pushedPivot (extra : Nat) (pivot : Fin (2 ^ (extra + 3) + 1)) :
    List (GateSpec (canonicalEncoding extra)) :=
  ((unselected extra (Addition.Gidney.biFlipGates (extra + 3) pivot) ++
    selected extra (Addition.Gidney.comparisonGates (extra + 3) pivot)) ++
    unselected extra (Addition.Gidney.biFlipGates (extra + 3) pivot)) ++
    selected extra (Addition.Gidney.comparisonGates (extra + 3) pivot)

/-- The selected pivot action preserves every non-target coordinate. -/
def pivotOutput (extra : Nat) (pivot : Fin (2 ^ (extra + 3) + 1))
    (state : CanonicalRegisters extra) : CanonicalRegisters extra :=
  (state.1, (state.2.1,
    if state.1 then Addition.Gidney.pivotOutput pivot state.2.2 else state.2.2))

/-- Two actual bi-flip executions cancel for every flag, word and helper value. -/
lemma biFlip_twice (width : Nat) (pivot : Fin (2 ^ width + 1))
    (state : Addition.Gidney.Registers width) :
    stepList (Addition.Gidney.biFlipGates width pivot)
      (stepList (Addition.Gidney.biFlipGates width pivot) state) = state := by
  rw [Addition.Gidney.gidneyBiFlipGates_step, Addition.Gidney.gidneyBiFlipGates_step]
  rcases state with ⟨flag, word, helper⟩
  cases flag <;>
    simp [Addition.Gidney.biFlipOutput, gidneyBiFlipWord_involutive]

/-- The original four actual blocks implement the complete pivot permutation. -/
lemma bcbc_step (width : Nat) (pivot : Fin (2 ^ width + 1))
    (state : Addition.Gidney.Registers width) :
    stepList (Addition.Gidney.comparisonGates width pivot)
      (stepList (Addition.Gidney.biFlipGates width pivot)
        (stepList (Addition.Gidney.comparisonGates width pivot)
          (stepList (Addition.Gidney.biFlipGates width pivot) state))) =
      Addition.Gidney.pivotOutput pivot state := by
  simpa only [Addition.Gidney.pivotGates, stepList_append]
    using Addition.Gidney.gidneyPivotGates_step width pivot state

/-- The actual selector and every unused coordinate retain their arbitrary input values. -/
lemma pushedPivot_step (extra : Nat) (pivot : Fin (2 ^ (extra + 3) + 1))
    (state : CanonicalRegisters extra) :
    stepList (pushedPivot extra pivot) state = pivotOutput extra pivot state := by
  rcases state with ⟨selector, unused, body⟩
  cases selector <;>
    simp [pushedPivot, stepList_append, unselected_step, selected_step,
      pivotOutput, biFlip_twice, bcbc_step]

/-- Three optimized pivots implement the selected modular offset. -/
def canonicalGates (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) : List (GateSpec (canonicalEncoding extra)) :=
  (pushedPivot extra (offsetFirstPivot modulus constant) ++ pushedPivot extra modulus) ++
    pushedPivot extra (offsetLastPivot modulus constant)

/-- Three actual optimized pivots implement the existing all-label modular offset. -/
lemma canonical_step (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) (state : CanonicalRegisters extra) :
    stepList (canonicalGates extra modulus constant) state =
      canonicalOutput modulus constant state := by
  simp only [canonicalGates, stepList_append, pushedPivot_step]
  rcases state with ⟨selector, unused, flag, input, helper⟩
  cases selector
  · rfl
  · change (true, (unused, (flag,
        (pivotWordOutput (offsetLastPivot modulus constant)
          (pivotWordOutput modulus
            (pivotWordOutput (offsetFirstPivot modulus constant) input)), helper)))) =
      (true, (unused, (flag, (modularWordOutput modulus constant input, helper))))
    exact congrArg (fun word => (true, (unused, (flag, (word, helper)))))
      (gidneyModularWord_three_pivots modulus constant input)

/-- Both borrowed bits and all source coordinates are restored on both selector branches. -/
lemma canonical_restores (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) (state : CanonicalRegisters extra) :
    let final := stepList (canonicalGates extra modulus constant) state
    final.1 = state.1 ∧ final.2.1 = state.2.1 ∧
      final.2.2.1 = state.2.2.1 ∧ final.2.2.2.2 = state.2.2.2.2 := by
  rw [canonical_step]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The number of actual native X occurrences in a gate list. -/
def xCount {Data : Type} {carrier : BinaryLabelEncoding Data}
    (gates : List (GateSpec carrier)) : Nat := (gates.map xMultiplicity).sum

/-- The number of actual native CNOT occurrences in a gate list. -/
def cCount {Data : Type} {carrier : BinaryLabelEncoding Data}
    (gates : List (GateSpec carrier)) : Nat := (gates.map cnotMultiplicity).sum

/-- The number of actual native Toffoli occurrences in a gate list. -/
def tCount {Data : Type} {carrier : BinaryLabelEncoding Data}
    (gates : List (GateSpec carrier)) : Nat := (gates.map toffoliMultiplicity).sum

/-- X occurrences add under literal list concatenation. -/
lemma xCount_append {Data : Type} {carrier : BinaryLabelEncoding Data}
    (left right : List (GateSpec carrier)) :
    xCount (left ++ right) = xCount left + xCount right := by
  simp only [xCount, List.map_append, List.sum_append]

/-- CNOT occurrences add under literal list concatenation. -/
lemma cCount_append {Data : Type} {carrier : BinaryLabelEncoding Data}
    (left right : List (GateSpec carrier)) :
    cCount (left ++ right) = cCount left + cCount right := by
  simp only [cCount, List.map_append, List.sum_append]

/-- Toffoli occurrences add under literal list concatenation. -/
lemma tCount_append {Data : Type} {carrier : BinaryLabelEncoding Data}
    (left right : List (GateSpec carrier)) :
    tCount (left ++ right) = tCount left + tCount right := by
  simp only [tCount, List.map_append, List.sum_append]

/-- Placement beside unused source coordinates preserves all native counts. -/
lemma unused_counts (extra : Nat)
    (gates : List (GateSpec (Addition.Gidney.encoding (extra + 3)))) :
    xCount (unusedLift extra gates) = xCount gates ∧
      cCount (unusedLift extra gates) = cCount gates ∧
      tCount (unusedLift extra gates) = tCount gates := by
  have same := map_event_prodRight (oracles := .empty) (finIdentity extra) gates
  exact ⟨sum_xMultiplicity_eq_of_events_eq .empty same,
    sum_cnotMultiplicity_eq_of_events_eq .empty same,
    sum_toffoliMultiplicity_eq_of_events_eq .empty same⟩

/-- Leaving the selector unused preserves all three native coordinates. -/
lemma unselected_counts (extra : Nat)
    (gates : List (GateSpec (Addition.Gidney.encoding (extra + 3)))) :
    xCount (unselected extra gates) = xCount gates ∧
      cCount (unselected extra gates) = cCount gates ∧
      tCount (unselected extra gates) = tCount gates := by
  have same := map_event_prodRight (oracles := .empty) bool (unusedLift extra gates)
  have inner := unused_counts extra gates
  exact ⟨(sum_xMultiplicity_eq_of_events_eq .empty same).trans inner.1,
    (sum_cnotMultiplicity_eq_of_events_eq .empty same).trans inner.2.1,
    (sum_toffoliMultiplicity_eq_of_events_eq .empty same).trans inner.2.2⟩

/-- The actual selector expansion has its exact native coordinate formula. -/
lemma selected_counts (extra : Nat)
    (gates : List (GateSpec (Addition.Gidney.encoding (extra + 3)))) :
    xCount (selected extra gates) = 0 ∧
      cCount (selected extra gates) = xCount gates ∧
      tCount (selected extra gates) = cCount gates + 4 * tCount gates := by
  have actual := controlRightList_native_counts (fun _ => boolBit) (bodyBits extra)
    singleBit_wire (bodyBits_wire extra) (bodyCapacity extra) boolBit (unusedLift extra gates)
  have inner := unused_counts extra gates
  exact ⟨actual.1, actual.2.1.trans inner.1, by
    calc
      tCount (selected extra gates) = cCount (unusedLift extra gates) +
          4 * tCount (unusedLift extra gates) := actual.2.2
      _ = cCount gates + 4 * tCount gates := by rw [inner.2.1, inner.2.2]⟩

/-- The optimized four-block pivot has these exact actual native counts. -/
lemma pivot_counts (extra : Nat) (pivot : Fin (2 ^ (extra + 3) + 1)) :
    xCount (pushedPivot extra pivot) =
        2 * xCount (Addition.Gidney.biFlipGates (extra + 3) pivot) ∧
      cCount (pushedPivot extra pivot) =
        2 * cCount (Addition.Gidney.biFlipGates (extra + 3) pivot) +
          2 * xCount (Addition.Gidney.comparisonGates (extra + 3) pivot) ∧
      tCount (pushedPivot extra pivot) =
        2 * tCount (Addition.Gidney.biFlipGates (extra + 3) pivot) +
          2 * (cCount (Addition.Gidney.comparisonGates (extra + 3) pivot) +
            4 * tCount (Addition.Gidney.comparisonGates (extra + 3) pivot)) := by
  have lifted := unselected_counts extra (Addition.Gidney.biFlipGates (extra + 3) pivot)
  have controlled := selected_counts extra (Addition.Gidney.comparisonGates (extra + 3) pivot)
  constructor
  · simp only [pushedPivot, xCount_append, lifted.1, controlled.1]
    omega
  constructor
  · simp only [pushedPivot, cCount_append, lifted.2.1, controlled.2.1]
    omega
  · simp only [pushedPivot, tCount_append, lifted.2.2, controlled.2.2]
    omega

/-- The exact Toffoli occurrences removed from one selected pivot. -/
def pivotToffoliSaving (extra : Nat) (pivot : Fin (2 ^ (extra + 3) + 1)) : Nat :=
  2 * cCount (Addition.Gidney.biFlipGates (extra + 3) pivot) +
    6 * tCount (Addition.Gidney.biFlipGates (extra + 3) pivot)

/-- The exact serial native instructions removed from one selected pivot. -/
def pivotTimeSaving (extra : Nat) (pivot : Fin (2 ^ (extra + 3) + 1)) : Nat :=
  6 * tCount (Addition.Gidney.biFlipGates (extra + 3) pivot)

/-- Exact Toffoli and serial-time savings compare the two actual pivot lists. -/
lemma selectedPivot_savings (extra : Nat) (pivot : Fin (2 ^ (extra + 3) + 1)) :
    tCount (selected extra (Addition.Gidney.pivotGates (extra + 3) pivot)) =
        tCount (pushedPivot extra pivot) + pivotToffoliSaving extra pivot ∧
      (selected extra (Addition.Gidney.pivotGates (extra + 3) pivot)).length =
        (pushedPivot extra pivot).length + pivotTimeSaving extra pivot := by
  have old := selected_counts extra (Addition.Gidney.pivotGates (extra + 3) pivot)
  have replacement := pivot_counts extra pivot
  constructor
  · rw [old.2.2, replacement.2.2]
    simp only [Addition.Gidney.pivotGates, cCount_append, tCount_append, pivotToffoliSaving]
    ring
  · rw [length_eq_multiplicity_sums, length_eq_multiplicity_sums]
    change xCount _ + cCount _ + tCount _ =
      xCount _ + cCount _ + tCount _ + pivotTimeSaving extra pivot
    rw [old.1, old.2.1, old.2.2, replacement.1, replacement.2.1, replacement.2.2]
    simp only [Addition.Gidney.pivotGates, xCount_append, cCount_append, tCount_append,
      pivotTimeSaving]
    ring

/-- The sum of actual Toffoli savings across the three pivots. -/
def offsetToffoliSaving (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) : Nat :=
  pivotToffoliSaving extra (offsetFirstPivot modulus constant) +
    pivotToffoliSaving extra modulus + pivotToffoliSaving extra (offsetLastPivot modulus constant)

/-- The sum of actual serial-time savings across the three pivots. -/
def offsetTimeSaving (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) : Nat :=
  pivotTimeSaving extra (offsetFirstPivot modulus constant) +
    pivotTimeSaving extra modulus + pivotTimeSaving extra (offsetLastPivot modulus constant)

/-- Exact savings compare against the actual original canonical control expansion. -/
lemma canonical_savings (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) :
    tCount (originalCanonicalGates extra modulus constant) =
        tCount (canonicalGates extra modulus constant) +
          offsetToffoliSaving extra modulus constant ∧
      (originalCanonicalGates extra modulus constant).length =
        (canonicalGates extra modulus constant).length + offsetTimeSaving extra modulus constant :=
  by
    have original : originalCanonicalGates extra modulus constant =
        selected extra (Addition.Gidney.modularOffsetGates (extra + 3) modulus constant) := rfl
    have old := selected_counts extra
      (Addition.Gidney.modularOffsetGates (extra + 3) modulus constant)
    have first := pivot_counts extra (offsetFirstPivot modulus constant)
    have middle := pivot_counts extra modulus
    have last := pivot_counts extra (offsetLastPivot modulus constant)
    constructor
    · rw [original, old.2.2]
      simp only [canonicalGates, tCount_append, first.2.2, middle.2.2, last.2.2,
        Addition.Gidney.modularOffsetGates, Addition.Gidney.pivotGates,
        cCount_append, tCount_append, offsetToffoliSaving, pivotToffoliSaving]
      ring
    · rw [original, length_eq_multiplicity_sums, length_eq_multiplicity_sums]
      change xCount _ + cCount _ + tCount _ =
        xCount _ + cCount _ + tCount _ + offsetTimeSaving extra modulus constant
      rw [old.1, old.2.1, old.2.2]
      simp only [canonicalGates, xCount_append, cCount_append, tCount_append,
        first.1, first.2.1, first.2.2, middle.1, middle.2.1, middle.2.2,
        last.1, last.2.1, last.2.2, Addition.Gidney.modularOffsetGates,
        Addition.Gidney.pivotGates, xCount_append, cCount_append, tCount_append,
        offsetTimeSaving, pivotTimeSaving]
      ring

/-- Every actual X, CNOT and Toffoli instruction has unit quantum duration. -/
lemma native_time {Data : Type} {carrier : BinaryLabelEncoding Data}
    (gates : List (GateSpec carrier)) :
    (programList (QubitLayout.canonical _) .empty gates).evaluatedEventDepth
      Resource.Event.quantumDuration = gates.length := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      rw [programList, UnitaryCircuit.evaluatedEventDepth_seq, ih]
      have head : (gate.program (QubitLayout.canonical _) .empty).evaluatedEventDepth
          Resource.Event.quantumDuration = 1 := by
        rw [UnitaryCircuit.evaluatedEventDepth, program_eventDepth]
        cases gate <;> rfl
      rw [head, List.length_cons]
      omega

/-- The X occurrences of any native gate list are bounded by its literal length. -/
private lemma xCount_le_length {Data : Type} {carrier : BinaryLabelEncoding Data}
    (gates : List (GateSpec carrier)) : xCount gates ≤ gates.length := by
  have counts := length_eq_multiplicity_sums gates
  change (gates.map xMultiplicity).sum ≤ gates.length
  omega

/-- The bi-flip is already flag-controlled, so its actual large-width list emits no X. -/
lemma biFlip_xCount (extra : Nat) (pivot : Fin (2 ^ (extra + 3) + 1)) :
    xCount (Addition.Gidney.biFlipGates (extra + 3) pivot) = 0 := by
  have notSmall : ¬extra + 3 ≤ 2 := by omega
  change ((Addition.Gidney.biFlipGates (extra + 3) pivot).map xMultiplicity).sum = 0
  rw [Addition.Gidney.biFlipGates, dif_neg notSmall, Addition.Gidney.largeBiFlipGates]
  exact (controlRightList_native_counts _ _ _ _ _ _ _).1

/-- Each native CNOT in the bi-flip is an actual X of its unselected arithmetic body. -/
lemma biFlip_cCount_eq_body_xCount (extra : Nat)
    (pivot : Fin (2 ^ (extra + 3) + 1)) :
    cCount (Addition.Gidney.biFlipGates (extra + 3) pivot) =
      xCount (Addition.Gidney.biFlipBodyGates (extra + 3) pivot) := by
  have notSmall : ¬extra + 3 ≤ 2 := by omega
  change ((Addition.Gidney.biFlipGates (extra + 3) pivot).map cnotMultiplicity).sum = _
  rw [Addition.Gidney.biFlipGates, dif_neg notSmall, Addition.Gidney.largeBiFlipGates]
  exact (controlRightList_native_counts _ _ _ _ _ _ _).2.1

/-- The arithmetic body contains one HRS offset and exactly one X per target bit. -/
lemma biFlipBody_length_bound (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (Addition.Gidney.biFlipBodyGates width pivot).length ≤
      Addition.Gidney.constantOffsetEventBound width + width := by
  have bound := Addition.HRS.hrsOneDirtyGates_length_bound width
    (Addition.Gidney.negatedPivot width pivot.val)
  have complementLength : (Addition.Gidney.complementBodyGates width).length = width :=
    (List.length_map (as := Addition.Gidney.complementGates width)
      (f := GateSpec.prodLeft bool)).trans List.length_ofFn
  rw [Addition.Gidney.biFlipBodyGates, List.length_append, complementLength]
  exact Nat.add_le_add_right bound width

/-- The independent bi-flip CNOT cap follows from the arithmetic body's native X count. -/
lemma biFlip_cCount_bound (extra : Nat) (pivot : Fin (2 ^ (extra + 3) + 1)) :
    cCount (Addition.Gidney.biFlipGates (extra + 3) pivot) ≤
      Addition.Gidney.constantOffsetEventBound (extra + 3) + (extra + 3) := by
  rw [biFlip_cCount_eq_body_xCount]
  exact (xCount_le_length _).trans (biFlipBody_length_bound _ pivot)

/-- Selected comparisons contribute their actual native X occurrences to CNOT. -/
lemma comparison_xCount_bound (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    xCount (Addition.Gidney.comparisonGates width pivot) ≤
      Addition.Gidney.comparisonEventBound width :=
  (xCount_le_length _).trans (Addition.Gidney.gidneyComparisonGates_length_bound width pivot)

/-- Two bi-flips and two selected comparisons independently bound one pivot's CNOT count. -/
def pivotCnotBound (width : Nat) : Nat :=
  2 * (Addition.Gidney.constantOffsetEventBound width + width +
    Addition.Gidney.comparisonEventBound width)

/-- Three pivots use this independent CNOT envelope, including zero-pivot branches. -/
def canonicalCnotBound (width : Nat) : Nat := 3 * pivotCnotBound width

/-- The actual optimized pivot has zero single-qubit instructions. -/
lemma pushedPivot_xCount (extra : Nat) (pivot : Fin (2 ^ (extra + 3) + 1)) :
    xCount (pushedPivot extra pivot) = 0 := by
  rw [(pivot_counts extra pivot).1, biFlip_xCount, Nat.mul_zero]

/-- The complete actual optimized canonical offset preserves its zero-X contract. -/
lemma canonical_xCount (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) :
    xCount (canonicalGates extra modulus constant) = 0 := by
  simp only [canonicalGates, xCount_append, pushedPivot_xCount, Nat.zero_add]

/-- One pivot's CNOT bound is proved from its own exact native count formula. -/
lemma pushedPivot_cCount_bound (extra : Nat) (pivot : Fin (2 ^ (extra + 3) + 1)) :
    cCount (pushedPivot extra pivot) ≤ pivotCnotBound (extra + 3) := by
  have biFlip := biFlip_cCount_bound extra pivot
  have comparison := comparison_xCount_bound (extra + 3) pivot
  rw [(pivot_counts extra pivot).2.1, pivotCnotBound]
  omega

/-- The canonical CNOT envelope depends only on width, not a projected run resource witness. -/
lemma canonical_cCount_bound (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) :
    cCount (canonicalGates extra modulus constant) ≤ canonicalCnotBound (extra + 3) := by
  have first := pushedPivot_cCount_bound extra (offsetFirstPivot modulus constant)
  have middle := pushedPivot_cCount_bound extra modulus
  have last := pushedPivot_cCount_bound extra (offsetLastPivot modulus constant)
  simp only [canonicalGates, cCount_append, canonicalCnotBound]
  omega

/-- The literal original full-control list obeys the independent offset envelope. -/
lemma originalCanonical_length_bound (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (originalCanonicalGates extra modulus constant).length ≤
      4 * Addition.Gidney.modularOffsetEventBound (extra + 3) := by
  have bound := controlRightList_length_bound (fun _ => boolBit) (bodyBits extra)
    singleBit_wire (bodyBits_wire extra) (bodyCapacity extra) boolBit
    (bodyGates extra modulus constant)
  have bodyLength : (bodyGates extra modulus constant).length =
      (Addition.Gidney.modularOffsetProgram (extra + 3) modulus constant).eventCost.card := by
    rw [Addition.Gidney.modularOffsetProgram, programList_eventCost_card]
    exact List.length_map (GateSpec.prodRight (finIdentity extra))
  exact bound.trans (by
    rw [bodyLength]
    exact Nat.mul_le_mul_left 4
      (Addition.Gidney.gidneyModularOffset_event_count_bound (extra + 3) modulus constant))

/-- Pushing control through the three actual pivots preserves the independent event cap. -/
lemma canonical_length_bound (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (canonicalGates extra modulus constant).length ≤
      4 * Addition.Gidney.modularOffsetEventBound (extra + 3) := by
  have savings := (canonical_savings extra modulus constant).2
  have bound := originalCanonical_length_bound extra modulus constant
  omega

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney.ControlPushdown
