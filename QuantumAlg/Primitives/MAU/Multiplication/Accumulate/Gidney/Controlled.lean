/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Gates
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Stage.Placement
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Carrier
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.ControlPushdown
import all QuantumAlg.Components.Encoded.BitGates.Resources
import all QuantumAlg.Core.Base.Accounting.Support

/-!
# Two total pivot controls on the actual complete accumulation carrier

The source selector and one outer-word bit are the two external controls
of each pivot. Only comparisons receive both controls; the actual flag-
controlled bi-flips cancel on either unselected branch. Physical placement
and every unused coordinate are preserved [G17, paper.tex:276-293,319-334].
Zero-, one- and two-bit paths keep their original complete gate lists.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney.ControlPushdown

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth BinaryLabelEncoding EncodedBit GateSpec


/-- Physical lenses for the original two-word accumulator carrier. -/
def wordBits (width : Nat) : Fin (encoding width).width → EncodedBit (encoding width) :=
  productBit (finIdentityBit width) (finIdentityBit width)

/-- Every two-word lens addresses its original physical position. -/
lemma wordBits_wire (width : Nat) (position : Fin (encoding width).width) :
    (wordBits width position).wire = position :=
  productBit_wire (left := finIdentity width) (right := finIdentity width)
    (finIdentityBit width) (finIdentityBit width) (fun _ => rfl) (fun _ => rfl) position

/-- The original fully controlled stage on the certified word placement. -/
def originalPlacedStageGates (extra : Nat) (selector : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    List (GateSpec (encoding (extra + 3))) :=
  (originalCanonicalGates extra modulus constant).map
    (stageFullPlacement extra selector).placeGate

/-- The literal original placed stage obeys its independent envelope. -/
lemma originalPlaced_length_bound (extra : Nat) (selector : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (originalPlacedStageGates extra selector modulus constant).length ≤
      stageEventBound (extra + 3) := by
  simpa only [originalPlacedStageGates, List.length_map, stageEventBound,
    if_neg (show ¬extra + 3 ≤ 2 by omega)] using
      originalCanonical_length_bound extra modulus constant
/-- An arbitrary external word beside the original source and target words. -/
abbrev OuterRegisters (outerWidth width : Nat) :=
  Fin (2 ^ outerWidth) × Registers width

/-- The full external-word and two-word physical layout. -/
abbrev outerEncoding (outerWidth width : Nat) :
    BinaryLabelEncoding (OuterRegisters outerWidth width) :=
  prod (finIdentity outerWidth) (encoding width)

/-- The chosen outer-word bit in the fixed little-endian wire convention. -/
def outerBit (outerWidth : Nat) (address : Fin outerWidth) :
    EncodedBit (finIdentity outerWidth) :=
  finIdentityBit outerWidth (WireAddress.littleEndianWire address)

/-- The addressed external bit reads its exact finite-word test bit. -/
lemma outerBit_get (outerWidth : Nat) (address : Fin outerWidth)
    (word : Fin (2 ^ outerWidth)) :
    (outerBit outerWidth address).get word = word.val.testBit address.val := by
  change word.val.testBit
    (WireAddress.bitIndex (WireAddress.littleEndianWire address)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

/-- Place a real two-word gate list beside an untouched external word. -/
def outerLift (outerWidth : Nat) {width : Nat}
    (body : List (GateSpec (encoding width))) :
    List (GateSpec (outerEncoding outerWidth width)) :=
  body.map (GateSpec.prodRight (finIdentity outerWidth))

/-- Lifting preserves the complete arbitrary external word exactly. -/
lemma outerLift_step (outerWidth : Nat) {width : Nat}
    (body : List (GateSpec (encoding width))) (state : OuterRegisters outerWidth width) :
    stepList (outerLift outerWidth body) state = (state.1, stepList body state.2) :=
  stepList_prodRight (finIdentity outerWidth) body state

/-- Expand one external control using existing carrier wires only. -/
def outerControl (outerWidth width : Nat) (large : 2 ≤ width)
    (address : Fin outerWidth) (body : List (GateSpec (encoding width))) :
    List (GateSpec (outerEncoding outerWidth width)) :=
  controlRightList (finIdentityBit outerWidth) (wordBits width)
    (fun _ => rfl) (wordBits_wire width)
    (by
      have positive := address.isLt
      change 5 ≤ outerWidth + (width + width)
      omega)
    (outerBit outerWidth address) body

/-- The actual outer expansion has its exact selected and idle branches. -/
lemma outerControl_step (outerWidth width : Nat) (large : 2 ≤ width)
    (address : Fin outerWidth) (body : List (GateSpec (encoding width)))
    (state : OuterRegisters outerWidth width) :
    stepList (outerControl outerWidth width large address body) state =
      (state.1, if state.1.val.testBit address.val then stepList body state.2 else state.2) := by
  have actual := controlRightList_step (finIdentityBit outerWidth)
    (wordBits width) (fun _ => rfl) (wordBits_wire width)
    (by
      have positive := address.isLt
      change 5 ≤ outerWidth + (width + width)
      omega)
    (outerBit outerWidth address) body state
  simpa only [outerControl, outerBit_get] using actual

/-- Place a canonical gate list using the certified source-word regrouping. -/
def relocate (extra : Nat) (selector : Fin (extra + 3))
    (body : List (GateSpec (canonicalEncoding extra))) :
    List (GateSpec (encoding (extra + 3))) :=
  body.map (stageFullPlacement extra selector).placeGate

/-- The real placement acts by its exact complete-carrier equivalence. -/
lemma relocate_step (extra : Nat) (selector : Fin (extra + 3))
    (body : List (GateSpec (canonicalEncoding extra))) (state : Registers (extra + 3)) :
    stepList (relocate extra selector body) state =
      (stageFullPlacement extra selector).step (stepList body) state :=
  FullPlacement.placeGates_step _ body state

/-- Certified physical placement retains each actual native event label. -/
lemma relocate_events (extra : Nat) (selector : Fin (extra + 3))
    (body : List (GateSpec (canonicalEncoding extra))) :
    (relocate extra selector body).map (event .empty) = body.map (event .empty) := by
  simp only [relocate, List.map_map, Function.comp_def, FullPlacement.placeGate_event]

/-- Two placed bi-flips cancel on every allowed dirty input. -/
lemma relocated_B_twice (extra : Nat) (selector : Fin (extra + 3))
    (pivot : Fin (2 ^ (extra + 3) + 1)) (state : Registers (extra + 3)) :
    let body := relocate extra selector
      (unselected extra (Addition.Gidney.biFlipGates (extra + 3) pivot))
    stepList body (stepList body state) = state := by
  dsimp only
  rw [relocate_step, relocate_step]
  simp only [FullPlacement.step, Equiv.apply_symm_apply, unselected_step, biFlip_twice]
  exact (stageFullPlacement extra selector).grouping.symm_apply_apply state

/-- The actual placed BCBC list with two external controls on comparisons only. -/
def twoPivot (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (pivot : Fin (2 ^ (extra + 3) + 1)) :
    List (GateSpec (outerEncoding outerWidth (extra + 3))) :=
  let b := relocate extra selector
    (unselected extra (Addition.Gidney.biFlipGates (extra + 3) pivot))
  let c := relocate extra selector
    (selected extra (Addition.Gidney.comparisonGates (extra + 3) pivot))
  ((outerLift outerWidth b ++
    outerControl outerWidth (extra + 3) (by omega) address c) ++ outerLift outerWidth b) ++
    outerControl outerWidth (extra + 3) (by omega) address c

/-- The total selected pivot action with the complete outer word retained. -/
def twoPivotOutput (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (pivot : Fin (2 ^ (extra + 3) + 1))
    (state : OuterRegisters outerWidth (extra + 3)) : OuterRegisters outerWidth (extra + 3) :=
  (state.1, if state.1.val.testBit address.val then
    (stageFullPlacement extra selector).step (pivotOutput extra pivot) state.2 else state.2)

/-- Both external branches use the actual placed BCBC list and restore arbitrary work. -/
lemma twoPivot_step (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (pivot : Fin (2 ^ (extra + 3) + 1))
    (state : OuterRegisters outerWidth (extra + 3)) :
    stepList (twoPivot outerWidth extra address selector pivot) state =
      twoPivotOutput outerWidth extra address selector pivot state := by
  by_cases enabled : state.1.val.testBit address.val = true
  · have inner := relocate_step extra selector (pushedPivot extra pivot) state.2
    rw [FullPlacement.step, pushedPivot_step] at inner
    simpa only [twoPivot, twoPivotOutput, stepList_append, outerLift_step,
      outerControl_step, enabled, if_true, relocate, pushedPivot, List.map_append,
      stepList_append, FullPlacement.step] using congrArg (fun body => (state.1, body)) inner
  · have twice := relocated_B_twice extra selector pivot state.2
    simpa only [twoPivot, twoPivotOutput, stepList_append, outerLift_step,
      outerControl_step, enabled, Bool.false_eq_true, if_false]
      using congrArg (fun body => (state.1, body)) twice

/-- Three actual doubly selected pivots on the original two-word placement. -/
def twoStage (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) :
    List (GateSpec (outerEncoding outerWidth (extra + 3))) :=
  (twoPivot outerWidth extra address selector (offsetFirstPivot modulus constant) ++
    twoPivot outerWidth extra address selector modulus) ++
    twoPivot outerWidth extra address selector (offsetLastPivot modulus constant)

/-- The three pivots implement the full selected offset on every joint label. -/
lemma twoStage_step (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) (state : OuterRegisters outerWidth (extra + 3)) :
    stepList (twoStage outerWidth extra address selector modulus constant) state =
      (state.1, if state.1.val.testBit address.val then
        selectedOutput selector modulus constant state.2 else state.2) := by
  by_cases enabled : state.1.val.testBit address.val = true
  · have inner := gidneyPlacedStageGates_step extra selector modulus constant state.2
    rw [placedStageGates, Gidney.canonicalGates, FullPlacement.placeGates_step,
      FullPlacement.step, canonicalGates,
      stepList_append, stepList_append] at inner
    simp only [pushedPivot_step] at inner
    simpa only [twoStage, stepList_append, twoPivot_step, twoPivotOutput,
      enabled, if_true, FullPlacement.step, Equiv.apply_symm_apply]
      using congrArg (fun body => (state.1, body)) inner
  · simp only [twoStage, stepList_append, twoPivot_step, twoPivotOutput,
      enabled, Bool.false_eq_true, if_false]

/-- The external full word and the original two-word source are preserved exactly. -/
lemma twoStage_restores (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) (state : OuterRegisters outerWidth (extra + 3)) :
    let final := stepList (twoStage outerWidth extra address selector modulus constant) state
    final.1 = state.1 ∧ final.2.1 = state.2.1 := by
  rw [twoStage_step]
  constructor
  · rfl
  · split_ifs <;> rfl

/-- The original literal control expansion, including both small-width branches. -/
def originalControlled (outerWidth width : Nat) (address : Fin outerWidth)
    (body : List (GateSpec (encoding width))) :
    List (GateSpec (outerEncoding outerWidth width)) :=
  if small : width ≤ 1 then
    body.map (controlSmall (outerBit outerWidth address)
      (by change width + width ≤ 2; omega))
  else outerControl outerWidth width (by omega) address body

/-- The original expansion has exact coherent branch semantics. -/
lemma originalControlled_step (outerWidth width : Nat) (address : Fin outerWidth)
    (body : List (GateSpec (encoding width))) (state : OuterRegisters outerWidth width) :
    stepList (originalControlled outerWidth width address body) state =
      (state.1, if state.1.val.testBit address.val then stepList body state.2 else state.2) := by
  by_cases small : width ≤ 1
  · simp only [originalControlled, dif_pos small]
    rw [controlSmallList_step, outerBit_get]
  · simp only [originalControlled, dif_neg small]
    exact outerControl_step outerWidth width (by omega) address body state

/-- The width-complete stage keeps literal small paths and optimizes larger widths. -/
def twoStageGates (outerWidth : Nat) : (width : Nat) → Fin outerWidth → Fin width →
    (modulus : Fin (2 ^ width + 1)) → Fin (modulus.val + 1) →
    List (GateSpec (outerEncoding outerWidth width))
  | 0, _, selector, _, _ => Fin.elim0 selector
  | 1, address, selector, modulus, constant => originalControlled outerWidth 1 address
      (Gidney.stageGates 1 selector modulus constant)
  | 2, address, selector, modulus, constant => originalControlled outerWidth 2 address
      (Gidney.stageGates 2 selector modulus constant)
  | extra + 3, address, selector, modulus, constant =>
      twoStage outerWidth extra address selector modulus constant

/-- Every width has the same exact total selected offset semantics. -/
lemma twoStageGates_step (outerWidth : Nat) : (width : Nat) →
    (address : Fin outerWidth) → (selector : Fin width) →
    (modulus : Fin (2 ^ width + 1)) → (constant : Fin (modulus.val + 1)) →
    (state : OuterRegisters outerWidth width) →
    stepList (twoStageGates outerWidth width address selector modulus constant) state =
      (state.1, if state.1.val.testBit address.val then
        selectedOutput selector modulus constant state.2 else state.2)
  | 0, _, selector, _, _, _ => Fin.elim0 selector
  | 1, address, selector, modulus, constant, state => by
      rw [twoStageGates, originalControlled_step, gidneyStageGates_step]
  | 2, address, selector, modulus, constant, state => by
      rw [twoStageGates, originalControlled_step, gidneyStageGates_step]
  | extra + 3, address, selector, modulus, constant, state =>
      twoStage_step outerWidth extra address selector modulus constant state

/-- The actual ordered selected-add prefix under one retained outer-word bit. -/
def twoPrefix (outerWidth width : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    (count : Nat) → count ≤ width → List (GateSpec (outerEncoding outerWidth width))
  | 0, _ => []
  | index + 1, within => twoPrefix outerWidth width address modulus coefficient index (by omega) ++
      twoStageGates outerWidth width address ⟨index, by omega⟩ modulus
        (accumulateConstant modulus coefficient index)

/-- Every prefix retains the full outer word and exact modular accumulation action. -/
lemma twoPrefix_step (outerWidth width : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ width + 1)) (coefficient count : Nat) (within : count ≤ width)
    (state : OuterRegisters outerWidth width) :
    stepList (twoPrefix outerWidth width address modulus coefficient count within) state =
      (state.1, if state.1.val.testBit address.val then
        prefixOutput modulus coefficient count state.2 else state.2) := by
  induction count with
  | zero =>
      cases state.1.val.testBit address.val <;> rfl
  | succ index ih =>
      rw [twoPrefix, stepList_append, ih (by omega), twoStageGates_step]
      cases state.1.val.testBit address.val <;> rfl

/-- The complete outer-controlled accumulator with unchanged literal small paths. -/
def twoGates (outerWidth : Nat) : (width : Nat) → Fin outerWidth →
    (modulus : Fin (2 ^ width + 1)) → Nat →
    List (GateSpec (outerEncoding outerWidth width))
  | 0, address, modulus, coefficient => originalControlled outerWidth 0 address
      (Gidney.gates 0 modulus coefficient)
  | 1, address, modulus, coefficient => originalControlled outerWidth 1 address
      (Gidney.gates 1 modulus coefficient)
  | 2, address, modulus, coefficient => originalControlled outerWidth 2 address
      (Gidney.gates 2 modulus coefficient)
  | extra + 3, address, modulus, coefficient =>
      twoPrefix outerWidth (extra + 3) address modulus coefficient (extra + 3) (Nat.le_refl _)

/-- All source, target and outer-word labels follow the exact accumulation action. -/
lemma twoGates_step (outerWidth : Nat) : (width : Nat) →
    (address : Fin outerWidth) → (modulus : Fin (2 ^ width + 1)) → (coefficient : Nat) →
    (state : OuterRegisters outerWidth width) →
    stepList (twoGates outerWidth width address modulus coefficient) state =
      (state.1, if state.1.val.testBit address.val then
        prefixOutput modulus coefficient width state.2 else state.2)
  | 0, address, modulus, coefficient, state => by
      rw [twoGates, originalControlled_step, gidneyAccumulateGates_step]
  | 1, address, modulus, coefficient, state => by
      rw [twoGates, originalControlled_step, gidneyAccumulateGates_step]
  | 2, address, modulus, coefficient, state => by
      rw [twoGates, originalControlled_step, gidneyAccumulateGates_step]
  | extra + 3, address, modulus, coefficient, state =>
      twoPrefix_step outerWidth (extra + 3) address modulus coefficient
        (extra + 3) (Nat.le_refl _) state

/-- Compile exactly the gate list used by the semantic and resource proofs. -/
def twoProgram (outerWidth width : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (outerEncoding outerWidth width).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty
    (twoGates outerWidth width address modulus coefficient)

/-- Exact joint phase, every external label and every allowed dirty source label are included. -/
lemma twoAccumulator_realizes (outerWidth width : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    UnitaryCircuit.Realizes (outerEncoding outerWidth width)
      (twoProgram outerWidth width address modulus coefficient) environment
      (fun state => (state.1, if state.1.val.testBit address.val then
        prefixOutput modulus coefficient width state.2 else state.2)) :=
  realizesList_congrStep _ _ _ (twoGates_step outerWidth width address modulus coefficient)
      environment

/-- Exact phase and the complete action extend to any encoded reference. -/
lemma twoAccumulator_reference {Reference : Type}
    (reference : BinaryLabelEncoding Reference) (outerWidth width : Nat)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    UnitaryCircuit.Realizes (prod (outerEncoding outerWidth width) reference)
      (layout := QubitLayout.canonical ((outerEncoding outerWidth width).width + reference.width))
      (UnitaryCircuit.onBinaryPrefix reference.width
        (twoProgram outerWidth width address modulus coefficient)) environment
      (fun state => ((state.1.1, if state.1.1.val.testBit address.val then
        prefixOutput modulus coefficient width state.1.2 else state.1.2), state.2)) :=
  UnitaryCircuit.Realizes.onBinaryPrefix (right := reference)
    (twoAccumulator_realizes outerWidth width address modulus coefficient)

/-- The zero-, one- and two-bit complete instruction paths are unchanged. -/
lemma twoAccumulator_small (outerWidth width : Nat) (small : width ≤ 2)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    twoGates outerWidth width address modulus coefficient =
      originalControlled outerWidth width address (Gidney.gates width modulus coefficient) := by
  match width with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | extra + 3 => omega

/-- Both the complete outer word and original source word are restored. -/
lemma twoAccumulator_restores (outerWidth width : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ width + 1)) (coefficient : Nat)
    (state : OuterRegisters outerWidth width) :
    let final := stepList (twoGates outerWidth width address modulus coefficient) state
    final.1 = state.1 ∧ final.2.1 = state.2.1 := by
  rw [twoGates_step]
  constructor
  · rfl
  · split_ifs <;> rfl

/-- The physical carrier is exactly the outer word and the original two words. -/
lemma twoAccumulator_width (outerWidth width : Nat) :
    (outerEncoding outerWidth width).width = outerWidth + 2 * width := by
  change outerWidth + (width + width) = _
  omega

/-- Certified placement preserves every actual native coordinate. -/
lemma relocate_counts (extra : Nat) (selector : Fin (extra + 3))
    (body : List (GateSpec (canonicalEncoding extra))) :
    xCount (relocate extra selector body) = xCount body ∧
      cCount (relocate extra selector body) = cCount body ∧
      tCount (relocate extra selector body) = tCount body := by
  have same := relocate_events extra selector body
  exact ⟨sum_xMultiplicity_eq_of_events_eq .empty same,
    sum_cnotMultiplicity_eq_of_events_eq .empty same,
    sum_toffoliMultiplicity_eq_of_events_eq .empty same⟩

/-- Lifting beside the arbitrary outer word preserves all native coordinates. -/
lemma outerLift_counts (outerWidth : Nat) {width : Nat}
    (body : List (GateSpec (encoding width))) :
    xCount (outerLift outerWidth body) = xCount body ∧
      cCount (outerLift outerWidth body) = cCount body ∧
      tCount (outerLift outerWidth body) = tCount body := by
  have same := map_event_prodRight (oracles := .empty) (finIdentity outerWidth) body
  exact ⟨sum_xMultiplicity_eq_of_events_eq .empty same,
    sum_cnotMultiplicity_eq_of_events_eq .empty same,
    sum_toffoliMultiplicity_eq_of_events_eq .empty same⟩

/-- One actual outer expansion has the exact three-coordinate native formula. -/
lemma outerControl_counts (outerWidth width : Nat) (large : 2 ≤ width)
    (address : Fin outerWidth) (body : List (GateSpec (encoding width))) :
    xCount (outerControl outerWidth width large address body) = 0 ∧
      cCount (outerControl outerWidth width large address body) = xCount body ∧
      tCount (outerControl outerWidth width large address body) =
        cCount body + 4 * tCount body := by
  unfold outerControl xCount cCount tCount
  exact controlRightList_native_counts (left := finIdentity outerWidth) (right := encoding width)
    (finIdentityBit outerWidth) (wordBits width)
    (fun _ => rfl) (wordBits_wire width)
    (by
      have positive := address.isLt
      change 5 ≤ outerWidth + (width + width)
      omega)
    (outerBit outerWidth address) body

/-- The placed source-selector expansion retains its exact native counts. -/
lemma relocated_selected_counts (extra : Nat) (selector : Fin (extra + 3))
    (body : List (GateSpec (Addition.Gidney.encoding (extra + 3)))) :
    xCount (relocate extra selector (selected extra body)) = 0 ∧
      cCount (relocate extra selector (selected extra body)) = xCount body ∧
      tCount (relocate extra selector (selected extra body)) =
        cCount body + 4 * tCount body := by
  have placed := relocate_counts extra selector (selected extra body)
  have source := selected_counts extra body
  exact ⟨placed.1.trans source.1, placed.2.1.trans source.2.1,
    placed.2.2.trans source.2.2⟩

/-- Both actual controls on a comparison give the exact nested native formula. -/
lemma twiceSelected_counts (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3))
    (body : List (GateSpec (Addition.Gidney.encoding (extra + 3)))) :
    xCount (outerControl outerWidth (extra + 3) (by omega) address
        (relocate extra selector (selected extra body))) = 0 ∧
      cCount (outerControl outerWidth (extra + 3) (by omega) address
        (relocate extra selector (selected extra body))) = 0 ∧
      tCount (outerControl outerWidth (extra + 3) (by omega) address
        (relocate extra selector (selected extra body))) =
        xCount body + 4 * cCount body + 16 * tCount body := by
  have outer := outerControl_counts outerWidth (extra + 3) (by omega) address
    (relocate extra selector (selected extra body))
  have inner := relocated_selected_counts extra selector body
  refine ⟨outer.1, outer.2.1.trans inner.1, ?_⟩
  rw [outer.2.2, inner.2.1, inner.2.2]
  ring

/-- The unselected bi-flip retains its own native counts after both placements. -/
lemma twiceUnselected_counts (outerWidth extra : Nat) (selector : Fin (extra + 3))
    (body : List (GateSpec (Addition.Gidney.encoding (extra + 3)))) :
    xCount (outerLift outerWidth (relocate extra selector (unselected extra body))) =
        xCount body ∧
      cCount (outerLift outerWidth (relocate extra selector (unselected extra body))) =
        cCount body ∧
      tCount (outerLift outerWidth (relocate extra selector (unselected extra body))) =
        tCount body := by
  have outer := outerLift_counts outerWidth (relocate extra selector (unselected extra body))
  have placed := relocate_counts extra selector (unselected extra body)
  have inner := unselected_counts extra body
  exact ⟨outer.1.trans (placed.1.trans inner.1),
    outer.2.1.trans (placed.2.1.trans inner.2.1),
    outer.2.2.trans (placed.2.2.trans inner.2.2)⟩

/-- The actual two-control pivot has these exact independent native coordinates. -/
lemma twoPivot_counts (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (pivot : Fin (2 ^ (extra + 3) + 1)) :
    xCount (twoPivot outerWidth extra address selector pivot) =
        2 * xCount (Addition.Gidney.biFlipGates (extra + 3) pivot) ∧
      cCount (twoPivot outerWidth extra address selector pivot) =
        2 * cCount (Addition.Gidney.biFlipGates (extra + 3) pivot) ∧
      tCount (twoPivot outerWidth extra address selector pivot) =
        2 * tCount (Addition.Gidney.biFlipGates (extra + 3) pivot) +
          2 * (xCount (Addition.Gidney.comparisonGates (extra + 3) pivot) +
            4 * cCount (Addition.Gidney.comparisonGates (extra + 3) pivot) +
              16 * tCount (Addition.Gidney.comparisonGates (extra + 3) pivot)) := by
  have lifted := twiceUnselected_counts outerWidth extra selector
    (Addition.Gidney.biFlipGates (extra + 3) pivot)
  have controlled := twiceSelected_counts outerWidth extra address selector
    (Addition.Gidney.comparisonGates (extra + 3) pivot)
  constructor
  · simp only [twoPivot, xCount_append, lifted.1, controlled.1]
    omega
  constructor
  · simp only [twoPivot, cCount_append, lifted.2.1, controlled.2.1]
    omega
  · simp only [twoPivot, tCount_append, lifted.2.2, controlled.2.2]
    omega

/-- The exact two-control Toffoli saving from one actual BCBC pivot. -/
def twoPivotToffoliSaving (extra : Nat) (pivot : Fin (2 ^ (extra + 3) + 1)) : Nat :=
  2 * xCount (Addition.Gidney.biFlipGates (extra + 3) pivot) +
    8 * cCount (Addition.Gidney.biFlipGates (extra + 3) pivot) +
      30 * tCount (Addition.Gidney.biFlipGates (extra + 3) pivot)

/-- The exact two-control serial native-time saving from one actual pivot. -/
def twoPivotTimeSaving (extra : Nat) (pivot : Fin (2 ^ (extra + 3) + 1)) : Nat :=
  6 * cCount (Addition.Gidney.biFlipGates (extra + 3) pivot) +
    30 * tCount (Addition.Gidney.biFlipGates (extra + 3) pivot)

/-- The accepted two-control formulas survive actual unused fields and physical placement. -/
lemma twoPivot_savings (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (pivot : Fin (2 ^ (extra + 3) + 1)) :
    let original := outerControl outerWidth (extra + 3) (by omega) address
      (relocate extra selector (selected extra (Addition.Gidney.pivotGates (extra + 3) pivot)))
    tCount original = tCount (twoPivot outerWidth extra address selector pivot) +
        twoPivotToffoliSaving extra pivot ∧
      original.length = (twoPivot outerWidth extra address selector pivot).length +
        twoPivotTimeSaving extra pivot := by
  dsimp only
  have old := twiceSelected_counts outerWidth extra address selector
    (Addition.Gidney.pivotGates (extra + 3) pivot)
  have replacement := twoPivot_counts outerWidth extra address selector pivot
  constructor
  · rw [old.2.2, replacement.2.2]
    simp only [Addition.Gidney.pivotGates, xCount_append, cCount_append, tCount_append,
      twoPivotToffoliSaving]
    ring
  · rw [length_eq_multiplicity_sums, length_eq_multiplicity_sums]
    change xCount _ + cCount _ + tCount _ =
      xCount _ + cCount _ + tCount _ + twoPivotTimeSaving extra pivot
    rw [old.1, old.2.1, old.2.2, replacement.1, replacement.2.1, replacement.2.2]
    simp only [Addition.Gidney.pivotGates, xCount_append, cCount_append, tCount_append,
      twoPivotTimeSaving]
    ring

/-- The actual Toffoli savings summed over the three required pivots. -/
def twoOffsetToffoliSaving (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) : Nat :=
  twoPivotToffoliSaving extra (offsetFirstPivot modulus constant) +
    twoPivotToffoliSaving extra modulus +
      twoPivotToffoliSaving extra (offsetLastPivot modulus constant)

/-- The actual serial native-time savings summed over the three pivots. -/
def twoOffsetTimeSaving (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) : Nat :=
  twoPivotTimeSaving extra (offsetFirstPivot modulus constant) +
    twoPivotTimeSaving extra modulus + twoPivotTimeSaving extra (offsetLastPivot modulus constant)

/-- Exact two-control savings compare the two real three-pivot stage lists. -/
lemma twoStage_savings (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) :
    let original := outerControl outerWidth (extra + 3) (by omega) address
      (originalPlacedStageGates extra selector modulus constant)
    tCount original = tCount (twoStage outerWidth extra address selector modulus constant) +
        twoOffsetToffoliSaving extra modulus constant ∧
      original.length = (twoStage outerWidth extra address selector modulus constant).length +
        twoOffsetTimeSaving extra modulus constant := by
  dsimp only
  have original : originalPlacedStageGates extra selector modulus constant =
      relocate extra selector
        (selected extra (Addition.Gidney.modularOffsetGates (extra + 3) modulus constant)) := rfl
  rw [original]
  have old := twiceSelected_counts outerWidth extra address selector
    (Addition.Gidney.modularOffsetGates (extra + 3) modulus constant)
  have first := twoPivot_counts outerWidth extra address selector
    (offsetFirstPivot modulus constant)
  have middle := twoPivot_counts outerWidth extra address selector modulus
  have last := twoPivot_counts outerWidth extra address selector (offsetLastPivot modulus constant)
  constructor
  · rw [old.2.2]
    simp only [twoStage, tCount_append, first.2.2, middle.2.2, last.2.2,
      Addition.Gidney.modularOffsetGates, Addition.Gidney.pivotGates,
      xCount_append, cCount_append, tCount_append, twoOffsetToffoliSaving, twoPivotToffoliSaving]
    ring
  · rw [length_eq_multiplicity_sums, length_eq_multiplicity_sums]
    change xCount _ + cCount _ + tCount _ =
      xCount _ + cCount _ + tCount _ + twoOffsetTimeSaving extra modulus constant
    rw [old.1, old.2.1, old.2.2]
    simp only [twoStage, xCount_append, cCount_append, tCount_append,
      first.1, first.2.1, first.2.2, middle.1, middle.2.1, middle.2.2,
      last.1, last.2.1, last.2.2, Addition.Gidney.modularOffsetGates,
      Addition.Gidney.pivotGates, xCount_append, cCount_append, tCount_append,
      twoOffsetTimeSaving, twoPivotTimeSaving]
    ring

/-- The literal control expansion emits at most four native gates per input gate. -/
lemma originalControlled_length (outerWidth width : Nat) (address : Fin outerWidth)
    (body : List (GateSpec (encoding width))) :
    (originalControlled outerWidth width address body).length ≤ 4 * body.length := by
  by_cases small : width ≤ 1
  · simp only [originalControlled, dif_pos small, List.length_map]
    omega
  · simp only [originalControlled, dif_neg small, outerControl]
    exact controlRightList_length_bound _ _ _ _ _ _ _

/-- The exact stage savings are coordinates and time of the same emitted native circuit. -/
lemma twoStage_program_savings (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) :
    let original := programList (QubitLayout.canonical _) .empty
      (outerControl outerWidth (extra + 3) (by omega) address
        (originalPlacedStageGates extra selector modulus constant))
    let replacement := programList (QubitLayout.canonical _) .empty
      (twoStage outerWidth extra address selector modulus constant)
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate .toffoli) original.eventCost =
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate .toffoli) replacement.eventCost + twoOffsetToffoliSaving extra modulus constant ∧
      original.evaluatedEventDepth Resource.Event.quantumDuration =
        replacement.evaluatedEventDepth Resource.Event.quantumDuration +
          twoOffsetTimeSaving extra modulus constant := by
  dsimp only
  have savings := twoStage_savings outerWidth extra address selector modulus constant
  constructor
  · simpa only [programList_toffoli_count_eq_sum, tCount] using savings.1
  · simpa only [native_time] using savings.2

/-- The width-complete source stage retains its independent event envelope. -/
lemma oldStage_length (width : Nat) (selector : Fin width)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    (Gidney.stageGates width selector modulus constant).length ≤ stageEventBound width := by
  have card := congrArg Multiset.card (gidneyStageGates_eventCost width selector modulus constant)
  simp only [ResourcePool.ofList, Multiset.coe_card, List.length_map] at card
  rw [card]
  exact gidneyStage_event_count_bound width selector modulus constant

/-- The actual optimized stage retains the original external-control event cap. -/
lemma twoStageGates_bound (outerWidth : Nat) : (width : Nat) →
    (address : Fin outerWidth) → (selector : Fin width) →
    (modulus : Fin (2 ^ width + 1)) → (constant : Fin (modulus.val + 1)) →
    (twoStageGates outerWidth width address selector modulus constant).length ≤
      4 * stageEventBound width
  | 0, _, selector, _, _ => Fin.elim0 selector
  | 1, address, selector, modulus, constant =>
      (originalControlled_length outerWidth 1 address _).trans
        (Nat.mul_le_mul_left 4 (oldStage_length 1 selector modulus constant))
  | 2, address, selector, modulus, constant =>
      (originalControlled_length outerWidth 2 address _).trans
        (Nat.mul_le_mul_left 4 (oldStage_length 2 selector modulus constant))
  | extra + 3, address, selector, modulus, constant => by
      have savings := (twoStage_savings outerWidth extra address selector modulus constant).2
      have old := originalControlled_length outerWidth (extra + 3) address
        (originalPlacedStageGates extra selector modulus constant)
      have stage := originalPlaced_length_bound extra selector modulus constant
      change (twoStage outerWidth extra address selector modulus constant).length ≤ _
      have original : originalControlled outerWidth (extra + 3) address
          (originalPlacedStageGates extra selector modulus constant) =
          outerControl outerWidth (extra + 3) (by omega) address
            (originalPlacedStageGates extra selector modulus constant) := by
        rw [originalControlled, dif_neg (show ¬extra + 3 ≤ 1 by omega)]
      rw [original, savings] at old
      change (originalPlacedStageGates extra selector modulus constant).length ≤ _ at stage
      omega

/-- The actual ordered prefix obeys the sum of independent stage event caps. -/
lemma twoPrefix_bound (outerWidth width : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ width + 1)) (coefficient count : Nat) (within : count ≤ width) :
    (twoPrefix outerWidth width address modulus coefficient count within).length ≤
      count * (4 * stageEventBound width) := by
  induction count with
  | zero => simp only [twoPrefix, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | succ index ih =>
      rw [twoPrefix, List.length_append, Nat.succ_mul]
      exact Nat.add_le_add (ih (by omega)) (twoStageGates_bound _ _ _ _ _ _)

/-- The complete actual accumulator retains its independent event envelope. -/
lemma twoGates_bound (outerWidth : Nat) : (width : Nat) →
    (address : Fin outerWidth) → (modulus : Fin (2 ^ width + 1)) → (coefficient : Nat) →
    (twoGates outerWidth width address modulus coefficient).length ≤
      4 * (width * stageEventBound width)
  | 0, address, modulus, coefficient =>
      (originalControlled_length outerWidth 0 address _).trans
        (Nat.mul_le_mul_left 4 (gidneyAccumulateGates_length_bound 0 modulus coefficient))
  | 1, address, modulus, coefficient =>
      (originalControlled_length outerWidth 1 address _).trans
        (Nat.mul_le_mul_left 4 (gidneyAccumulateGates_length_bound 1 modulus coefficient))
  | 2, address, modulus, coefficient =>
      (originalControlled_length outerWidth 2 address _).trans
        (Nat.mul_le_mul_left 4 (gidneyAccumulateGates_length_bound 2 modulus coefficient))
  | extra + 3, address, modulus, coefficient => by
      simpa only [twoGates, Nat.mul_left_comm]
        using twoPrefix_bound outerWidth (extra + 3) address modulus coefficient
          (extra + 3) (Nat.le_refl _)

/-- Actual native time and event count meet the original independent external-control envelope. -/
lemma twoAccumulator_budget (outerWidth width : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    (twoProgram outerWidth width address modulus coefficient).eventCost.card ≤
        4 * (width * stageEventBound width) ∧
      (twoProgram outerWidth width address modulus coefficient).evaluatedEventDepth
        Resource.Event.quantumDuration ≤ 4 * (width * stageEventBound width) := by
  constructor
  · simpa only [twoProgram, programList_eventCost_card]
      using twoGates_bound outerWidth width address modulus coefficient
  · simpa only [twoProgram, native_time]
      using twoGates_bound outerWidth width address modulus coefficient

/-- Every event of the actual accumulator uses the declared native alphabet. -/
lemma twoAccumulator_support (outerWidth width : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ width + 1)) (coefficient : Nat)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (twoProgram outerWidth width address modulus coefficient).eventCost) :
    focus ∈ primitiveAlphabet :=
  programList_native_support _ _ focus present

/-- The same emitted program meets its independent native resource pool. -/
lemma twoAccumulator_native_budget (outerWidth width : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    (twoProgram outerWidth width address modulus coefficient).eventCost ≤
      (4 * (width * stageEventBound width)) • primitiveAlphabet :=
  ResourcePool.le_scaled_of_support_card_le _ _ _
    (twoAccumulator_support outerWidth width address modulus coefficient)
    (twoAccumulator_budget outerWidth width address modulus coefficient).1

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney.ControlPushdown
