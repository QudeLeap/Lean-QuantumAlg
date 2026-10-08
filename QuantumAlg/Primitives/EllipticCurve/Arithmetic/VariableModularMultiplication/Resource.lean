/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.VariableModularMultiplication.Endpoint

/-!
# Resources for width-parameterized variable modular multiplication

The bounds in this module are projections of the concrete encoded-bit programs
used by the semantic endpoint. They are uniform in the stored modulus bit
pattern. In particular, the Toffoli coordinate is not replaced by a bound on
all primitive events.
-/

section

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic

namespace VariableModularMul

noncomputable section

variable [params : Parameters]

/-- Exact qubit width of a width-`f` common variable-multiplication carrier. -/
def physicalWidthFor (f : Nat) : Nat :=
  7 * f + 5

/-- Exact qubit width of the common variable-multiplication carrier. -/
theorem encoding_width_exact : encoding.width = physicalWidthFor params.width := by
  simp [encoding, rawEncoding, accumulatorSuffixEncoding,
    inPlaceWithWorkEncoding, inPlaceEncoding, wordEncoding,
    PlainAdder.Schedule.PowerOfTwo.wordEncoding, physicalWidthFor]
  omega

private theorem rawArithmeticGates_events_eq_source :
    rawArithmeticGates.map (EncodedBit.GateSpec.event .empty) =
      (MAU.Addition.VBECircuit.modularAddGates
        params.width params.modulus.val).map (EncodedBit.GateSpec.event .empty) := by
  unfold rawArithmeticGates inPlaceArithmeticGates
  calc
    (((((MAU.Addition.VBECircuit.modularAddGates
          params.width params.modulus.val).map
        (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticGate
          params.width)).map
        (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
        (EncodedBit.GateSpec.prodRight wordEncoding)).map
        (EncodedBit.GateSpec.prodRight wordEncoding)).map
        (EncodedBit.GateSpec.event .empty) =
      ((((MAU.Addition.VBECircuit.modularAddGates
          params.width params.modulus.val).map
        (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticGate
          params.width)).map
        (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
        (EncodedBit.GateSpec.prodRight wordEncoding)).map
        (EncodedBit.GateSpec.event .empty) :=
      EncodedBit.GateSpec.map_event_prodRight wordEncoding _
    _ = (((MAU.Addition.VBECircuit.modularAddGates
          params.width params.modulus.val).map
        (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticGate
          params.width)).map
        (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
        (EncodedBit.GateSpec.event .empty) :=
      EncodedBit.GateSpec.map_event_prodRight wordEncoding _
    _ = ((MAU.Addition.VBECircuit.modularAddGates
          params.width params.modulus.val).map
        (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticGate
          params.width)).map (EncodedBit.GateSpec.event .empty) :=
      EncodedBit.GateSpec.map_event_prodLeft BinaryLabelEncoding.bool _
    _ = (MAU.Addition.VBECircuit.modularAddGates
          params.width params.modulus.val).map (EncodedBit.GateSpec.event .empty) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro gate _
      cases gate <;> rfl

theorem liftInPlaceGates_events_eq_source
    (gates : List (EncodedBit.GateSpec inPlaceEncoding)) :
    (liftInPlaceGates gates).map (EncodedBit.GateSpec.event .empty) =
      gates.map (EncodedBit.GateSpec.event .empty) := by
  change
    (((gates.map (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
        (EncodedBit.GateSpec.prodRight wordEncoding)).map
        (EncodedBit.GateSpec.prodRight wordEncoding)).map
      (EncodedBit.GateSpec.event .empty) =
    gates.map (EncodedBit.GateSpec.event .empty)
  calc
    (((gates.map (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
        (EncodedBit.GateSpec.prodRight wordEncoding)).map
        (EncodedBit.GateSpec.prodRight wordEncoding)).map
        (EncodedBit.GateSpec.event .empty) =
      ((gates.map (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
        (EncodedBit.GateSpec.prodRight wordEncoding)).map
        (EncodedBit.GateSpec.event .empty) :=
      EncodedBit.GateSpec.map_event_prodRight wordEncoding _
    _ = (gates.map (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
        (EncodedBit.GateSpec.event .empty) :=
      EncodedBit.GateSpec.map_event_prodRight wordEncoding _
    _ = gates.map (EncodedBit.GateSpec.event .empty) :=
      EncodedBit.GateSpec.map_event_prodLeft BinaryLabelEncoding.bool _

theorem liftInPlaceGates_length
    (gates : List (EncodedBit.GateSpec inPlaceEncoding)) :
    (liftInPlaceGates gates).length = gates.length := by
  have h := congrArg List.length (liftInPlaceGates_events_eq_source gates)
  simpa only [List.length_map] using h

omit params in
private theorem controlledEventExpansion_toffoli_count
    {Physical : Type} {physicalEncoding : BinaryLabelEncoding Physical}
    (gate : EncodedBit.GateSpec physicalEncoding) :
    (EncodedBit.GateSpec.controlledEventExpansion .empty gate).count
        (.gate .toffoli) =
      EncodedBit.GateSpec.cnotMultiplicity gate +
        3 * EncodedBit.GateSpec.toffoliMultiplicity gate := by
  cases gate <;> rfl

omit params in
private theorem flatMap_controlledEventExpansion_toffoli_count
    {Physical : Type} {physicalEncoding : BinaryLabelEncoding Physical} :
    ∀ gates : List (EncodedBit.GateSpec physicalEncoding),
      (gates.flatMap (EncodedBit.GateSpec.controlledEventExpansion .empty)).count
          (.gate .toffoli) =
        (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum +
          3 * (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum
  | [] => rfl
  | gate :: rest => by
      simp only [List.flatMap_cons, List.count_append, List.map_cons,
        List.sum_cons, controlledEventExpansion_toffoli_count,
        flatMap_controlledEventExpansion_toffoli_count]
      omega

omit params in
private theorem controlledEventExpansion_length
    {Physical : Type} {physicalEncoding : BinaryLabelEncoding Physical}
    (gate : EncodedBit.GateSpec physicalEncoding) :
    (EncodedBit.GateSpec.controlledEventExpansion .empty gate).length =
      EncodedBit.GateSpec.xMultiplicity gate +
        EncodedBit.GateSpec.cnotMultiplicity gate +
          3 * EncodedBit.GateSpec.toffoliMultiplicity gate := by
  cases gate <;> rfl

omit params in
private theorem flatMap_controlledEventExpansion_length
    {Physical : Type} {physicalEncoding : BinaryLabelEncoding Physical} :
    ∀ gates : List (EncodedBit.GateSpec physicalEncoding),
      (gates.flatMap (EncodedBit.GateSpec.controlledEventExpansion .empty)).length =
        (gates.map EncodedBit.GateSpec.xMultiplicity).sum +
          (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum +
            3 * (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum
  | [] => rfl
  | gate :: rest => by
      simp only [List.flatMap_cons, List.length_append, List.map_cons,
        List.sum_cons, controlledEventExpansion_length,
        flatMap_controlledEventExpansion_length]
      omega

/-- One controlled modular-add stage uses at most `108f+14` Toffoli gates. -/
theorem stageCircuit_toffoli_count_le (bit : Fin params.width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (stageCircuit bit).eventCost ≤ 108 * params.width + 14 := by
  have hsourceC :=
    MAU.Addition.VBECircuit.modularAddGates_cnotMultiplicity_sum_le
      params.width params.modulus.val
  have hsourceT :=
    MAU.Addition.VBECircuit.modularAddGates_toffoliMultiplicity_sum
      params.width params.modulus.val
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (rawStageGates bit)).eventCost ≤ _
  rw [EncodedBit.GateSpec.programList_eventCost, ResourcePool.count_ofList]
  unfold rawStageGates
  rw [EncodedBit.GateSpec.map_event_controlledListWithWorkGates (oracles := .empty),
    flatMap_controlledEventExpansion_toffoli_count]
  have hc := EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    rawArithmeticGates_events_eq_source
  have ht := EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    rawArithmeticGates_events_eq_source
  rw [hc, ht, hsourceT]
  omega

/-- One clean-work-controlled modular-add stage contains exactly one CNOT:
the unique source X gate becomes the controlled CNOT leaf. -/
theorem rawStageGates_cnotMultiplicity_sum (bit : Fin params.width) :
    ((rawStageGates bit).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  unfold rawStageGates
  rw [EncodedBit.GateSpec.controlledListWithWorkGates_cnotMultiplicity_sum]
  have hx := EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq .empty
    rawArithmeticGates_events_eq_source
  rw [hx,
    MAU.Addition.VBECircuit.modularAddGates_xMultiplicity_sum]

/-- One controlled modular-add stage has at most `108f+15` primitive events. -/
theorem stageCircuit_eventCount_le (bit : Fin params.width) :
    (stageCircuit bit).eventCost.card ≤ 108 * params.width + 15 := by
  have hsourceX :=
    MAU.Addition.VBECircuit.modularAddGates_xMultiplicity_sum
      params.width params.modulus.val
  have hsourceC :=
    MAU.Addition.VBECircuit.modularAddGates_cnotMultiplicity_sum_le
      params.width params.modulus.val
  have hsourceT :=
    MAU.Addition.VBECircuit.modularAddGates_toffoliMultiplicity_sum
      params.width params.modulus.val
  rw [show (stageCircuit bit).eventCost.card = (rawStageGates bit).length by
    exact EncodedBit.GateSpec.programList_eventCost_card
      (layout := QubitLayout.canonical _) (oracles := .empty) _]
  have hevents := EncodedBit.GateSpec.map_event_controlledListWithWorkGates
    (oracles := .empty)
    (rawMultiplierBit bit) rawWorkBit rawArithmeticGates
    (rawMultiplierDisjoint bit) rawWorkDisjoint (rawMultiplierWork_ne bit)
  have hlength := congrArg List.length hevents
  simp only [List.length_map] at hlength
  unfold rawStageGates
  rw [hlength, flatMap_controlledEventExpansion_length]
  have hx := EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq .empty
    rawArithmeticGates_events_eq_source
  have hc := EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    rawArithmeticGates_events_eq_source
  have ht := EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    rawArithmeticGates_events_eq_source
  rw [hx, hc, ht, hsourceX, hsourceT]
  omega

private theorem accumulatorSwapCircuit_eventCount :
    accumulatorSwapCircuit.eventCost.card = 3 * params.width := by
  unfold accumulatorSwapCircuit accumulatorSwapGates
  rw [EncodedBit.GateSpec.programList_eventCost_card]
  exact EncodedBit.Word.swapGates_length rawAccumulatorWord
    rawInPlaceAccumulatorWord rawAccumulator_inPlaceAccumulator_ne

private theorem sourceCopyCircuit_eventCount :
    sourceCopyCircuit.eventCost.card = params.width := by
  unfold sourceCopyCircuit sourceCopyGates
  rw [EncodedBit.GateSpec.programList_eventCost_card]
  simp [EncodedBit.Word.xorIntoGates]

private theorem accumulatorSwapGates_cnotMultiplicity_sum :
    (accumulatorSwapGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      3 * params.width := by
  exact EncodedBit.Word.swapGates_cnotMultiplicity_sum
    rawAccumulatorWord rawInPlaceAccumulatorWord
      rawAccumulator_inPlaceAccumulator_ne

private theorem sourceCopyGates_cnotMultiplicity_sum :
    (sourceCopyGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      params.width := by
  exact EncodedBit.Word.xorIntoGates_cnotMultiplicity_sum
    rawInPlaceMultiplicandWord rawInPlaceActiveSourceWord
      rawInPlaceMultiplicand_activeSource_ne

private theorem accumulatorSwapCircuit_toffoli_count_zero :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      accumulatorSwapCircuit.eventCost = 0 := by
  unfold accumulatorSwapCircuit accumulatorSwapGates
  rw [EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact EncodedBit.Word.swapGates_toffoliMultiplicity_sum
    rawAccumulatorWord rawInPlaceAccumulatorWord
      rawAccumulator_inPlaceAccumulator_ne

private theorem sourceCopyCircuit_toffoli_count_zero :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      sourceCopyCircuit.eventCost = 0 := by
  unfold sourceCopyCircuit sourceCopyGates
  rw [EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact EncodedBit.Word.xorIntoGates_toffoliMultiplicity_sum
    rawInPlaceMultiplicandWord rawInPlaceActiveSourceWord
      rawInPlaceMultiplicand_activeSource_ne

/-- Accumulator routing does not change the Toffoli coordinate. -/
theorem selectedAddCircuit_toffoli_count_le (bit : Fin params.width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (selectedAddCircuit bit).eventCost ≤ 108 * params.width + 14 := by
  have hswap :
      (accumulatorSwapGates.map (EncodedBit.GateSpec.event .empty)).count
          (.gate .toffoli) = 0 := by
    simpa only [accumulatorSwapCircuit,
      EncodedBit.GateSpec.programList_eventCost, ResourcePool.count_ofList]
      using accumulatorSwapCircuit_toffoli_count_zero
  have hcopy :
      (sourceCopyGates.map (EncodedBit.GateSpec.event .empty)).count
          (.gate .toffoli) = 0 := by
    simpa only [sourceCopyCircuit,
      EncodedBit.GateSpec.programList_eventCost, ResourcePool.count_ofList]
      using sourceCopyCircuit_toffoli_count_zero
  have hstage :
      ((rawStageGates bit).map (EncodedBit.GateSpec.event .empty)).count
          (.gate .toffoli) ≤ 108 * params.width + 14 := by
    simpa only [stageCircuit, EncodedBit.GateSpec.programList_eventCost,
      ResourcePool.count_ofList] using stageCircuit_toffoli_count_le bit
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (selectedAddGates bit)).eventCost ≤ _
  rw [EncodedBit.GateSpec.programList_eventCost, ResourcePool.count_ofList]
  unfold selectedAddGates sourceUnloadGates
  simp only [List.map_append, List.count_append, hswap, hcopy,
    Nat.zero_add, Nat.add_zero]
  exact hstage

/-- The routed selected-add list contains exactly `8f+1` CNOT leaves: two
three-CNOT swaps, two word xors, and the controlled source X leaf. -/
theorem selectedAddGates_cnotMultiplicity_sum (bit : Fin params.width) :
    ((selectedAddGates bit).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      8 * params.width + 1 := by
  simp only [selectedAddGates, sourceUnloadGates, List.map_append,
    List.sum_append, accumulatorSwapGates_cnotMultiplicity_sum,
    sourceCopyGates_cnotMultiplicity_sum,
    rawStageGates_cnotMultiplicity_sum]
  omega

/-- One routed selected add has at most `116f+15` primitive events. -/
theorem selectedAddCircuit_eventCount_le (bit : Fin params.width) :
    (selectedAddCircuit bit).eventCost.card ≤ 116 * params.width + 15 := by
  have hstage := stageCircuit_eventCount_le bit
  have hswap : accumulatorSwapGates.length = 3 * params.width := by
    simpa only [accumulatorSwapCircuit,
      EncodedBit.GateSpec.programList_eventCost_card]
      using accumulatorSwapCircuit_eventCount
  have hcopy : sourceCopyGates.length = params.width := by
    simpa only [sourceCopyCircuit,
      EncodedBit.GateSpec.programList_eventCost_card]
      using sourceCopyCircuit_eventCount
  change (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (selectedAddGates bit)).eventCost.card ≤ _
  rw [EncodedBit.GateSpec.programList_eventCost_card]
  have hstageLength : (rawStageGates bit).length ≤ 108 * params.width + 15 := by
    simpa only [stageCircuit,
      EncodedBit.GateSpec.programList_eventCost_card] using hstage
  unfold selectedAddGates sourceUnloadGates
  simp only [List.length_append, hswap, hcopy]
  omega

/-- One full widened-word swap contributes exactly `3(f+1)` CNOT leaves. -/
private theorem doublingSwapGates_cnotMultiplicity_sum :
    (doublingSwapGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      3 * (params.width + 1) := by
  exact EncodedBit.Word.swapGates_cnotMultiplicity_sum
    rawDoublingSourceWord rawDoublingTargetWord _

/-- One full widened-word swap has no Toffoli leaf. -/
private theorem doublingSwapGates_toffoliMultiplicity_sum :
    (doublingSwapGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  exact EncodedBit.Word.swapGates_toffoliMultiplicity_sum
    rawDoublingSourceWord rawDoublingTargetWord _

/-- One full widened-word swap has `3(f+1)` primitive leaves. -/
private theorem doublingSwapGates_length :
    doublingSwapGates.length = 3 * (params.width + 1) := by
  exact EncodedBit.Word.swapGates_length
    rawDoublingSourceWord rawDoublingTargetWord _

/-- The adjacent-swap left shift contributes exactly `3f` CNOT leaves. -/
private theorem doublingShiftGates_cnotMultiplicity_sum :
    (doublingShiftGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      3 * params.width := by
  rw [doublingShiftGates, EncodedBit.Word.adjacentShiftRightGates,
    List.map_reverse, List.sum_reverse,
    EncodedBit.Word.adjacentShiftLeftGates]
  have hsum : ∀ indices : List
      (Fin (MAU.Addition.VBECircuit.AdderWidth params.width - 1)),
      ((indices.flatMap
          (EncodedBit.Word.adjacentSwapGates rawDoublingTargetWord
            rawDoublingTargetWord_pairwise_ne)).map
          EncodedBit.GateSpec.cnotMultiplicity).sum =
        3 * indices.length := by
    intro indices
    induction indices with
    | nil => rfl
    | cons bit rest ih =>
        simp only [List.flatMap_cons, List.map_append, List.sum_append]
        have hhead :
            ((EncodedBit.Word.adjacentSwapGates rawDoublingTargetWord
                rawDoublingTargetWord_pairwise_ne bit).map
              EncodedBit.GateSpec.cnotMultiplicity).sum = 3 := by
          simp [EncodedBit.Word.adjacentSwapGates,
            EncodedBit.swapGates]
        rw [hhead, ih, List.length_cons]
        omega
  simpa only [List.length_ofFn,
    MAU.Addition.VBECircuit.AdderWidth, Nat.add_sub_cancel] using
    hsum (List.ofFn fun i : Fin
      (MAU.Addition.VBECircuit.AdderWidth params.width - 1) => i)

/-- The adjacent-swap left shift has no Toffoli leaf. -/
private theorem doublingShiftGates_toffoliMultiplicity_sum :
    (doublingShiftGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  rw [doublingShiftGates, EncodedBit.Word.adjacentShiftRightGates,
    List.map_reverse, List.sum_reverse,
    EncodedBit.Word.adjacentShiftLeftGates]
  have hsum : ∀ indices : List
      (Fin (MAU.Addition.VBECircuit.AdderWidth params.width - 1)),
      ((indices.flatMap
          (EncodedBit.Word.adjacentSwapGates rawDoublingTargetWord
            rawDoublingTargetWord_pairwise_ne)).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
    intro indices
    induction indices with
    | nil => rfl
    | cons bit rest ih =>
        simp only [List.flatMap_cons, List.map_append, List.sum_append]
        have hhead :
            ((EncodedBit.Word.adjacentSwapGates rawDoublingTargetWord
                rawDoublingTargetWord_pairwise_ne bit).map
              EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
          simp [EncodedBit.Word.adjacentSwapGates,
            EncodedBit.swapGates]
        rw [hhead, ih]
  exact hsum _

/-- The adjacent-swap left shift has exactly `3f` primitive leaves. -/
private theorem doublingShiftGates_length :
    doublingShiftGates.length = 3 * params.width := by
  simp [doublingShiftGates, EncodedBit.Word.adjacentShiftRightGates,
    EncodedBit.Word.adjacentShiftLeftGates,
    EncodedBit.Word.adjacentSwapGates, EncodedBit.swapGates,
    List.length_flatMap, Function.comp_def]
  omega

/-- The shift/reduce doubling block has exactly `30f` Toffoli gates. -/
theorem doublingCircuit_toffoli_count_eq :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        doublingCircuit.eventCost = 30 * params.width := by
  have hraw := EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    rawArithmeticGates_events_eq_source
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty doublingGates).eventCost = _
  rw [EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  simp only [doublingGates, List.map_append, List.sum_append,
    doublingSwapGates_toffoliMultiplicity_sum,
    doublingShiftGates_toffoliMultiplicity_sum, hraw,
    MAU.Addition.VBECircuit.modularAddGates_toffoliMultiplicity_sum,
    doublingCleanupGates,
    EncodedBit.GateSpec.toffoliMultiplicity_cnot, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- The shift/reduce doubling list has at most `27f+21` CNOT leaves. -/
theorem doublingGates_cnotMultiplicity_sum_le :
    (doublingGates.map EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      27 * params.width + 21 := by
  have hraw := EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    rawArithmeticGates_events_eq_source
  have harithmetic :=
    MAU.Addition.VBECircuit.modularAddGates_cnotMultiplicity_sum_le
      params.width params.modulus.val
  simp only [doublingGates, List.map_append, List.sum_append,
    doublingSwapGates_cnotMultiplicity_sum,
    doublingShiftGates_cnotMultiplicity_sum, hraw,
    doublingCleanupGates,
    EncodedBit.GateSpec.cnotMultiplicity_cnot, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

/-- The shift/reduce doubling block has a uniform linear event bound. -/
theorem doublingCircuit_eventCount_le :
    doublingCircuit.eventCost.card ≤
      57 * params.width + 52 := by
  have hsource :=
    MAU.Addition.VBECircuit.modularAddGates_length_le
      params.width params.modulus.val
  have hraw : rawArithmeticGates.length =
      (MAU.Addition.VBECircuit.modularAddGates
        params.width params.modulus.val).length := by
    simpa only [List.length_map] using
      congrArg List.length rawArithmeticGates_events_eq_source
  change (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    doublingGates).eventCost.card ≤ _
  rw [EncodedBit.GateSpec.programList_eventCost_card]
  simp only [doublingGates, List.length_append,
    doublingSwapGates_length, doublingShiftGates_length,
    hraw, doublingCleanupGates, List.length_cons, List.length_nil]
  omega

/-- Toffoli bound for one selected-add/doubling round. -/
theorem roundCircuit_toffoli_count_le (bit : Fin params.width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (roundCircuit bit).eventCost ≤
      (108 * params.width + 14) + 30 * params.width := by
  have hselected :
      ((selectedAddGates bit).map (EncodedBit.GateSpec.event .empty)).count
          (.gate .toffoli) ≤ 108 * params.width + 14 := by
    simpa only [selectedAddCircuit,
      EncodedBit.GateSpec.programList_eventCost, ResourcePool.count_ofList]
      using selectedAddCircuit_toffoli_count_le bit
  have hdoubling :
      (doublingGates.map (EncodedBit.GateSpec.event .empty)).count
          (.gate .toffoli) = 30 * params.width := by
    simpa only [doublingCircuit,
      EncodedBit.GateSpec.programList_eventCost, ResourcePool.count_ofList]
      using doublingCircuit_toffoli_count_eq
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (roundGates bit)).eventCost ≤ _
  rw [EncodedBit.GateSpec.programList_eventCost, ResourcePool.count_ofList]
  unfold roundGates
  simp only [List.map_append, List.count_append]
  exact Nat.add_le_add hselected hdoubling.le

/-- CNOT bound for one selected-add/doubling round, projected from the two
literal source lists. -/
theorem roundGates_cnotMultiplicity_sum_le (bit : Fin params.width) :
    ((roundGates bit).map EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      (8 * params.width + 1) +
        (27 * params.width + 21) := by
  simp only [roundGates, List.map_append, List.sum_append]
  exact Nat.add_le_add (selectedAddGates_cnotMultiplicity_sum bit).le
    doublingGates_cnotMultiplicity_sum_le

/-- Primitive-event bound for one selected-add/doubling round. -/
theorem roundCircuit_eventCount_le (bit : Fin params.width) :
    (roundCircuit bit).eventCost.card ≤
      (116 * params.width + 15) +
        (57 * params.width + 52) := by
  have hselected : (selectedAddGates bit).length ≤ 116 * params.width + 15 := by
    simpa only [selectedAddCircuit,
      EncodedBit.GateSpec.programList_eventCost_card]
      using selectedAddCircuit_eventCount_le bit
  have hdoubling : doublingGates.length ≤
      57 * params.width + 52 := by
    simpa only [doublingCircuit,
      EncodedBit.GateSpec.programList_eventCost_card]
      using doublingCircuit_eventCount_le
  change (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (roundGates bit)).eventCost.card ≤ _
  rw [EncodedBit.GateSpec.programList_eventCost_card]
  unfold roundGates
  rw [List.length_append]
  exact Nat.add_le_add hselected hdoubling

end

end VariableModularMul

namespace VariableModularMulSchedule

noncomputable section

variable [params : VariableModularMul.Parameters]

/-- Closed Toffoli bound for a complete width-`f` schedule. -/
def toffoliBoundFor (f : Nat) : Nat :=
  168 * f ^ 2 + 14 * f

/-- Closed Toffoli bound for the instantiated width-indexed schedule. -/
def toffoliBound : Nat :=
  toffoliBoundFor params.width

/-- Closed CNOT bound for a complete width-`f` schedule. -/
def cnotBoundFor (f : Nat) : Nat :=
  62 * f ^ 2 + 43 * f

/-- Closed CNOT bound for the instantiated width-indexed schedule. -/
def cnotBound : Nat :=
  cnotBoundFor params.width

/-- Closed primitive-event bound for a complete width-`f` schedule. -/
def eventCountBoundFor (f : Nat) : Nat :=
  230 * f ^ 2 + 119 * f

/-- Closed primitive-event bound for the instantiated width-indexed schedule. -/
def eventCountBound : Nat :=
  eventCountBoundFor params.width

/-- A closed literal-X bound for a complete width-`f` schedule. -/
def xBoundFor (f : Nat) : Nat :=
  eventCountBoundFor f

/-- A closed literal-X bound for the instantiated width-indexed schedule. -/
def xBound : Nat :=
  xBoundFor params.width

/-- Closed unit-depth bound for a complete width-`f` schedule. -/
def unitDepthBoundFor (f : Nat) : Nat :=
  eventCountBoundFor f

/-- Closed unit-depth bound for the instantiated width-indexed schedule. -/
def unitDepthBound : Nat :=
  unitDepthBoundFor params.width

set_option exponentiation.threshold 2048 in
/-- Reversing the doubling source list preserves its strict event pool. -/
theorem inverseDoublingCircuit_eventCost :
    inverseDoublingCircuit.eventCost =
      VariableModularMul.doublingCircuit.eventCost := by
  change (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    inverseDoublingGates).eventCost =
    (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
      VariableModularMul.doublingGates).eventCost
  rw [EncodedBit.GateSpec.programList_eventCost,
    EncodedBit.GateSpec.programList_eventCost, inverseDoublingGates,
    List.map_reverse]
  exact Multiset.coe_reverse _

/-- Each inverse doubling has exactly the same Toffoli count as a forward one. -/
theorem inverseDoublingCircuit_toffoli_count_eq :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        inverseDoublingCircuit.eventCost = 30 * params.width := by
  rw [inverseDoublingCircuit_eventCost]
  exact VariableModularMul.doublingCircuit_toffoli_count_eq

/-- The exact inverse doubling schedule preserves the forward schedule's CNOT
bound. -/
theorem inverseDoublingGates_cnotMultiplicity_sum_le :
    (inverseDoublingGates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      27 * params.width + 21 := by
  rw [inverseDoublingGates, List.map_reverse, List.sum_reverse]
  exact VariableModularMul.doublingGates_cnotMultiplicity_sum_le

/-- Each inverse doubling has the same bit-pattern-independent event bound. -/
theorem inverseDoublingCircuit_eventCount_le :
    inverseDoublingCircuit.eventCost.card ≤
      57 * params.width + 52 := by
  change (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    inverseDoublingGates).eventCost.card ≤ _
  rw [EncodedBit.GateSpec.programList_eventCost_card]
  rw [inverseDoublingGates, List.length_reverse]
  simpa only [VariableModularMul.doublingCircuit,
    EncodedBit.GateSpec.programList_eventCost_card] using
    VariableModularMul.doublingCircuit_eventCount_le

/-- Toffoli count of an explicit forward prefix is linear in its round count. -/
theorem forwardProgram_toffoli_count_le :
    ∀ roundBits : List (Fin params.width),
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
          (forwardProgram roundBits).eventCost ≤
        roundBits.length *
          ((108 * params.width + 14) + 30 * params.width)
  | [] => by simp [forwardProgram]
  | bit :: rest => by
      rw [forwardProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        List.length_cons, Nat.succ_mul,
        Nat.add_comm
          (rest.length *
            ((108 * params.width + 14) + 30 * params.width))
          ((108 * params.width + 14) + 30 * params.width)]
      exact Nat.add_le_add
        (VariableModularMul.roundCircuit_toffoli_count_le bit)
        (forwardProgram_toffoli_count_le rest)

/-- Event count of an explicit forward prefix is linear in its round count. -/
theorem forwardProgram_eventCount_le :
    ∀ roundBits : List (Fin params.width),
      (forwardProgram roundBits).eventCost.card ≤
        roundBits.length *
          ((116 * params.width + 15) +
            (57 * params.width + 52))
  | [] => by simp [forwardProgram]
  | bit :: rest => by
      rw [forwardProgram, UnitaryCircuit.seq_eventCost, Multiset.card_add,
        List.length_cons, Nat.succ_mul,
        Nat.add_comm
          (rest.length *
            ((116 * params.width + 15) +
              (57 * params.width + 52)))
          ((116 * params.width + 15) +
            (57 * params.width + 52))]
      exact Nat.add_le_add
        (VariableModularMul.roundCircuit_eventCount_le bit)
        (forwardProgram_eventCount_le rest)

/-- Toffoli count of the restoration suffix is linear in its round count. -/
theorem restoreProgram_toffoli_count_le :
    ∀ rounds : Nat,
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
          (restoreProgram rounds).eventCost ≤
        rounds * (30 * params.width)
  | 0 => by simp [restoreProgram]
  | rounds + 1 => by
      rw [restoreProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        Nat.succ_mul,
        Nat.add_comm (rounds * (30 * params.width))
          (30 * params.width)]
      exact Nat.add_le_add inverseDoublingCircuit_toffoli_count_eq.le
        (restoreProgram_toffoli_count_le rounds)

/-- Event count of the restoration suffix is linear in its round count. -/
theorem restoreProgram_eventCount_le :
    ∀ rounds : Nat,
      (restoreProgram rounds).eventCost.card ≤
        rounds * (57 * params.width + 52)
  | 0 => by simp [restoreProgram]
  | rounds + 1 => by
      rw [restoreProgram, UnitaryCircuit.seq_eventCost, Multiset.card_add,
        Nat.succ_mul,
        Nat.add_comm
          (rounds *
            (57 * params.width + 52))
          (57 * params.width + 52)]
      exact Nat.add_le_add inverseDoublingCircuit_eventCount_le
        (restoreProgram_eventCount_le rounds)

private theorem forwardGates_toffoli_count_le :
    ∀ roundBits : List (Fin params.width),
      ((forwardGates roundBits).map (EncodedBit.GateSpec.event .empty)).count
          (.gate .toffoli) ≤
        roundBits.length *
          ((108 * params.width + 14) + 30 * params.width)
  | [] => by simp [forwardGates]
  | bit :: rest => by
      have hround :
          ((VariableModularMul.roundGates bit).map
            (EncodedBit.GateSpec.event .empty)).count
            (.gate .toffoli) ≤
            (108 * params.width + 14) + 30 * params.width := by
        simpa only [VariableModularMul.roundCircuit,
          EncodedBit.GateSpec.programList_eventCost,
          ResourcePool.count_ofList] using
          VariableModularMul.roundCircuit_toffoli_count_le bit
      rw [forwardGates, List.map_append, List.count_append,
        List.length_cons, Nat.succ_mul,
        Nat.add_comm
          (rest.length *
            ((108 * params.width + 14) + 30 * params.width))
          ((108 * params.width + 14) + 30 * params.width)]
      exact Nat.add_le_add hround (forwardGates_toffoli_count_le rest)

private theorem forwardGates_cnotMultiplicity_sum_le :
    ∀ roundBits : List (Fin params.width),
      ((forwardGates roundBits).map
          EncodedBit.GateSpec.cnotMultiplicity).sum ≤
        roundBits.length *
          ((8 * params.width + 1) +
            (27 * params.width + 21))
  | [] => by simp [forwardGates]
  | bit :: rest => by
      rw [forwardGates, List.map_append, List.sum_append,
        List.length_cons, Nat.succ_mul,
        Nat.add_comm
          (rest.length *
            ((8 * params.width + 1) +
              (27 * params.width + 21)))
          ((8 * params.width + 1) +
            (27 * params.width + 21))]
      exact Nat.add_le_add
        (VariableModularMul.roundGates_cnotMultiplicity_sum_le bit)
        (forwardGates_cnotMultiplicity_sum_le rest)

private theorem forwardGates_eventCount_le :
    ∀ roundBits : List (Fin params.width),
      (forwardGates roundBits).length ≤
        roundBits.length *
          ((116 * params.width + 15) +
            (57 * params.width + 52))
  | [] => by simp [forwardGates]
  | bit :: rest => by
      have hround : (VariableModularMul.roundGates bit).length ≤
          (116 * params.width + 15) +
            (57 * params.width + 52) := by
        simpa only [VariableModularMul.roundCircuit,
          EncodedBit.GateSpec.programList_eventCost_card] using
          VariableModularMul.roundCircuit_eventCount_le bit
      rw [forwardGates, List.length_append, List.length_cons, Nat.succ_mul,
        Nat.add_comm
          (rest.length *
            ((116 * params.width + 15) +
              (57 * params.width + 52)))
          ((116 * params.width + 15) +
            (57 * params.width + 52))]
      exact Nat.add_le_add hround (forwardGates_eventCount_le rest)

private theorem restoreGates_toffoli_count_le :
    ∀ rounds : Nat,
      ((restoreGates rounds).map (EncodedBit.GateSpec.event .empty)).count
          (.gate .toffoli) ≤
        rounds * (30 * params.width)
  | 0 => by simp [restoreGates]
  | rounds + 1 => by
      have hinverse :
          (inverseDoublingGates.map (EncodedBit.GateSpec.event .empty)).count
              (.gate .toffoli) = 30 * params.width := by
        simpa only [inverseDoublingCircuit,
          EncodedBit.GateSpec.programList_eventCost,
          ResourcePool.count_ofList] using inverseDoublingCircuit_toffoli_count_eq
      rw [restoreGates, List.map_append, List.count_append, Nat.succ_mul,
        Nat.add_comm (rounds * (30 * params.width))
          (30 * params.width)]
      exact Nat.add_le_add hinverse.le (restoreGates_toffoli_count_le rounds)

private theorem restoreGates_cnotMultiplicity_sum_le :
    ∀ rounds : Nat,
      ((restoreGates rounds).map
          EncodedBit.GateSpec.cnotMultiplicity).sum ≤
        rounds * (27 * params.width + 21)
  | 0 => by simp [restoreGates]
  | rounds + 1 => by
      rw [restoreGates, List.map_append, List.sum_append, Nat.succ_mul,
        Nat.add_comm
          (rounds * (27 * params.width + 21))
          (27 * params.width + 21)]
      exact Nat.add_le_add inverseDoublingGates_cnotMultiplicity_sum_le
        (restoreGates_cnotMultiplicity_sum_le rounds)

private theorem restoreGates_eventCount_le :
    ∀ rounds : Nat,
      (restoreGates rounds).length ≤
        rounds * (57 * params.width + 52)
  | 0 => by simp [restoreGates]
  | rounds + 1 => by
      have hinverse : inverseDoublingGates.length ≤
          57 * params.width + 52 := by
        simpa only [inverseDoublingCircuit,
          EncodedBit.GateSpec.programList_eventCost_card] using
          inverseDoublingCircuit_eventCount_le
      rw [restoreGates, List.length_append, Nat.succ_mul,
        Nat.add_comm (rounds * (57 * params.width + 52))
          (57 * params.width + 52)]
      exact Nat.add_le_add hinverse (restoreGates_eventCount_le rounds)

private theorem prefix_length :
    (bits.take (params.width - 1)).length = params.width - 1 := by
  simp [bits, List.length_take]

/-- The complete actual variable-multiplication circuit obeys `toffoliBound`. -/
theorem circuit_toffoli_count_le :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .toffoli) circuit.eventCost ≤ toffoliBound := by
  have hforward :=
    forwardGates_toffoli_count_le (bits.take (params.width - 1))
  have hselected :
      ((VariableModularMul.selectedAddGates lastBit).map
          (EncodedBit.GateSpec.event .empty)).count (.gate .toffoli) ≤
        108 * params.width + 14 := by
    simpa only [VariableModularMul.selectedAddCircuit,
      EncodedBit.GateSpec.programList_eventCost, ResourcePool.count_ofList]
      using VariableModularMul.selectedAddCircuit_toffoli_count_le lastBit
  have hrestore := restoreGates_toffoli_count_le (params.width - 1)
  rw [prefix_length] at hforward
  have htotal :=
    Nat.add_le_add hforward (Nat.add_le_add hselected hrestore)
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty gates).eventCost ≤ _
  rw [EncodedBit.GateSpec.programList_eventCost, ResourcePool.count_ofList]
  unfold gates toffoliBound toffoliBoundFor
  simp only [List.map_append, List.count_append, Nat.add_assoc]
  calc
    _ ≤ (params.width - 1) *
          ((108 * params.width + 14) + 30 * params.width) +
        (108 * params.width + 14) +
          (params.width - 1) * (30 * params.width) := by
      simpa only [Nat.add_assoc] using htotal
    _ ≤ 168 * params.width ^ 2 + 14 * params.width := by
      have hpred : params.width - 1 + 1 = params.width := by
        exact Nat.sub_add_cancel params.widthPos
      have hpredLe : params.width - 1 ≤ params.width := Nat.sub_le _ _
      nlinarith

/-- The complete literal variable-multiplication schedule obeys its closed
Toffoli-coordinate bound. -/
theorem gates_toffoliMultiplicity_sum_le :
    (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      toffoliBound := by
  simpa only [circuit,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum] using
      circuit_toffoli_count_le

/-- The complete literal variable-multiplication schedule obeys its closed
CNOT-coordinate bound. -/
theorem gates_cnotMultiplicity_sum_le :
    (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum ≤ cnotBound := by
  have hforward :=
    forwardGates_cnotMultiplicity_sum_le
      (bits.take (params.width - 1))
  have hselected :=
    VariableModularMul.selectedAddGates_cnotMultiplicity_sum lastBit
  have hrestore := restoreGates_cnotMultiplicity_sum_le (params.width - 1)
  rw [prefix_length] at hforward
  have htotal :=
    Nat.add_le_add (Nat.add_le_add hforward hselected.le) hrestore
  unfold gates cnotBound cnotBoundFor
  simp only [List.map_append, List.sum_append]
  calc
    _ ≤ (params.width - 1) *
          ((8 * params.width + 1) + (27 * params.width + 21)) +
        (8 * params.width + 1) +
          (params.width - 1) * (27 * params.width + 21) := htotal
    _ ≤ 62 * params.width ^ 2 + 43 * params.width := by
      have hpred : params.width - 1 + 1 = params.width := by
        exact Nat.sub_add_cancel params.widthPos
      have hpredLe : params.width - 1 ≤ params.width := Nat.sub_le _ _
      nlinarith

/-- The complete actual variable-multiplication circuit obeys `eventCountBound`. -/
theorem circuit_eventCount_le : circuit.eventCost.card ≤ eventCountBound := by
  have hforward :=
    forwardGates_eventCount_le (bits.take (params.width - 1))
  have hselected : (VariableModularMul.selectedAddGates lastBit).length ≤
      116 * params.width + 15 := by
    simpa only [VariableModularMul.selectedAddCircuit,
      EncodedBit.GateSpec.programList_eventCost_card] using
      VariableModularMul.selectedAddCircuit_eventCount_le lastBit
  have hrestore := restoreGates_eventCount_le (params.width - 1)
  rw [prefix_length] at hforward
  have htotal :=
    Nat.add_le_add hforward (Nat.add_le_add hselected hrestore)
  change (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty gates).eventCost.card ≤ _
  rw [EncodedBit.GateSpec.programList_eventCost_card]
  unfold gates eventCountBound eventCountBoundFor
  simp only [List.length_append, Nat.add_assoc]
  calc
    _ ≤ (params.width - 1) *
          ((116 * params.width + 15) + (57 * params.width + 52)) +
        (116 * params.width + 15) +
          (params.width - 1) * (57 * params.width + 52) := by
      simpa only [Nat.add_assoc] using htotal
    _ ≤ 230 * params.width ^ 2 + 119 * params.width := by
      have hpred : params.width - 1 + 1 = params.width := by
        exact Nat.sub_add_cancel params.widthPos
      have hpredLe : params.width - 1 ≤ params.width := Nat.sub_le _ _
      nlinarith

/-- The literal source gate list obeys the same closed event-count bound as
the circuit compiled from it. -/
theorem gates_length_le : gates.length ≤ eventCountBound := by
  simpa only [circuit,
    EncodedBit.GateSpec.programList_eventCost_card] using
    circuit_eventCount_le

/-- The complete literal variable-multiplication schedule obeys its closed
X-coordinate bound. -/
theorem gates_xMultiplicity_sum_le :
    (gates.map EncodedBit.GateSpec.xMultiplicity).sum ≤ xBound := by
  have hcoordinates := EncodedBit.GateSpec.length_eq_multiplicity_sums gates
  have hx :
      (gates.map EncodedBit.GateSpec.xMultiplicity).sum ≤ gates.length := by
    rw [hcoordinates]
    omega
  simpa only [xBound, xBoundFor, eventCountBound] using
    hx.trans gates_length_le

/-- Circuit-only unit depth of the same schedule is bounded by its event bound. -/
theorem circuit_unitDepth_le :
    circuit.evaluatedEventDepth (fun _ => 1) ≤ unitDepthBound := by
  change (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    gates).evaluatedEventDepth
      (fun _ => 1) ≤ _
  rw [EncodedBit.GateSpec.programList_evaluatedEventDepth_unit]
  simpa only [unitDepthBound, unitDepthBoundFor, eventCountBound] using
    gates_length_le

end

end VariableModularMulSchedule

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic

end
