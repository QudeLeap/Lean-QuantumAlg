/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Gates
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Controlled.Counts

/-!
# The current outer-control expansion and the actual two-control producer

The comparison program controls the already optimized one-control BCBC
accumulator. Thus both programs have the same doubly controlled comparisons;
only the outer control of each cancelling bi-flip pair is removed. The
Toffoli, CNOT, single-qubit and serial quantum-time coordinates are kept
separate. Every width, modulus and complete input label remains admitted.
-/

namespace QuantumAlg.MAU.Multiplication.VariableGidney.PushdownComparison

noncomputable section

open Nat.FixedWidth EncodedBit GateSpec
open Accumulate.Gidney.ControlPushdown

/-- The previous outer expansion of the current one-control accumulator. -/
def previousStageGates (width : Nat) (modulus : Fin (2 ^ width + 1))
    (index : Fin width) : List (GateSpec (encoding width)) :=
  originalControlled width width index
    (Accumulate.Gidney.gates width modulus (2 ^ index.val))

/-- The previous word and the actual replacement agree on every complete label. -/
lemma previousStage_step (width : Nat) (modulus : Fin (2 ^ width + 1))
    (index : Fin width) (state : Registers width) :
    stepList (previousStageGates width modulus index) state =
      stepList (stageGates width modulus index) state := by
  have previous := originalControlled_step width width index
    (Accumulate.Gidney.gates width modulus (2 ^ index.val)) state
  rw [Accumulate.Gidney.gidneyAccumulateGates_step] at previous
  exact previous.trans (variableGidney_stageGates_step width modulus index state).symm

/-- The previous complete program, retained only for exact resource comparison. -/
def previousPrefixGates (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (count : Nat) → count ≤ width → List (GateSpec (encoding width))
  | 0, _ => []
  | index + 1, within => previousPrefixGates width modulus index (by omega) ++
      previousStageGates width modulus ⟨index, by omega⟩

/-- The actual replacement preserves every previous prefix action, including idle branches. -/
lemma previousPrefix_step (width : Nat) (modulus : Fin (2 ^ width + 1))
    (count : Nat) (within : count ≤ width) (state : Registers width) :
    stepList (previousPrefixGates width modulus count within) state =
      stepList (prefixGates width modulus count within) state := by
  induction count generalizing state with
  | zero => rfl
  | succ index ih =>
      rw [previousPrefixGates, prefixGates, stepList_append, stepList_append,
        ih (by omega), previousStage_step]

/-- Every complete first-input stage is included in its original order. -/
def previousGates (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    List (GateSpec (encoding width)) :=
  previousPrefixGates width modulus width (Nat.le_refl width)

/-- No canonical-label or initialization restriction is needed for the whole word. -/
lemma previousGates_step (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state : Registers width) :
    stepList (previousGates width modulus) state = stepList (gates width modulus) state :=
  previousPrefix_step width modulus width (Nat.le_refl width) state

/-- The actual additional CNOTs in the three unselected bi-flip pairs. -/
def offsetCnotIncrease (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) : Nat :=
  2 * cCount (Addition.Gidney.biFlipGates (extra + 3)
    (offsetFirstPivot modulus constant)) +
  2 * cCount (Addition.Gidney.biFlipGates (extra + 3) modulus) +
  2 * cCount (Addition.Gidney.biFlipGates (extra + 3)
    (offsetLastPivot modulus constant))

/-- Exact current-baseline comparison on a large-width selected offset. -/
private lemma large_coordinates (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) :
    let previous := outerControl outerWidth (extra + 3) (by omega) address
      (Accumulate.Gidney.stageGates (extra + 3) selector modulus constant)
    let actual := twoStage outerWidth extra address selector modulus constant
    xCount previous = 0 ∧ cCount previous = 0 ∧
      cCount actual = offsetCnotIncrease extra modulus constant ∧
      tCount previous = tCount actual + offsetToffoliSaving extra modulus constant ∧
      previous.length = actual.length + offsetTimeSaving extra modulus constant := by
  dsimp only
  have source : Accumulate.Gidney.stageGates (extra + 3) selector modulus constant =
      relocate extra selector (Accumulate.Gidney.ControlPushdown.canonicalGates
        extra modulus constant) := rfl
  rw [source]
  have old := outerControl_counts outerWidth (extra + 3) (by omega) address
    (relocate extra selector (Accumulate.Gidney.ControlPushdown.canonicalGates
      extra modulus constant))
  have placed := relocate_counts extra selector
    (Accumulate.Gidney.ControlPushdown.canonicalGates extra modulus constant)
  have first := pivot_counts extra (offsetFirstPivot modulus constant)
  have middle := pivot_counts extra modulus
  have last := pivot_counts extra (offsetLastPivot modulus constant)
  have firstNew := twoPivot_counts outerWidth extra address selector
    (offsetFirstPivot modulus constant)
  have middleNew := twoPivot_counts outerWidth extra address selector modulus
  have lastNew := twoPivot_counts outerWidth extra address selector
    (offsetLastPivot modulus constant)
  have oldX := old.1
  have oldC : cCount (outerControl outerWidth (extra + 3) (by omega) address
      (relocate extra selector (Accumulate.Gidney.ControlPushdown.canonicalGates
        extra modulus constant))) = 0 := by
    rw [old.2.1, placed.1, canonical_xCount]
  have newC : cCount (twoStage outerWidth extra address selector modulus constant) =
      offsetCnotIncrease extra modulus constant := by
    simp only [twoStage, cCount_append, firstNew.2.1, middleNew.2.1, lastNew.2.1,
      offsetCnotIncrease]
  have saving : tCount (outerControl outerWidth (extra + 3) (by omega) address
      (relocate extra selector (Accumulate.Gidney.ControlPushdown.canonicalGates
        extra modulus constant))) =
      tCount (twoStage outerWidth extra address selector modulus constant) +
        offsetToffoliSaving extra modulus constant := by
    rw [old.2.2, placed.2.1, placed.2.2]
    simp only [Accumulate.Gidney.ControlPushdown.canonicalGates, cCount_append, tCount_append,
      first.2.1, first.2.2, middle.2.1, middle.2.2, last.2.1, last.2.2,
      twoStage, firstNew.2.2, middleNew.2.2, lastNew.2.2,
      offsetToffoliSaving, pivotToffoliSaving]
    ring
  refine ⟨oldX, oldC, newC, saving, ?_⟩
  rw [length_eq_multiplicity_sums, length_eq_multiplicity_sums]
  change xCount _ + cCount _ + tCount _ =
    xCount _ + cCount _ + tCount _ + offsetTimeSaving extra modulus constant
  rw [oldX, oldC, saving, twoStage_xCount, newC]
  simp only [offsetToffoliSaving, pivotToffoliSaving, offsetTimeSaving, pivotTimeSaving,
    offsetCnotIncrease]
  ring

/-- The native Toffoli reduction at a source-bit stage; small paths are unchanged. -/
def sourceToffoliSaving : (width : Nat) → (modulus : Fin (2 ^ width + 1)) →
    Fin (modulus.val + 1) → Nat
  | 0, _, _ => 0
  | 1, _, _ => 0
  | 2, _, _ => 0
  | extra + 3, modulus, constant => offsetToffoliSaving extra modulus constant

/-- The real serial quantum-time reduction at the same source-bit stage. -/
def sourceTimeSaving : (width : Nat) → (modulus : Fin (2 ^ width + 1)) →
    Fin (modulus.val + 1) → Nat
  | 0, _, _ => 0
  | 1, _, _ => 0
  | 2, _, _ => 0
  | extra + 3, modulus, constant => offsetTimeSaving extra modulus constant

/-- The separate actual CNOT increase at the same source-bit stage. -/
def sourceCnotIncrease : (width : Nat) → (modulus : Fin (2 ^ width + 1)) →
    Fin (modulus.val + 1) → Nat
  | 0, _, _ => 0
  | 1, _, _ => 0
  | 2, _, _ => 0
  | extra + 3, modulus, constant => offsetCnotIncrease extra modulus constant

/-- The previous and actual source stages have independently accounted coordinates. -/
lemma source_coordinates (outerWidth : Nat) : (width : Nat) →
    (address : Fin outerWidth) → (selector : Fin width) →
    (modulus : Fin (2 ^ width + 1)) → (constant : Fin (modulus.val + 1)) →
    let previous := originalControlled outerWidth width address
      (Accumulate.Gidney.stageGates width selector modulus constant)
    let actual := twoStageGates outerWidth width address selector modulus constant
    xCount previous = 0 ∧ cCount previous = 0 ∧
      cCount actual = sourceCnotIncrease width modulus constant ∧
      tCount previous = tCount actual + sourceToffoliSaving width modulus constant ∧
      previous.length = actual.length + sourceTimeSaving width modulus constant
  | 0, _, selector, _, _ => Fin.elim0 selector
  | 1, address, selector, modulus, constant => by
      dsimp only [twoStageGates, sourceCnotIncrease, sourceToffoliSaving, sourceTimeSaving]
      have counts := originalControlled_native_counts outerWidth 1 address
        (Accumulate.Gidney.stageGates 1 selector modulus constant)
      have zero := Accumulate.Gidney.gidneyStage_singleQubit_count 1 selector modulus constant
      have source : xCount (Accumulate.Gidney.stageGates 1 selector modulus constant) = 0 := by
        change ((Accumulate.Gidney.stageGates 1 selector modulus constant).map
          xMultiplicity).sum = 0
        rw [← programList_x_count_eq_sum (QubitLayout.canonical _) .empty,
          programList_eventCost, Accumulate.Gidney.gidneyStageGates_eventCost]
        exact zero
      exact ⟨counts.1, counts.2.trans source, counts.2.trans source, by omega, by omega⟩
  | 2, address, selector, modulus, constant => by
      dsimp only [twoStageGates, sourceCnotIncrease, sourceToffoliSaving, sourceTimeSaving]
      have counts := originalControlled_native_counts outerWidth 2 address
        (Accumulate.Gidney.stageGates 2 selector modulus constant)
      have source : xCount (Accumulate.Gidney.stageGates 2 selector modulus constant) = 0 := by
        change ((Accumulate.Gidney.stageGates 2 selector modulus constant).map
          xMultiplicity).sum = 0
        rw [← programList_x_count_eq_sum (QubitLayout.canonical _) .empty,
          programList_eventCost, Accumulate.Gidney.gidneyStageGates_eventCost]
        exact Accumulate.Gidney.gidneyStage_singleQubit_count 2 selector modulus constant
      exact ⟨counts.1, counts.2.trans source, counts.2.trans source, by omega, by omega⟩
  | extra + 3, address, selector, modulus, constant => by
      simpa only [originalControlled, dif_neg (show ¬extra + 3 ≤ 1 by omega),
        twoStageGates, sourceCnotIncrease, sourceToffoliSaving, sourceTimeSaving]
        using large_coordinates outerWidth extra address selector modulus constant

end

end QuantumAlg.MAU.Multiplication.VariableGidney.PushdownComparison
