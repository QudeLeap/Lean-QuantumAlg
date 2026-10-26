/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Resources.General
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Resources.Toffoli
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Resources.Coordinates

/-!
# Parity-independent native bounds of the same measured modular-addition word

The independent row ledger includes both actual comparisons, both measured
additions and the one flag Toffoli. Width two is counted separately. No
assumption about an odd modulus or a nonzero canonical offset is needed
for these resource bounds [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Both actual comparator carry words are counted even at the separate two-bit width. -/
lemma comparisonGates_toffoli_bound_general (layout : Layout encoding width) (wide : 2 ≤ width)
    (threshold : BitVec width) :
    ((layout.comparisonGates wide threshold).map toffoliMultiplicity).sum ≤
      if width = 2 then 5 else 4 * width - 4 := by
  by_cases zero : threshold = 0
  · subst threshold
    rw [comparisonGates_zero_toffoli]
    exact Nat.zero_le _
  · have low : ((-threshold).getLsbD 0).toNat ≤ 1 := by
      cases (-threshold).getLsbD 0 <;> decide
    by_cases two : width = 2
    · subst width
      rw [if_pos rfl, comparisonGates, if_neg zero]
      simp only [List.map_append, List.sum_append, List.map_reverse, List.sum_reverse,
        activePair_toffoli, CarryLayout.cleanLowGates_toffoliMultiplicity]
      have lower : (((-threshold).setWidth (2 - 1)).getLsbD 0).toNat =
          ((-threshold).getLsbD 0).toNat := by
        rw [BitVec.getLsbD_setWidth]
        rfl
      rw [lower]
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        toffoliMultiplicity, if_true, if_false]
      omega
    · rw [if_neg two, comparisonGates_toffoli layout wide (by omega) threshold zero]
      omega

/-- The separate two-bit comparator and the larger native recurrence have independent CNOT caps. -/
lemma comparisonGates_cnot_bound_general (layout : Layout encoding width) (wide : 2 ≤ width)
    (threshold : BitVec width) :
    ((layout.comparisonGates wide threshold).map cnotMultiplicity).sum ≤
      if width = 2 then 12 else 14 * width - 18 := by
  by_cases two : width = 2
  · subst width
    rw [if_pos rfl]
    unfold comparisonGates
    split
    · exact Nat.zero_le _
    · simp only [List.map_append, List.sum_append, List.map_reverse, List.sum_reverse]
      have full := CarryLayout.cleanLowGates_cnot_bound (layout.comparisonLayout wide) (-threshold)
      have lower := CarryLayout.cleanLowGates_cnot_bound (layout.comparisonLowerLayout wide)
        ((-threshold).setWidth (2 - 1))
      change 0 + _ + _ + 1 + 0 ≤ _
      change (((layout.comparisonLayout wide).cleanLowGates (-threshold)).map
        cnotMultiplicity).sum ≤ 8 at full
      change (((layout.comparisonLowerLayout wide).cleanLowGates
        ((-threshold).setWidth (2 - 1))).map cnotMultiplicity).sum ≤ 3 at lower
      omega
  · rw [if_neg two]
    exact comparisonGates_cnot_bound layout wide (by omega) threshold

/-- The row Toffoli cap includes all literal stages for arbitrary static constants and parity. -/
lemma modularWord_toffoli_bound_general (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) :
    wordToffoliCount (layout.modularWord wide modulus constant) ≤
      if width = 2 then 13 else 14 * width - 19 := by
  unfold modularWord
  split
  · exact Nat.zero_le _
  · simp only [wordToffoliCount_append, nativeWord_toffoli, toggleFlag_toffoli]
    have first := comparisonGates_toffoli_bound_general layout wide (modulus - constant)
    have last := comparisonGates_toffoli_bound_general layout wide constant
    have addFirst := Measured.Layout.adderWord_toffoli_bound_general
      layout.adderLayout wide constant
    have addLast := Measured.Layout.adderWord_toffoli_bound_general
      layout.adderLayout wide (constant - modulus)
    by_cases two : width = 2
    · rw [if_pos two] at first last addFirst addLast ⊢
      omega
    · rw [if_neg two] at first last addFirst addLast ⊢
      omega

/-- CNOT and paid one-qubit allowances include every stage of the actual parity-independent row. -/
lemma modularWord_coordinate_bounds_general (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) :
    wordCnotCount (layout.modularWord wide modulus constant) ≤
        (if width = 2 then 30 else 54 * width - 90) ∧
      wordSingleQubitBound (layout.modularWord wide modulus constant) ≤ 12 * width - 16 := by
  unfold modularWord
  split
  · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · have first := comparisonGates_cnot_bound_general layout wide (modulus - constant)
    have last := comparisonGates_cnot_bound_general layout wide constant
    have addFirst := Measured.Layout.adderWord_cnot_bound_general
      layout.adderLayout wide constant
    have addLast := Measured.Layout.adderWord_cnot_bound_general
      layout.adderLayout wide (constant - modulus)
    constructor
    · simp only [wordCnotCount_append]
      change ((layout.comparisonGates wide (modulus - constant)).map cnotMultiplicity).sum +
        wordCnotCount (layout.adderLayout.adderWord wide constant) + 0 +
          wordCnotCount (layout.adderLayout.adderWord wide (constant - modulus)) +
            ((layout.comparisonGates wide constant).map cnotMultiplicity).sum ≤ _
      by_cases two : width = 2
      · rw [if_pos two] at first last addFirst addLast ⊢
        omega
      · rw [if_neg two] at first last addFirst addLast ⊢
        omega
    · have nativeSingle (gates : List (GateSpec encoding)) :
          wordSingleQubitBound (records := width - 2) [.native gates] =
            (gates.map xMultiplicity).sum := rfl
      simp only [wordSingleQubitBound_append, nativeSingle, comparisonGates_x_count,
        Measured.Layout.adderWord_single_bound]
      change 0 + (6 * width - 8) + 0 + (6 * width - 8) + 0 ≤ _
      omega

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
