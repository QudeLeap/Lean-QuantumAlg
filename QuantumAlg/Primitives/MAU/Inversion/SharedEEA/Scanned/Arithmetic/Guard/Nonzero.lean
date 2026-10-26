/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Pattern

/-!
# Actual nonzero-divisor phase selection with arbitrary original Iter

The phase pattern and the same pattern with a complete divisor-zero
test execute as two actual native words. Their output xors retain only
the nonzero-divisor case. All original source fields and arbitrary work
are restored within both real calls.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard

noncomputable section

open EncodedBit

/-- Two actual native predicate words implement phase and nonzero divisor, under original Iter. -/
def nonzeroGates (width count : Nat) (bound : count ≤ 3) (expected : Fin count → Bool) :
    List (GateSpec (encoding width)) :=
  phaseGates width count bound expected ++ zeroDivisorGates width count bound expected

/-- Independent retained-control predicate on the original complete finite fields. -/
def nonzeroStep (width count : Nat) (bound : count ≤ 3) (expected : Fin count → Bool)
    (state : Data width) : Data width :=
  if (flag width 3).get state && decide
      ((flags width count bound).PatternMatches expected state ∧ state.1.divisorLength ≠ 0) then
    (flag width 4).flip state else state

/-- Both actual full-state calls cancel their zero-divisor output toggle exactly. -/
lemma nonzeroGates_step (width count : Nat) (bound : count ≤ 3) (expected : Fin count → Bool)
    (state : Data width) :
    GateSpec.stepList (nonzeroGates width count bound expected) state =
      nonzeroStep width count bound expected state := by
  have iteration : (flag width 3).get ((flag width 4).flip state) =
      (flag width 3).get state :=
    get_flip_of_wire_ne (flag width 4) (flag width 3)
      (iteration_output_work_ne width).1.symm state
  have matchedAfter :
      (flags width count bound).PatternMatches expected ((flag width 4).flip state) ↔
      (flags width count bound).PatternMatches expected state :=
    (flags width count bound).patternMatches_flip_output expected state
  have divisorRetained : ((flag width 4).flip state).1.divisorLength =
      state.1.divisorLength := rfl
  rw [nonzeroGates, GateSpec.stepList_append, phaseGates_step]
  by_cases selected : (flag width 3).get state = true
  · rw [if_pos selected]
    by_cases phase : (flags width count bound).PatternMatches expected state
    · rw [if_pos phase, zeroDivisorGates_step, iteration, if_pos selected]
      by_cases zero : state.1.divisorLength = 0
      · rw [if_pos ⟨matchedAfter.mpr phase, divisorRetained.trans zero⟩, EncodedBit.flip_flip]
        simp only [nonzeroStep, selected, Bool.true_and, decide_eq_true_eq]
        rw [if_neg (fun value => value.2 zero)]
      · rw [if_neg (fun value => zero (divisorRetained.symm.trans value.2))]
        simp only [nonzeroStep, selected, Bool.true_and, decide_eq_true_eq]
        rw [if_pos ⟨phase, zero⟩]
    · rw [if_neg phase, zeroDivisorGates_step, if_pos selected,
        if_neg (fun value => phase value.1)]
      simp only [nonzeroStep, selected, Bool.true_and, decide_eq_true_eq]
      rw [if_neg (fun value => phase value.1)]
  · rw [if_neg selected, zeroDivisorGates_step, if_neg selected]
    simp [nonzeroStep, selected]

/-- The complete actual word has the same coherent action on all original finite labels. -/
lemma nonzeroProgram_realizes (width count : Nat) (bound : count ≤ 3)
    (expected : Fin count → Bool) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width)
      (GateSpec.programList (QubitLayout.canonical _) .empty
        (nonzeroGates width count bound expected)) environment
      (nonzeroStep width count bound expected) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (nonzeroGates_step width count bound expected) environment

/-- Every mask and both complete native conjunction cleanups remain in the bound. -/
lemma nonzeroGates_length_le (width count : Nat) (bound : count ≤ 3)
    (expected : Fin count → Bool) :
    (nonzeroGates width count bound expected).length ≤
      (10 * (count + 1) + 1) + (10 * (count + width.size + 1) + 1) := by
  rw [nonzeroGates, List.length_append]
  exact Nat.add_le_add (phaseGates_length_le width count bound expected)
    (zeroDivisorGates_length_le width count bound expected)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard
