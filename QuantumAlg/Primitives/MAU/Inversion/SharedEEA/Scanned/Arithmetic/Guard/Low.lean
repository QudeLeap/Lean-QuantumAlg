/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Nonzero
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Readout
import all QuantumAlg.Components.Encoded.BitGates.Dirty.Xor

/-!
# Actual low-instruction phase and retained-Sign guards

Three disjoint public patterns implement each source phase condition.
The remainder pattern also performs its actual complete nonzero-divisor
test. Original Iter is the retained control, while the one dirty operand
bit is restored by each call. Low arithmetic retains the Sign value read
by the guard [LYL+26, sec_EEA/sub_opt.tex:43-48,61-66].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard

noncomputable section

open EncodedBit

/-- Every actual phase native word has one of the three fixed enabled physical source patterns. -/
def lowGates (width : Nat) (coefficient : Bool) : List (GateSpec (encoding width)) :=
  if coefficient then
    phaseGates width 3 (by decide) ![true, false, false] ++
      phaseGates width 3 (by decide) ![true, true, false] ++
      phaseGates width 3 (by decide) ![true, true, true]
  else
    nonzeroGates width 3 (by decide) ![false, false, false] ++
      nonzeroGates width 3 (by decide) ![false, false, true] ++
      nonzeroGates width 3 (by decide) ![false, true, false]

/-- The exact independent original-field condition for the two low arithmetic instructions. -/
def lowStep (width : Nat) (coefficient : Bool) (state : Data width) : Data width :=
  if (flag width 3).get state &&
      (if coefficient then state.1.flags.first && (state.1.flags.second || !state.1.flags.sign)
      else !state.1.flags.first && (!state.1.flags.second || !state.1.flags.sign) &&
        decide (state.1.divisorLength ≠ 0)) then
    (flag width 4).flip state else state

private def patternCondition (width : Nat) (nonzero : Bool) (expected : Fin 3 → Bool)
    (state : Data width) : Bool :=
  state.1.flags.iteration &&
    (decide (state.1.flags.first = expected 0 ∧ state.1.flags.second = expected 1 ∧
      state.1.flags.sign = expected 2) &&
      (if nonzero then decide (state.1.divisorLength ≠ 0) else true))

private lemma iteration_get (width : Nat) (state : Data width) :
    (flag width 3).get state = state.1.flags.iteration := rfl

private lemma phasePattern_step (width : Nat) (expected : Fin 3 → Bool) (state : Data width) :
    GateSpec.stepList (phaseGates width 3 (by decide) expected) state =
      predicateFlip (flag width 4) (patternCondition width false expected) state := by
  rw [phaseGates_step]
  simp only [flags_matches_three, predicateFlip, patternCondition, Bool.false_eq_true,
    if_false, Bool.and_true]
  change (if state.1.flags.iteration then
    if state.1.flags.first = expected 0 ∧ state.1.flags.second = expected 1 ∧
      state.1.flags.sign = expected 2 then (flag width 4).flip state else state else state) = _
  cases state.1.flags.iteration <;>
    simp only [Bool.false_eq_true, if_false, if_true, Bool.false_and,
      Bool.true_and, decide_eq_true_eq]

private lemma nonzeroPattern_step (width : Nat) (expected : Fin 3 → Bool) (state : Data width) :
    GateSpec.stepList (nonzeroGates width 3 (by decide) expected) state =
      predicateFlip (flag width 4) (patternCondition width true expected) state := by
  rw [nonzeroGates_step]
  simp only [nonzeroStep, flags_matches_three, predicateFlip, patternCondition,
    if_true, Bool.decide_and]
  rfl

private lemma patternCondition_stable (width : Nat) (nonzero : Bool)
    (expected : Fin 3 → Bool) (state : Data width) :
    patternCondition width nonzero expected ((flag width 4).flip state) =
      patternCondition width nonzero expected state := rfl

private lemma threePatterns (width : Nat) (nonzero : Bool)
    (first second third : Fin 3 → Bool) (state : Data width) :
    predicateFlip (flag width 4) (patternCondition width nonzero third)
      (predicateFlip (flag width 4) (patternCondition width nonzero second)
        (predicateFlip (flag width 4) (patternCondition width nonzero first) state)) =
      predicateFlip (flag width 4) (fun value =>
        patternCondition width nonzero first value ^^
          patternCondition width nonzero second value ^^
            patternCondition width nonzero third value) state := by
  rw [predicateFlip_comp _ _ _ (patternCondition_stable width nonzero second),
    predicateFlip_comp _ _ _ (patternCondition_stable width nonzero third)]

/-- The finite Boolean truth table is independent of the large encoded-state expression. -/
private lemma patternTruth (coefficient iteration first second sign nonzero : Bool) :
    (if coefficient then
      (iteration && decide (first = true ∧ second = false ∧ sign = false)) ^^
        (iteration && decide (first = true ∧ second = true ∧ sign = false)) ^^
          (iteration && decide (first = true ∧ second = true ∧ sign = true))
    else
      (iteration && (decide (first = false ∧ second = false ∧ sign = false) && nonzero)) ^^
        (iteration && (decide (first = false ∧ second = false ∧ sign = true) && nonzero)) ^^
          (iteration && (decide (first = false ∧ second = true ∧ sign = false) && nonzero))) =
      (iteration && if coefficient then first && (second || !sign)
        else !first && (!second || !sign) && nonzero) := by
  cases coefficient <;> cases iteration <;> cases first <;> cases second <;>
    cases sign <;> cases nonzero <;> decide

/-- The complete actual finite native word has precisely the source phase/Sign action. -/
lemma lowGates_step (width : Nat) (coefficient : Bool) (state : Data width) :
    GateSpec.stepList (lowGates width coefficient) state = lowStep width coefficient state := by
  cases coefficient with
  | false =>
      simp only [lowGates, Bool.false_eq_true, if_false, GateSpec.stepList_append,
        nonzeroPattern_step, threePatterns]
      unfold predicateFlip patternCondition lowStep
      have truth := patternTruth false state.1.flags.iteration state.1.flags.first
        state.1.flags.second state.1.flags.sign (decide (state.1.divisorLength ≠ 0))
      simpa only [Bool.false_eq_true, if_false, if_true, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        iteration_get] using
        congrArg (fun selected : Bool => if selected then (flag width 4).flip state else state)
          truth
  | true =>
      simp only [lowGates, if_true, GateSpec.stepList_append, phasePattern_step, threePatterns]
      unfold predicateFlip patternCondition lowStep
      have truth := patternTruth true state.1.flags.iteration state.1.flags.first
        state.1.flags.second state.1.flags.sign (decide (state.1.divisorLength ≠ 0))
      simpa only [if_true, Bool.false_eq_true, if_false, Bool.and_true,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, iteration_get] using
        congrArg (fun selected : Bool => if selected then (flag width 4).flip state else state)
          truth

/-- The same emitted gates preserve all original coherent amplitudes and complementary systems. -/
lemma lowProgram_realizes (width : Nat) (coefficient : Bool)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width)
      (GateSpec.programList (QubitLayout.canonical _) .empty (lowGates width coefficient))
      environment (lowStep width coefficient) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (lowGates_step width coefficient) environment

/-- Every actual pattern mask and full dirty-work cleanup is included in the elementary bound. -/
lemma lowGates_length_le (width : Nat) (coefficient : Bool) :
    (lowGates width coefficient).length ≤
      if coefficient then 3 * 41 else 3 * (41 + (10 * (width.size + 4) + 1)) := by
  cases coefficient with
  | false =>
      simp only [lowGates, Bool.false_eq_true, if_false, List.length_append]
      have first := nonzeroGates_length_le width 3 (by decide) ![false, false, false]
      have second := nonzeroGates_length_le width 3 (by decide) ![false, false, true]
      have third := nonzeroGates_length_le width 3 (by decide) ![false, true, false]
      omega
  | true =>
      simp only [lowGates, if_true, List.length_append]
      have first := phaseGates_length_le width 3 (by decide) ![true, false, false]
      have second := phaseGates_length_le width 3 (by decide) ![true, true, false]
      have third := phaseGates_length_le width 3 (by decide) ![true, true, true]
      omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard
