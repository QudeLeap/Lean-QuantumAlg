/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Frame

/-!
# Actual Iter-controlled phase patterns and complete divisor-zero rejection

Every pattern reads its declared original sources and toggles original
Ctrl. Original Iter is retained control and an arbitrary original
operand bit supplies restored dirty work. Both masks and all native
conjunction gates are executed and charged.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard

noncomputable section

open EncodedBit

/-- Actual phase pattern controlled by the same original arbitrary Iter. -/
def phaseGates (width count : Nat) (bound : count ≤ 3) (expected : Fin count → Bool) :
    List (GateSpec (encoding width)) :=
  (flags width count bound).controlledPatternGates (flag width 3)
    (iteration_flags_ne width count bound)
    (iteration_output_work_ne width).1 (iteration_output_work_ne width).2 expected

/-- The actual complete phase pattern uses its original physical inputs and retained control. -/
lemma phaseGates_step (width count : Nat) (bound : count ≤ 3) (expected : Fin count → Bool)
    (state : Data width) :
    GateSpec.stepList (phaseGates width count bound expected) state =
      if (flag width 3).get state then
        (if (flags width count bound).PatternMatches expected state then
          (flag width 4).flip state else state) else state :=
  (flags width count bound).controlledPatternGates_step (flag width 3)
    (iteration_flags_ne width count bound)
    (iteration_output_work_ne width).1 (iteration_output_work_ne width).2 expected state

/-- Native zero-divisor rejection reads every actual divisor-length bit, without truncation. -/
def zeroDivisorGates (width count : Nat) (bound : count ≤ 3) (expected : Fin count → Bool) :
    List (GateSpec (encoding width)) :=
  (flagsDivisor width count bound).controlledPatternGates (flag width 3)
    (iteration_flagsDivisor_ne width count bound)
    (iteration_output_work_ne width).1 (iteration_output_work_ne width).2
    (Fin.append expected (fun _ => false))

private lemma divisor_zero_iff (width : Nat) (state : Data width) :
    (∀ index, ((divisor width).bit index).get state = false) ↔
      state.1.divisorLength = 0#width.size := by
  constructor
  · intro zero
    apply BitVec.eq_of_getMsbD_eq
    intro index within
    have read := zero ⟨index, within⟩
    simp only [divisor, sourceBit_get, divisorLengthBit_get] at read
    simpa only [BitVec.getMsbD_zero] using read
  · intro zero index
    simp only [divisor, sourceBit_get, divisorLengthBit_get, zero, BitVec.getMsbD_zero]

private lemma flagsDivisor_matches (width count : Nat) (bound : count ≤ 3)
    (expected : Fin count → Bool) (state : Data width) :
    (flagsDivisor width count bound).PatternMatches
        (Fin.append expected (fun _ => false)) state ↔
      (flags width count bound).PatternMatches expected state ∧
        state.1.divisorLength = 0#width.size := by
  have actual := Word.OneDirtyLayout.appendSources_matches (flags width count bound)
    (divisor width)
    (by
      intro left right same
      apply Fin.ext
      have values := congrArg Fin.val same
      simp only [divisor_wire] at values
      omega)
    (fun left right => flag_divisor_ne width _ right)
    (fun index => (flag_divisor_ne width 4 index).symm)
    (divisor_work_ne width) expected (fun _ => false) state
  simpa only [flagsDivisor, divisor_zero_iff] using actual

/-- Every original Store-free basis label gets exactly its retained-control zero-divisor flip. -/
lemma zeroDivisorGates_step (width count : Nat) (bound : count ≤ 3)
    (expected : Fin count → Bool) (state : Data width) :
    GateSpec.stepList (zeroDivisorGates width count bound expected) state =
      if (flag width 3).get state then
        (if (flags width count bound).PatternMatches expected state ∧
            state.1.divisorLength = 0#width.size then
          (flag width 4).flip state else state) else state := by
  have actual := (flagsDivisor width count bound).controlledPatternGates_step (flag width 3)
    (iteration_flagsDivisor_ne width count bound)
    (iteration_output_work_ne width).1 (iteration_output_work_ne width).2
    (Fin.append expected (fun _ => false)) state
  have output : (flagsDivisor width count bound).output = flag width 4 := rfl
  rw [output] at actual
  simpa only [zeroDivisorGates, flagsDivisor_matches] using actual

/-- The entire original complement and all coherent phases follow the same actual phase gates. -/
lemma phaseProgram_realizes (width count : Nat) (bound : count ≤ 3)
    (expected : Fin count → Bool) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width)
      (GateSpec.programList (QubitLayout.canonical _) .empty
        (phaseGates width count bound expected)) environment
      (fun state => if (flag width 3).get state then
        (if (flags width count bound).PatternMatches expected state then
          (flag width 4).flip state else state) else state) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (phaseGates_step width count bound expected) environment

/-- Actual masks and arbitrary-work cleanup have a uniform linear elementary bound. -/
lemma phaseGates_length_le (width count : Nat) (bound : count ≤ 3)
    (expected : Fin count → Bool) :
    (phaseGates width count bound expected).length ≤ 10 * (count + 1) + 1 :=
  (flags width count bound).controlledPatternGates_length_le (flag width 3)
    (iteration_flags_ne width count bound)
    (iteration_output_work_ne width).1 (iteration_output_work_ne width).2 expected

/-- Rejection charges all full divisor sources, masks and actual dirty-work cleanup. -/
lemma zeroDivisorGates_length_le (width count : Nat) (bound : count ≤ 3)
    (expected : Fin count → Bool) :
    (zeroDivisorGates width count bound expected).length ≤
      10 * (count + width.size + 1) + 1 :=
  (flagsDivisor width count bound).controlledPatternGates_length_le (flag width 3)
    (iteration_flagsDivisor_ne width count bound)
    (iteration_output_work_ne width).1 (iteration_output_work_ne width).2
    (Fin.append expected (fun _ => false))

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard
