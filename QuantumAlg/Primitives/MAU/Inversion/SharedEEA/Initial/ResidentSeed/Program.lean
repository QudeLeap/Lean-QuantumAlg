/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.ResidentSeed.Frame

/-! # Actual parallel native X initialization of the resident source's four small positions -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ResidentSeed

noncomputable section

open EncodedBit

/-- One fixed actual native layer; its four positions are part of the existing source. -/
def program (width : Nat) (positive : 0 < width.size) (tail : BitVec 3) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  WindowLookup.wordXProgram (QubitLayout.canonical _) .empty (target width positive)
    (target_distinct width positive) (constant tail)

/-- All labels are interpreted by the same fixed four-position constant XOR. -/
def step (width : Nat) (positive : 0 < width.size) (tail : BitVec 3) :
    Registers width → Registers width :=
  Word.xorConstantStep (target width positive) (constant tail)

/-- Exact all-label native semantics, including arbitrary supplied Work2. -/
lemma program_realizes (width : Nat) (positive : 0 < width.size) (tail : BitVec 3)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width positive tail) environment
      (step width positive tail) :=
  WindowLookup.wordXProgram_realizes (QubitLayout.canonical _) .empty _ _ _ environment

private def withoutSeed {width : Nat} (state : Registers width) : Registers width :=
  { state with firstWord := 0#(width + 3), coefficientLength := 0#width.size }

private lemma step_complement (width : Nat) (positive : 0 < width.size) (tail : BitVec 3)
    (state : Registers width) :
    withoutSeed (step width positive tail state) = withoutSeed state := by
  apply GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate member
  rw [Word.xorConstantGates] at member
  rcases List.mem_map.mp member with ⟨index, _, rfl⟩
  change ∀ state, withoutSeed (((target width positive).bit index).flip state) = _
  dsimp only [target]
  split <;> intro state <;> rfl

private lemma target_tail_get (width : Nat) (positive : 0 < width.size) (index : Fin 3)
    (state : Registers width) :
    ((target width positive).bit ⟨index.val, by omega⟩).get state =
      state.firstWord.getLsbD index.val := by
  change (if within : index.val < 3 then
    firstWordBit width ⟨width + 2 - index.val, by omega⟩
    else coefficientLengthBit width ⟨width.size - 1, by omega⟩).get state = _
  rw [dif_pos index.isLt, firstWordBit_get]
  have bound : width + 2 - index.val < width + 3 := by omega
  have position : width + 3 - 1 - (width + 2 - index.val) = index.val := by omega
  simp only [BitVec.getMsbD_eq_getLsbD, bound, decide_true, Bool.true_and, position]

private lemma target_length_get (width : Nat) (positive : 0 < width.size)
    (state : Registers width) :
    ((target width positive).bit 3).get state = state.coefficientLength.getLsbD 0 := by
  change (coefficientLengthBit width ⟨width.size - 1, by omega⟩).get state = _
  rw [coefficientLengthBit_get]
  simp only [BitVec.getMsbD_eq_getLsbD]
  simp [show width.size - 1 < width.size by omega]

private lemma firstWord_little_get (width : Nat) (index : Fin (width + 3))
    (state : Registers width) :
    (firstWordBit width index.rev).get state = state.firstWord.getLsbD index.val := by
  rw [firstWordBit_get]
  have bound : index.rev.val < width + 3 := index.rev.isLt
  have position : width + 3 - 1 - index.rev.val = index.val := by
    have within := index.isLt
    simp only [Fin.val_rev]
    omega
  simp only [BitVec.getMsbD_eq_getLsbD, bound, decide_true, Bool.true_and, position]

private lemma length_little_get (width : Nat) (index : Fin width.size)
    (state : Registers width) :
    (coefficientLengthBit width index.rev).get state =
      state.coefficientLength.getLsbD index.val := by
  rw [coefficientLengthBit_get]
  have bound : index.rev.val < width.size := index.rev.isLt
  have position : width.size - 1 - index.rev.val = index.val := by
    have within := index.isLt
    simp only [Fin.val_rev]
    omega
  simp only [BitVec.getMsbD_eq_getLsbD, bound, decide_true, Bool.true_and, position]

private lemma step_firstWord (width : Nat) (positive : 0 < width.size) (tail : BitVec 3)
    (input : BitVec (width + 3)) :
    (step width positive tail (blank width input)).firstWord = tail.setWidth (width + 3) := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  by_cases small : index < 3
  · have actual := Word.xorConstantStep_get_target (target width positive) (constant tail)
      (⟨index, by omega⟩ : Fin 4)
      (fun other different same => different (target_distinct width positive same))
      (blank width input)
    rw [target_blank, Bool.false_xor, constant_read, if_pos small] at actual
    rw [show (⟨index, by omega⟩ : Fin 4) =
      (⟨(⟨index, small⟩ : Fin 3).val, by omega⟩ : Fin 4) from rfl,
      target_tail_get] at actual
    simpa only [step, BitVec.getLsbD_setWidth, within, decide_true, Bool.true_and] using actual
  · have actual := Word.xorConstantStep_get_observed_of_target_ne (target width positive)
      (constant tail) (firstWordBit width (⟨index, within⟩ : Fin (width + 3)).rev)
      (fun other same => by
        have values := congrArg Fin.val same
        rw [target_wire, firstWordBit_wire] at values
        simp only [Fin.val_rev] at values
        have otherBound := other.isLt
        split at values <;> omega) (blank width input)
    rw [firstWord_little_get, firstWord_little_get] at actual
    have tailZero : tail.getLsbD index = false :=
      BitVec.getLsbD_of_ge tail index (by omega)
    simpa only [step, blank, BitVec.getLsbD_zero, BitVec.getLsbD_setWidth, within,
      decide_true, Bool.true_and, tailZero] using actual

private lemma step_length (width : Nat) (positive : 0 < width.size) (tail : BitVec 3)
    (input : BitVec (width + 3)) :
    (step width positive tail (blank width input)).coefficientLength =
      BitVec.ofNat width.size 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  by_cases zero : index = 0
  · subst index
    have actual := Word.xorConstantStep_get_target (target width positive) (constant tail) 3
      (fun other different same => different (target_distinct width positive same))
      (blank width input)
    rw [target_blank, Bool.false_xor, target_length_get, constant_read] at actual
    simpa [step, BitVec.getLsbD_ofNat, positive] using actual
  · have actual := Word.xorConstantStep_get_observed_of_target_ne (target width positive)
      (constant tail) (coefficientLengthBit width (⟨index, within⟩ : Fin width.size).rev)
      (fun other same => by
        have values := congrArg Fin.val same
        rw [target_wire, coefficientLengthBit_wire] at values
        simp only [Fin.val_rev] at values
        have otherBound := other.isLt
        split at values <;> omega) (blank width input)
    rw [length_little_get, length_little_get] at actual
    have one : (1 : Nat).testBit index = false := by
      apply Nat.testBit_lt_two_pow
      exact (by decide : 1 < 2 ^ 1).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
    simpa only [step, blank, BitVec.getLsbD_zero, BitVec.getLsbD_ofNat, within,
      decide_true, Bool.true_and, one, Nat.zero_testBit] using actual

/-- The actual fixed native layer initializes the entire source from its zero workspace. -/
lemma step_blank (width : Nat) (positive : 0 < width.size) (tail : BitVec 3)
    (input : BitVec (width + 3)) :
    step width positive tail (blank width input) = source width tail input := by
  let result := step width positive tail (blank width input)
  calc
    result = { withoutSeed result with
      firstWord := result.firstWord
      coefficientLength := result.coefficientLength } := rfl
    _ = _ := by
      rw [step_complement, step_firstWord, step_length]
      rfl

/-- Every actually emitted fixed X gate remains charged as a native single-qubit event. -/
lemma program_eventTrace (width : Nat) (positive : 0 < width.size) (tail : BitVec 3) :
    (program width positive tail).eventTrace =
      List.replicate (Word.constantOneIndices (constant tail)).length (.gate .singleQubit) :=
  WindowLookup.wordXProgram_eventTrace (QubitLayout.canonical _) .empty _ _ _

/-- The distinct actual source positions have native dependency depth at most one. -/
lemma program_quantumTime_le (width : Nat) (positive : 0 < width.size) (tail : BitVec 3) :
    (program width positive tail).evaluatedEventDepth Resource.Event.quantumDuration ≤ 1 :=
  WindowLookup.wordXProgram_quantumTime_le (QubitLayout.canonical _) .empty _ _ _

/-- No more than the four independently identified existing source positions are charged. -/
lemma seed_count_le (tail : BitVec 3) :
    (Word.constantOneIndices (constant tail)).length ≤ 4 :=
  Word.constantOneIndices_length_le _

end

end QuantumAlg.MAU.Inversion.SharedEEA.ResidentSeed
