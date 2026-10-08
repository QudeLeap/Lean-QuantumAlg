/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Subtraction
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-!
# Literal word complement for the HRS borrowed incrementer

The borrowed word is the left TTK operand; the target word is the right
operand. One X gate per borrowed bit implements the finite complement
`2^n - 1 - g`, including the empty word. This is the complement operation
in the HRS incrementer identity [HRS16, paper.tex:219-224].
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

open EncodedBit.GateSpec

/-- Finite complement, with no sign convention or infinite leading bits. -/
def complementWord {n : Nat} (word : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨2 ^ n - (word.val + 1), by have := Nat.two_pow_pos n; omega⟩

/-- Complement the borrowed operand and preserve the target operand. -/
def complementOutput {n : Nat} (state : TTK.Registers n) : TTK.Registers n :=
  (complementWord state.1, state.2)

/-- Literal X gates on all borrowed-word wires, in increasing bit order. -/
def complementGates (n : Nat) : List (EncodedBit.GateSpec (TTK.encoding n)) :=
  List.ofFn fun bit : Fin n => .x (TTK.leftBit n bit)

/-- Compile the actual complement list on the two-word interface. -/
def complementProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (TTK.encoding n).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (complementGates n)

/-- Complemented representatives sum to one less than the modulus. -/
theorem hrsComplementWord_sum (n : Nat) (word : Fin (2 ^ n)) :
    word.val + (complementWord word).val + 1 = 2 ^ n := by
  change word.val + (2 ^ n - (word.val + 1)) + 1 = 2 ^ n
  have := word.isLt
  omega

/-- The finite complement restores every word when applied twice. -/
theorem hrsComplementWord_involutive (n : Nat) (word : Fin (2 ^ n)) :
    complementWord (complementWord word) = word := by
  apply Fin.ext
  have h := hrsComplementWord_sum n word
  have h' := hrsComplementWord_sum n (complementWord word)
  omega

/-- Every in-range bit is inverted. -/
theorem hrsComplementWord_testBit (n : Nat) (word : Fin (2 ^ n)) (bit : Fin n) :
    (complementWord word).val.testBit bit.val = !word.val.testBit bit.val := by
  simp only [complementWord, Nat.testBit_two_pow_sub_succ word.isLt,
    decide_eq_true bit.isLt, Bool.true_and]

private def borrowedWord (n : Nat) : EncodedBit.Word (TTK.encoding n) n :=
  ⟨TTK.leftBit n⟩

private def allOnes (n : Nat) : Fin (2 ^ n) :=
  ⟨2 ^ n - 1, by have := Nat.two_pow_pos n; omega⟩

private theorem allOnes_testBit (n : Nat) (bit : Fin n) :
    (allOnes n).val.testBit bit.val = true := by
  simp [allOnes, bit.isLt]

private theorem complementGates_eq_xorConstant (n : Nat) :
    complementGates n =
      EncodedBit.Word.xorConstantGates (borrowedWord n) (allOnes n) := by
  have hbits : (fun bit : Fin n => (allOnes n).val.testBit bit.val) =
      fun _ => true := by
    funext bit
    exact allOnes_testBit n bit
  simp only [EncodedBit.Word.xorConstantGates, EncodedBit.Word.constantOneIndices, hbits]
  simp [complementGates, borrowedWord, Function.comp_def]

/-- The actual X list has the finite complement action on all input words. -/
theorem hrsComplement_step (n : Nat) (state : TTK.Registers n) :
    stepList (complementGates n) state = complementOutput state := by
  rw [complementGates_eq_xorConstant]
  change EncodedBit.Word.xorConstantStep (borrowedWord n) (allOnes n) state = _
  apply Prod.ext
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    have h := EncodedBit.Word.xorConstantStep_get_target
      (borrowedWord n) (allOnes n) bit
      (fun other hne => TTK.ttkLeftLeft_disjoint n other bit hne) state
    change (TTK.leftBit n bit).get _ =
      ((TTK.leftBit n bit).get state ^^ (allOnes n).val.testBit bit.val) at h
    rw [TTK.ttkLeftBit_get, TTK.ttkLeftBit_get, allOnes_testBit] at h
    simpa only [complementOutput, hrsComplementWord_testBit, Bool.xor_true] using h
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    have h := EncodedBit.Word.xorConstantStep_get_observed_of_target_ne
      (borrowedWord n) (allOnes n) (TTK.rightBit n bit)
      (fun other => TTK.ttkLeftRight_disjoint n other bit) state
    simpa only [TTK.ttkRightBit_get, complementOutput] using h

/-- Exact amplitudes, without a phase allowance or borrowed-word restriction. -/
theorem hrsComplement_realizes (n : Nat) :
    UnitaryCircuit.Realizes (TTK.encoding n) (complementProgram n) complementOutput :=
  realizesList_congrStep (QubitLayout.canonical _) .empty
    (complementGates n) (hrsComplement_step n)

/-- Every native event coordinate follows from the actual list of X gates. -/
theorem hrsComplement_native_count (n : Nat)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (complementProgram n).eventCost =
      n * (if (.gate .singleQubit :
        Resource.Event (.quantum AlgorithmGate.model .empty)) = focus then 1 else 0) := by
  rw [complementProgram, programList_event_count_eq_sum_eventMultiplicity]
  have nativeX (bit : Fin n) :
      event .empty (.x (TTK.leftBit n bit)) =
        (.gate .singleQubit :
          Resource.Event (.quantum AlgorithmGate.model .empty)) := rfl
  by_cases h : (.gate .singleQubit :
      Resource.Event (.quantum AlgorithmGate.model .empty)) = focus
  · simp [complementGates, eventMultiplicity, nativeX, List.sum_ofFn, h]
  · simp [complementGates, eventMultiplicity, nativeX, List.sum_ofFn, h]

/-- The serial list contains exactly one gate per borrowed bit. -/
theorem hrsComplement_serial_resources (n : Nat) :
    (complementProgram n).eventCost.card = n ∧
      (complementProgram n).evaluatedEventDepth (fun _ => 1) = n := by
  change (programList (QubitLayout.canonical _) .empty
      (complementGates n)).eventCost.card = n ∧
    (programList (QubitLayout.canonical _) .empty
      (complementGates n)).evaluatedEventDepth (fun _ => 1) = n
  rw [programList_eventCost_card, programList_evaluatedEventDepth_unit]
  simp [complementGates]

end

end QuantumAlg.MAU.Addition.HRS
