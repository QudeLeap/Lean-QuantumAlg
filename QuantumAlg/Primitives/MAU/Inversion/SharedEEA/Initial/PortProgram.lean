/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Work1Constant
import all QuantumAlg.Util.NumberTheory.SharedEEA.Word.Unloading

/-!
# Actual initial constant load from the in-place division's clean large port

The in-place division initially supplies a zero large workspace and
keeps only the small auxiliary history for the inverse
[LYL+26, sec_point_add/sec_point_add.tex:45-79]. The source's initial
first word is `100,p` [LYL+26, sec_EEA/sub_4phase.tex:104-117].

This program uses actual fixed X gates to load its first n physical
positions from zero. Its final three positions and every other small
auxiliary field already have their fixed source initial values and are
retained. The input occupies exactly the last n Work2 positions and
does not select any gate or prepared value.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InitialPortProgram

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The source's full modulus-dependent initial Work1 value. -/
def initialWord (modulus : Nat) : BitVec (modulus.size + 3) :=
  BitVec.ofNat (modulus.size + 3) (4 * 2 ^ modulus.size + modulus)

/-- A fixed mask on the n large-workspace positions, with all three tail mask positions zero. -/
def mask (modulus : Nat) : BitVec (modulus.size + 3) :=
  WordUnloading.mainMask (PaddingClock.main (initialWord modulus))

private def constant (modulus : Nat) : Fin (2 ^ (modulus.size + 3)) :=
  BitVec.equivFin (mask modulus)

/-- Original input, zero main Work1, and exactly the remaining fixed source initialization. -/
def inputFrame (modulus : Nat) (input : Fin (2 ^ modulus.size)) : Registers modulus.size :=
  { InitialFrame.initial modulus input with
    firstWord := initialWord modulus ^^^ mask modulus }

/-- The supplied large port is zero on every one of its n actual physical positions. -/
theorem inputFrame_large_zero (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    PaddingClock.main (inputFrame modulus input).firstWord = 0#modulus.size :=
  (WordUnloading.unload_main (initialWord modulus)).1

/-- Each addressed large-workspace wire reads zero in the supplied input frame. -/
theorem inputFrame_large_bit (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (index : Fin modulus.size) :
    (inputFrame modulus input).firstWord.getMsbD index.val = false := by
  rw [WordUnloading.main_bit _ _ index.isLt, inputFrame_large_zero]
  exact BitVec.getMsbD_zero

/-- The high-clock positions and the final bit retain the original fixed source values. -/
theorem inputFrame_small_word (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    PaddingClock.high (inputFrame modulus input).firstWord =
        PaddingClock.high (initialWord modulus) ∧
      PaddingClock.last (inputFrame modulus input).firstWord =
        PaddingClock.last (initialWord modulus) :=
  (WordUnloading.unload_main (initialWord modulus)).2

/-- The actual input word is unchanged by the zero-workspace specification. -/
theorem inputFrame_input (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    (inputFrame modulus input).secondWord = (InitialFrame.initial modulus input).secondWord := rfl

/-- Execute the fixed constant-X load, using only the existing full frame. -/
def program (modulus : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding modulus.size).width).toQuantum :=
  Work1Constant.program modulus.size (constant modulus)

/-- The literal fixed X list reconstructs the complete source initial frame. -/
theorem gates_initial (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    GateSpec.stepList (Work1Constant.gates modulus.size (constant modulus))
        (inputFrame modulus input) = InitialFrame.initial modulus input := by
  rw [Work1Constant.gates_step]
  change { InitialFrame.initial modulus input with
    firstWord := (initialWord modulus ^^^ mask modulus) ^^^ mask modulus } = _
  rw [show (initialWord modulus ^^^ mask modulus) ^^^ mask modulus = initialWord modulus from
    WordUnloading.reload_main (initialWord modulus)]
  rfl

/-- Actual normalized amplitudes are preserved while loading A from zero, for every input label. -/
theorem program_initial (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    (program modulus).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
            ((encoding modulus.size).encode (inputFrame modulus input)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
          ((encoding modulus.size).encode (InitialFrame.initial modulus input))) := by
  exact (GateSpec.realizesList (QubitLayout.canonical _) .empty
    (Work1Constant.gates modulus.size (constant modulus))).apply_encoded_ket
      (inputFrame modulus input) |>.trans
        (congrArg (fun state => NormalizedVector.ket
          ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
            ((encoding modulus.size).encode state)))
          (gates_initial modulus input))

/-- Every literal initial X occurrence is charged, independently of the input value. -/
theorem program_resources (modulus : Nat) :
    (program modulus).eventCost.card ≤ modulus.size + 3 ∧
      (program modulus).evaluatedEventDepth (fun _ => 1) ≤ modulus.size + 3 := by
  have bound := Word.constantOneIndices_length_le (constant modulus)
  rw [program, Work1Constant.program, GateSpec.programList_eventCost_card,
    GateSpec.programList_evaluatedEventDepth_unit, Work1Constant.gates_length]
  exact ⟨bound, bound⟩

end

end QuantumAlg.MAU.Inversion.SharedEEA.InitialPortProgram
