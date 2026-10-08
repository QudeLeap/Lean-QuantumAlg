/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Schedule
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ClockDecode

/-!
# Complete actual fixed schedule followed by the real clock decoder

The fixed forward program and the actual bit-controlled inverse rotations
recover the complete terminal Work2 while keeping all other forward
history, including the reused high clock bits and Iter
[LYL+26, sec_EEA/sub_4phase.tex:105,121-128]. Each physical Work2 wire then
contains its original little-endian terminal coefficient bit.

The following exact normalized-ket equation is for that composed native
circuit. Conditional coefficient correction, copying the inverse to its
output register, and reversing the forward circuit remain separate
actual operations. No retained field is silently reset or omitted.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.DecodedSchedule

noncomputable section

open NumberTheory.SharedEEA

/-- Actual independent forward schedule followed by every native weighted decoder sweep. -/
def program (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding modulus.size).width).toQuantum :=
  (NativeSchedule.program modulus nontrivial).seq (ClockDecode.program modulus.size)

/-- Mathematical final physical frame retains the complete recorded clock while unrotating Work2. -/
def result (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus) :
    Registers modulus.size :=
  let terminal := NativeSchedule.terminalFrame modulus input positive bounded
  { TerminalPosition.frame terminal (QuotientSchedule.padding modulus input) with
    secondWord := terminal.secondWord }

/-- Actual preprocessing, fixed repetition, and real decoder produce this entire original frame. -/
theorem program_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    (program modulus nontrivial).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
            ((encoding modulus.size).encode (InitialFrame.initial modulus input)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
          ((encoding modulus.size).encode (result modulus input.val positive bounded))) := by
  have within : QuotientSchedule.padding modulus input.val < 2 ^ (2 + modulus.size.size) := by
    simpa only [Nat.add_comm] using
      QuotientSchedule.padding_fits_extended_clock modulus input.val coprime positive bounded
  rw [program, UnitaryCircuit.applyNormalized_seq,
    NativeSchedule.program_initial modulus nontrivial input coprime positive bounded,
    (ClockDecode.program_realizes modulus.size).apply_encoded_ket,
    TerminalPosition.decode_word
      (NativeSchedule.terminalFrame modulus input.val positive bounded)
      (QuotientSchedule.padding modulus input.val) within]
  rfl

/-- Every decoded Work2 coordinate is exactly the terminal coefficient's little-endian bit. -/
theorem result_coefficient_bit (modulus input index : Nat)
    (positive : 0 < input) (bounded : input < modulus) (within : index < modulus.size + 3) :
    (result modulus input positive bounded).secondWord.getMsbD index =
      (TerminalPadding.finalState modulus input).previousCoefficient.testBit index := by
  let state := TerminalPadding.finalState modulus input
  let valid := TerminalPadding.final_admissible modulus input positive bounded
  let conserved := TerminalPadding.final_balance modulus input
  let payload := DivisionCapacity.work2Payload state modulus valid conserved
  have physicalWidth := DivisionCapacity.work2_width state modulus valid conserved
  have coefficient : payload.coefficientBits.toNat = state.previousCoefficient := rfl
  have remainder : payload.remainderBits.toNat = state.divisor := rfl
  have finished : state.divisor = 0 := TerminalPadding.final_divisor modulus input positive bounded
  change ((WordPacking.packWork2 payload).cast physicalWidth).getMsbD index = _
  rw [BitVec.getMsbD_cast, PackingBoundary.work2_bit payload index (by
    rw [physicalWidth]
    exact within), coefficient, remainder, finished, Nat.zero_testBit, Bool.or_false]

/-- The retained iteration bit is the exact original-fold and macro-exchange history. -/
theorem result_iteration (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus) :
    (result modulus input positive bounded).flags.iteration =
      SignedTrajectory.finalIteration modulus input := rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.DecodedSchedule
