/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ClockDecode.Weight
import all QuantumAlg.Util.NumberTheory.SharedEEA.Word.Rotation.Right
import all QuantumAlg.Components.Encoded.BitGates.IterationLaws

/-!
# Actual complete-clock inverse rotation with no additional wire

Each original clock bit controls its actual three-Toffoli adjacent-swap
sweep. The sweep is repeated by that bit's fixed binary weight; the
complete physical clock is never supplied as a scalar gate parameter.
The resulting native sequence rotates all of Work2 right by the exact
retained displacement, including its two reused high positions
[LYL+26, sec_EEA/sub_4phase.tex:105,121-128].

Every other physical field, including the complete clock itself, is
retained for subsequent inverse computation. The construction admits
arbitrary original clock, word, phase, and Ctrl values. It uses only the
already proved actual controlled adjacent swaps and symbolic repetition;
no additional quantum system or dirty-work initialization is introduced.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ClockDecode

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open NumberTheory.SharedEEA EncodedBit PredicateLayout

private def rotateFrame {width : Nat} (state : Registers width) (count : Nat) : Registers width :=
  { state with secondWord := state.secondWord.rotateRight count }

private lemma rotateFrame_zero {width : Nat} (state : Registers width) :
    rotateFrame state 0 = state := by
  rw [rotateFrame, WordRotationRight.rotateRight_zero]

private lemma rotateFrame_comp {width : Nat} (state : Registers width) (first second : Nat) :
    rotateFrame (rotateFrame state first) second = rotateFrame state (first + second) := by
  dsimp only [rotateFrame]
  rw [WordRotationRight.rotateRight_comp]

private lemma control_rotateFrame (width : Nat) (index : Fin (width.size + 2))
    (state : Registers width) (count : Nat) :
    (clockBit width index).get (rotateFrame state count) = (clockBit width index).get state :=
  ClockDecodeBit.control_setWord width index _ state

private def bitStep (width : Nat) (index : Fin (width.size + 2)) (state : Registers width) :
    Registers width :=
  if (clockBit width index).get state then rotateFrame state 1 else state

private lemma bit_iterate (width : Nat) (index : Fin (width.size + 2))
    (count : Nat) (state : Registers width) :
    (bitStep width index)^[count] state =
      rotateFrame state (((clockBit width index).get state).toNat * count) := by
  induction count with
  | zero =>
      rw [Nat.mul_zero]
      exact (rotateFrame_zero state).symm
  | succ count inductionHypothesis =>
      rw [Function.iterate_succ_apply', inductionHypothesis]
      change (if (clockBit width index).get (rotateFrame state
        (((clockBit width index).get state).toNat * count)) then
          rotateFrame (rotateFrame state (((clockBit width index).get state).toNat * count)) 1
        else rotateFrame state (((clockBit width index).get state).toNat * count)) = _
      rw [control_rotateFrame]
      cases selected : (clockBit width index).get state with
      | false => simp only [Bool.false_eq_true, if_false, Bool.toNat_false, Nat.zero_mul]
      | true =>
          simp only [if_true, Bool.toNat_true, Nat.one_mul]
          exact rotateFrame_comp state count 1

/-- Fixed repetition of the existing real single-clock-bit decoder sweep. -/
def bitProgram (width : Nat) (index : Fin (width.size + 2)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  UnitaryCircuit.iterate (ClockDecodeWeight.weight width index) (ClockDecodeBit.program width index)

private lemma bit_realizes (width : Nat) (index : Fin (width.size + 2)) :
    UnitaryCircuit.Realizes (encoding width) (bitProgram width index) environment
      (fun state => rotateFrame state
        (((clockBit width index).get state).toNat * ClockDecodeWeight.weight width index)) :=
  ((ClockDecodeBit.program_realizes width index).iterate
    (ClockDecodeWeight.weight width index)).congrStep
      (bit_iterate width index (ClockDecodeWeight.weight width index))

private def sequence (width : Nat) : List (Fin (width.size + 2)) →
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum
  | [] => GateSpec.programList (QubitLayout.canonical _) .empty []
  | index :: rest => (bitProgram width index).seq (sequence width rest)

private lemma sequence_realizes (width : Nat) (indices : List (Fin (width.size + 2))) :
    UnitaryCircuit.Realizes (encoding width) (sequence width indices) environment
      (fun state => rotateFrame state
        ((indices.map fun index =>
          ((clockBit width index).get state).toNat *
            ClockDecodeWeight.weight width index).sum)) := by
  induction indices with
  | nil =>
      exact (GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty [] (fun state =>
        (rotateFrame_zero state).symm) environment)
  | cons index rest inductionHypothesis =>
      apply ((bit_realizes width index).seq inductionHypothesis).congrStep
      intro state
      let count := ((clockBit width index).get state).toNat * ClockDecodeWeight.weight width index
      have retained : (rest.map fun position =>
          ((clockBit width position).get (rotateFrame state count)).toNat *
            ClockDecodeWeight.weight width position) =
          rest.map (fun position => ((clockBit width position).get state).toNat *
            ClockDecodeWeight.weight width position) := by
        apply List.map_congr_left
        intro position _
        rw [control_rotateFrame]
      change rotateFrame (rotateFrame state count) _ = _
      rw [retained, rotateFrame_comp]
      rfl

/-- Execute the actual fixed weighted sweeps over all original high and low clock wires. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  sequence width (List.finRange (width.size + 2))

/-- Actual native execution decodes the complete physical clock and preserves every other bit. -/
lemma program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width) environment
      (fun state => { state with
        secondWord :=
          state.secondWord.rotateRight (ExtendedClockRegisters.clock state).toNat }) := by
  apply (sequence_realizes width (List.finRange (width.size + 2))).congrStep
  intro state
  have total : ((List.finRange (width.size + 2)).map fun index =>
      ((clockBit width index).get state).toNat * ClockDecodeWeight.weight width index).sum =
        (ExtendedClockRegisters.clock state).toNat := by
    rw [← Fin.sum_univ_def]
    exact ClockDecodeWeight.selected_sum width state
  exact congrArg (rotateFrame state) total

end

end QuantumAlg.MAU.Inversion.SharedEEA.ClockDecode
