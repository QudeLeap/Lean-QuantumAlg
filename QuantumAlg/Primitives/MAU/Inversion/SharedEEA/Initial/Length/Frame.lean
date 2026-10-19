/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.Length.Write

/-!
# Complete shared-frame restoration by the actual initial length writer

The actual gate list computes the current Work2 payload length in the
existing divisor-length field [LYL+26, sec_EEA/sub_4phase.tex:108-117].
This owner makes its complete frame action explicit: every other field,
including the dirty Work1 used inside the leading-bit predicates, is
restored exactly. The arbitrary initial length is updated by xor, so the
statement does not erase any incoming information.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InitialLengthFrame

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit InitialLengthSemantics

private def withoutLength {width : Nat} (state : Registers width) : Registers width :=
  { state with divisorLength := 0#width.size }

private lemma withoutLength_flip (width : Nat) (bit : Fin width.size)
    (state : Registers width) :
    withoutLength ((divisorLengthBit width bit).flip state) = withoutLength state := rfl

private lemma xor_withoutLength (width : Nat) (value : Fin (2 ^ width.size))
    (state : Registers width) :
    withoutLength (Word.xorConstantStep (InitialLengthWrite.target width) value state) =
      withoutLength state := by
  rw [Word.xorConstantStep_eq_indicesStep]
  generalize Word.constantOneIndices value = indices
  induction indices generalizing state with
  | nil => rfl
  | cons bit rest ih =>
      change withoutLength (Word.xorConstantIndicesStep (InitialLengthWrite.target width) rest
        ((divisorLengthBit width bit.rev).flip state)) = withoutLength state
      rw [ih, withoutLength_flip]

/-- The same actual gate list changes only the divisor length by the exact current payload size. -/
lemma gates_step_eq (width : Nat) (state : Registers width) :
    GateSpec.stepList (InitialLengthWrite.gates width) state =
      { state with divisorLength :=
          state.divisorLength ^^^ BitVec.ofNat width.size (payloadValue state).size } := by
  let result := GateSpec.stepList (InitialLengthWrite.gates width) state
  have retained : withoutLength result = withoutLength state := by
    dsimp only [result]
    rw [InitialLengthWrite.gates_step]
    exact xor_withoutLength width _ state
  have written := InitialLengthWrite.gates_divisorLength width state
  change result.divisorLength = _ at written
  calc
    result = { withoutLength result with divisorLength := result.divisorLength } := rfl
    _ = _ := by
      rw [retained, written]
      rfl

/-- The actual native program has the complete record update as its exact basis action. -/
lemma program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (InitialLengthWrite.program width) environment
      (fun state => { state with divisorLength :=
        state.divisorLength ^^^ BitVec.ofNat width.size (payloadValue state).size }) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (gates_step_eq width) environment

end

end QuantumAlg.MAU.Inversion.SharedEEA.InitialLengthFrame
