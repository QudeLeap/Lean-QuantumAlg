/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.Length.Predicate
import all QuantumAlg.Util.NumberTheory.SharedEEA.LeadingBit

/-!
# Connect the actual leading-bit gates to the divisor's binary length

Work2 has three padding bits before its n-bit divisor payload
[LYL+26, sec_EEA/sub_4phase.tex:108-117]. The actual gate predicates ignore
those padding bits and test exactly the binary length of that payload.
The equality below applies to every complete encoded source-register value;
it assumes neither a classical input value nor clean conjunction work.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InitialLengthSemantics

noncomputable section

open EncodedBit InitialLengthPredicate

/-- The actual low-n-bit divisor payload, independently of Work2's three high padding bits. -/
def payloadValue {width : Nat} (state : Registers width) : Nat :=
  state.secondWord.toNat % 2 ^ width

lemma payloadValue_fits {width : Nat} (state : Registers width) :
    payloadValue state < 2 ^ width := Nat.mod_lt _ (Nat.two_pow_pos width)

/-- The physical payload lens agrees with the corresponding bit of its exact finite value. -/
lemma payloadBit_testBit (width : Nat) (index : Fin width) (state : Registers width) :
    (payloadBit width index).get state =
      (payloadValue state).testBit (width - 1 - index.val) := by
  rw [payloadBit_get]
  have indexBound := index.isLt
  have physicalBound : 3 + index.val < width + 3 := by omega
  have reverseBound : width - 1 - index.val < width := by omega
  have reversed : width + 3 - 1 - (3 + index.val) = width - 1 - index.val := by omega
  simp only [BitVec.getMsbD_eq_getLsbD, physicalBound, decide_true, Bool.true_and,
    BitVec.getLsbD, reversed, payloadValue, Nat.testBit_mod_two_pow, reverseBound]

/-- The actual native leading-one condition selects precisely the current divisor's bit length. -/
lemma firstOne_iff_size (width : Nat) (index : Fin width) (state : Registers width) :
    firstOne width index state ↔ (payloadValue state).size = width - index.val := by
  trans QuantumAlg.NumberTheory.SharedEEA.LeadingBit.selected width (payloadValue state) index
  · simp only [firstOne, zeroPrefix, QuantumAlg.NumberTheory.SharedEEA.LeadingBit.selected,
      payloadBit_testBit]
  · exact QuantumAlg.NumberTheory.SharedEEA.LeadingBit.selected_iff_size width (payloadValue state)
      (payloadValue_fits state) index

/-- The exact complete-register action now refers to an arithmetic size, not a free predicate. -/
lemma firstOneGates_step_size (width : Nat) (index : Fin width) (output : Fin width.size)
    (state : Registers width) :
    GateSpec.stepList (firstOneGates width index output) state =
      if (payloadValue state).size = width - index.val
      then (divisorLengthBit width output).flip state else state := by
  rw [firstOneGates_step]
  simp only [firstOne_iff_size]

/-- Length output flips retain the payload, so every later predicate reads the same input. -/
lemma payloadValue_flip (width : Nat) (output : Fin width.size) (state : Registers width) :
    payloadValue ((divisorLengthBit width output).flip state) = payloadValue state := rfl

/-- No position is selected when the current payload is zero, including all available widths. -/
lemma firstOneGates_step_zero (width : Nat) (index : Fin width) (output : Fin width.size)
    (state : Registers width) (zero : payloadValue state = 0) :
    GateSpec.stepList (firstOneGates width index output) state = state := by
  rw [firstOneGates_step_size]
  have indexBound := index.isLt
  have different : (payloadValue state).size ≠ width - index.val := by
    rw [zero, Nat.size_zero]
    omega
  exact if_neg different

end

end QuantumAlg.MAU.Inversion.SharedEEA.InitialLengthSemantics
