/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Remainder.Natural
import all QuantumAlg.Util.NumberTheory.SharedEEA.Geometry.Coefficient

/-!
# Actual full-carry coefficient geometry for each fixed source phase

The phase-three native body loads one and adds the complete coefficient
field. The phase-four native body loads physical width and subtracts
complete divisor and shift. Both retain every original field and both
actual padding bits. The public phase argument selects fixed code;
coherent runtime selection must additionally execute native controls.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The constant is loaded by actual X instructions in the full temporary target. -/
def coefficientConstant (width : Nat) (deshift : Bool) : BitVec (fullWidth width) :=
  if deshift then BitVec.ofNat (fullWidth width) (width + 3) else 1

/-- The complete actual native sequence for the fixed phase-three or phase-four instruction. -/
def coefficientProgram (width : Nat) (positive : 1 ≤ width) (deshift : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (constantProgram width (coefficientConstant width deshift)).seq
    (if deshift then (subtractProgram width positive .divisor).seq
      (subtractProgram width positive .shift) else program width positive .coefficient)

/-- Independent complete finite word action of that same fixed actual sequence. -/
def coefficientStep (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (state : Data width) : Data width :=
  let loaded := constantStep width (coefficientConstant width deshift) state
  if deshift then subtractStep width positive .shift
    (subtractStep width positive .divisor loaded) else step width positive .coefficient loaded

/-- Actual coherent execution keeps the full source and all complementary physical systems. -/
lemma coefficientProgram_realizes (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (coefficientProgram width positive deshift)
      environment (coefficientStep width positive deshift) := by
  cases deshift with
  | false =>
      have complete := UnitaryCircuit.Realizes.seq
        (constantProgram_realizes width (coefficientConstant width false) environment)
        (program_realizes width positive .coefficient environment)
      exact complete
  | true =>
      have body := UnitaryCircuit.Realizes.seq
        (subtractProgram_realizes width positive .divisor environment)
        (subtractProgram_realizes width positive .shift environment)
      have complete := UnitaryCircuit.Realizes.seq
        (constantProgram_realizes width (coefficientConstant width true) environment) body
      exact complete

/-- All original operands, complete metadata, phase bits, Sign, Ctrl and Iter survive. -/
lemma coefficientStep_source (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (state : Data width) : (coefficientStep width positive deshift state).1 = state.1 := by
  cases deshift <;> simp only [coefficientStep, Bool.false_eq_true, if_false, if_true,
    step_source, subtractStep_source, constantStep_source]

/-- Both padding bits and every original prefix position retain their actual incoming values. -/
lemma coefficientStep_prefix (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (state : Data width) :
    (coefficientStep width positive deshift state).2.2.1 = state.2.2.1 := by
  cases deshift <;> simp only [coefficientStep, Bool.false_eq_true, if_false, if_true,
    step_prefix, subtractStep_prefix, constantStep_prefix]

/-- Every finite label obeys the same full modular geometry equation, including dirty padding. -/
lemma coefficientStep_targetValue (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (state : Data width) :
    targetValue width (coefficientStep width positive deshift state) =
      if deshift then (targetValue width state ^^^ coefficientConstant width true) -
        sourceValue width positive .divisor state - sourceValue width positive .shift state
      else sourceValue width positive .coefficient state +
        (targetValue width state ^^^ coefficientConstant width false) := by
  cases deshift <;> simp only [coefficientStep, Bool.false_eq_true, if_false, if_true,
    step_targetValue, subtractStep_targetValue, constantStep_targetValue,
    sourceValue, prefixBit_get, subtractStep_prefix, constantStep_prefix,
    fieldValue, subtractStep_source, constantStep_source]

/-- Actual clean padding and full target zero produce the exact mathematical coefficient word. -/
lemma coefficientStep_targetWord (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (state : Data width) (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : targetValue width state = 0#(fullWidth width)) :
    targetValue width (coefficientStep width positive deshift state) =
      ScanGeometry.coefficientWord deshift state.1.coefficientLength
        state.1.divisorLength state.1.shift := by
  rw [coefficientStep_targetValue, zero, BitVec.zero_xor, BitVec.zero_xor]
  cases deshift <;> simp only [Bool.false_eq_true, if_false, if_true,
    sourceValue_eq_extend width positive _ state clean,
    coefficientConstant, ScanGeometry.coefficientWord, fieldValue]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry
