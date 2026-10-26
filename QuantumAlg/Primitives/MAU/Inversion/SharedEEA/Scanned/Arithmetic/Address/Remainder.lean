/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Constant
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Subtraction

/-!
# Paid remainder length-minus-one address with separate conjunction

The actual load and three actual native inverse adders prepare the
ordered streaming address. No high arithmetic carry occupies conjunction
during the body. The complete modular equation also covers inactive
finite metadata, rather than assigning them a truncated natural window
[LYL+26, sec_EEA/sub_regshare.tex:278,291-298].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The actual address stores length minus one; its public constant is physical width minus two. -/
def remainderConstant (width : Nat) : BitVec (ScanMetadata.addressWidth width) :=
  BitVec.ofNat (ScanMetadata.addressWidth width) (width + 3 - 2)

/-- One actual X load and three actual finite native subtractors execute in source order. -/
def remainderProgram (width : Nat) (positive : 1 ≤ width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  .seq (constantProgram width (remainderConstant width))
    (.seq (subtractProgram width positive .coefficient)
      (.seq (subtractProgram width positive .quotient) (subtractProgram width positive .shift)))

/-- Full-frame action of that same executed address preparation. -/
def remainderStep (width : Nat) (positive : 1 ≤ width) (state : Data width) : Data width :=
  subtractStep width positive .shift (subtractStep width positive .quotient
    (subtractStep width positive .coefficient
      (constantStep width (remainderConstant width) state)))

/-- Complete coherent semantics retain all original source and complementary quantum systems. -/
lemma remainderProgram_realizes (width : Nat) (positive : 1 ≤ width)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (remainderProgram width positive) environment
      (remainderStep width positive) := by
  unfold remainderProgram remainderStep
  have tail := UnitaryCircuit.Realizes.seq
    (subtractProgram_realizes width positive .quotient environment)
    (subtractProgram_realizes width positive .shift environment)
  have body := UnitaryCircuit.Realizes.seq
    (subtractProgram_realizes width positive .coefficient environment) tail
  have complete := UnitaryCircuit.Realizes.seq
    (constantProgram_realizes width (remainderConstant width) environment) body
  exact complete

/-- Original source fields retain their complete finite values. -/
lemma remainderStep_source (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    (remainderStep width positive state).1 = state.1 := by
  simp only [remainderStep, subtractStep_source, constantStep_source]

/-- Conjunction and every prefix keep their original values during actual address preparation. -/
lemma remainderStep_workspace (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    (remainderStep width positive state).2.2 = state.2.2 := by
  simp only [remainderStep, subtractStep_workspace, constantStep_workspace]

/-- The actual address obeys the complete finite modular equation with its real padding. -/
lemma remainderStep_address (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    (remainderStep width positive state).2.1 =
      (state.2.1 ^^^ remainderConstant width) - sourceValue width positive .coefficient state -
        sourceValue width positive .quotient state - sourceValue width positive .shift state := by
  simp only [remainderStep, subtractStep_address, constantStep_address, sourceValue,
    prefixBit_get, ArithmeticGeometry.fieldValue, subtractStep_source, constantStep_source,
    congrArg Prod.fst (subtractStep_workspace width positive .coefficient
      (constantStep width (remainderConstant width) state)),
    congrArg Prod.fst (subtractStep_workspace width positive .quotient
      (subtractStep width positive .coefficient
        (constantStep width (remainderConstant width) state))),
    congrArg Prod.fst (constantStep_workspace width (remainderConstant width) state)]

/-- A proved physical zero padding identifies the native operand with its complete metadata. -/
lemma sourceValue_toNat_of_prefix_zero (width : Nat) (positive : 1 ≤ width)
    (field : ArithmeticGeometry.Field) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    (sourceValue width positive field state).toNat =
      (ArithmeticGeometry.fieldValue field state).toNat := by
  simp [sourceValue, prefixBit_get, clean]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress
