/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Constant
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Subtraction

/-!
# Actual full-carry remainder-window geometry

A real public constant load and three native placed subtractions compute
the geometry in the complete existing temporary target. The original
source words and metadata are retained. Dirty padding is included in the
all-label word equation; callers must prove the actual zero padding when
identifying the word with a natural source length
[LYL+26, sec_EEA/sub_regshare.tex:278,291-298].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The full mathematical remainder offset is public and loaded through native X gates. -/
def remainderConstant (width : Nat) : BitVec (fullWidth width) :=
  BitVec.ofNat (fullWidth width) (width + 3 - 1)

/-- The actual fixed native sequence contains all three complete finite metadata subtractions. -/
def remainderProgram (width : Nat) (positive : 1 ≤ width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  .seq (constantProgram width (remainderConstant width))
    (.seq (subtractProgram width positive .coefficient)
      (.seq (subtractProgram width positive .quotient) (subtractProgram width positive .shift)))

/-- The complete physical-frame action of that same actual native sequence. -/
def remainderStep (width : Nat) (positive : 1 ≤ width) (state : Data width) : Data width :=
  subtractStep width positive .shift (subtractStep width positive .quotient
    (subtractStep width positive .coefficient
      (constantStep width (remainderConstant width) state)))

/-- Complete coherent semantics follow from the actual constant and unitary arithmetic bodies. -/
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

/-- Original words, every complete metadata field, both phase bits, Sign and dirty Iter survive. -/
lemma remainderStep_source (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    (remainderStep width positive state).1 = state.1 := by
  simp only [remainderStep, subtractStep_source, constantStep_source]

/-- Both real padding bits and the entire actual prefix retain their original values. -/
lemma remainderStep_prefix (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    (remainderStep width positive state).2.2.1 = state.2.2.1 := by
  simp only [remainderStep, subtractStep_prefix, constantStep_prefix]

/-- The actual complete target obeys the full modular equation on every finite input. -/
lemma remainderStep_targetValue (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    targetValue width (remainderStep width positive state) =
      (targetValue width state ^^^ remainderConstant width) -
        sourceValue width positive .coefficient state -
        sourceValue width positive .quotient state - sourceValue width positive .shift state := by
  simp only [remainderStep, subtractStep_targetValue, constantStep_targetValue,
    sourceValue, prefixBit_get, subtractStep_prefix, constantStep_prefix,
    fieldValue, subtractStep_source, constantStep_source]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry
