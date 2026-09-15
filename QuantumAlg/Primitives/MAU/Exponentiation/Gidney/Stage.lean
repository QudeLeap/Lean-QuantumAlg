/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Program
import all QuantumAlg.Components.Encoded.BitGates.Control
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Exponentiation

/-!
# One coherent selected-power stage with shared multiplication storage

The addressed exponent bit controls the actual two-word multiplier. The
exponent word and multiplication words are the complete physical carrier;
no additional control or helper bit is introduced. Every canonical power
word and zero auxiliary word is transformed to the selected product and the
same zero auxiliary word. The unrestricted action remains an exact total
permutation, so coherence is preserved [VBE95, 9511018.tex:372-416].
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open QuantumAlg.Nat.FixedWidth.UnitExponentiation Nat.FixedWidth

/-- The complete exponent, current power, and shared multiplication auxiliary words. -/
abbrev Registers (exponentWidth width : Nat) :=
  Fin (2 ^ exponentWidth) × Multiplication.Accumulate.Gidney.Registers width

/-- The binary layout contains exactly the exponent and two multiplication words. -/
def encoding (exponentWidth width : Nat) : BinaryLabelEncoding (Registers exponentWidth width) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity exponentWidth)
    (Multiplication.Accumulate.Gidney.encoding width)

/-- Address one exponent bit using the library's fixed little-endian wire convention. -/
def exponentBit (exponentWidth : Nat) (bit : Fin exponentWidth) :
    EncodedBit (BinaryLabelEncoding.finIdentity exponentWidth) :=
  BinaryLabelEncoding.finIdentityBit exponentWidth (WireAddress.littleEndianWire bit)

theorem gidneyExponentBit_get (exponentWidth : Nat) (bit : Fin exponentWidth)
    (exponent : Fin (2 ^ exponentWidth)) :
    (exponentBit exponentWidth bit).get exponent = exponent.val.testBit bit.val := by
  change exponent.val.testBit (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

/-- Independent total two-word action selected by the unchanged exponent bit. -/
def stageOutput {exponentWidth width : Nat} (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth)
    (state : Registers exponentWidth width) : Registers exponentWidth width :=
  (state.1, if state.1.val.testBit bit.val then
    unitMultiplicationPairEquiv modulus (stageUnit base bit) state.2 else state.2)

/-- Coherently control the actual multiplier without allocating a separate control bit. -/
def stageProgram (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth) :
    UnitaryCircuit (Qubits (encoding exponentWidth width).width) :=
  UnitaryCircuit.controlAtEncodedBit (exponentBit exponentWidth bit)
    (Multiplication.Gidney.program width modulus (stageUnit base bit))

/-- Exact all-label action includes both the selected and unselected coherent branches. -/
theorem gidneyExponentStage_realizes (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth) :
    UnitaryCircuit.Realizes (encoding exponentWidth width)
      (stageProgram exponentWidth width modulus base bit) (stageOutput modulus base bit) where
  apply_encoded_ket := by
    rintro ⟨exponent, state⟩
    have actual := UnitaryCircuit.controlAtEncodedBit_applyNormalized_of_eq
      (exponentBit exponentWidth bit) (Multiplication.Accumulate.Gidney.encoding width)
      (Multiplication.Gidney.program width modulus (stageUnit base bit))
      state (unitMultiplicationPairEquiv modulus (stageUnit base bit) state)
      ((Multiplication.Gidney.gidneyUnitMultiplication_realizes width modulus
        (stageUnit base bit)).apply_encoded_ket state) exponent
    rw [gidneyExponentBit_get] at actual
    exact actual

/-- Each canonical selected stage restores the same zero auxiliary word exactly. -/
theorem gidneyExponentStage_clean (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth)
    (exponent : Fin (2 ^ exponentWidth)) (power : Fin (2 ^ width))
    (valid : power.val < modulus.val) :
    (stageProgram exponentWidth width modulus base bit).applyNormalized
        (NormalizedVector.ket ((encoding exponentWidth width).encode (exponent, power, 0))) =
      NormalizedVector.ket ((encoding exponentWidth width).encode
        (exponent, if exponent.val.testBit bit.val then
          unitProductWord modulus positive (stageUnit base bit) power else power, 0)) := by
  rw [(gidneyExponentStage_realizes exponentWidth width modulus base bit).apply_encoded_ket]
  apply congrArg NormalizedVector.ket
  apply congrArg (encoding exponentWidth width).encode
  unfold stageOutput
  cases selected : exponent.val.testBit bit.val
  · simp only [Bool.false_eq_true, if_false]
  · simp only [if_true,
      unitMultiplicationPairEquiv_clean modulus positive (stageUnit base bit) power valid]

theorem gidneyExponentStage_physical_range (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth) :
    (stageProgram exponentWidth width modulus base bit).physical_idx ⊆
      List.range (exponentWidth + 2 * width) := by
  have body : (Multiplication.Gidney.program width modulus (stageUnit base bit)).physical_idx ⊆
      List.range (Multiplication.Accumulate.Gidney.encoding width).width := by
    rw [Multiplication.Gidney.gidneyUnitMultiplication_physical]
    change List.range (2 * width) ⊆ List.range (width + width)
    simpa only [Nat.two_mul] using (List.Subset.refl (List.range (width + width)))
  have placed := UnitaryCircuit.controlAtEncodedBit_physical_idx_subset_range
    (exponentBit exponentWidth bit)
    (Multiplication.Gidney.program width modulus (stageUnit base bit)) body
  have size : (BinaryLabelEncoding.finIdentity exponentWidth).width +
      (Multiplication.Accumulate.Gidney.encoding width).width = exponentWidth + 2 * width := by
    change exponentWidth + (width + width) = exponentWidth + 2 * width
    omega
  unfold stageProgram
  simpa only [size] using placed

end

end QuantumAlg.MAU.Exponentiation.Gidney
