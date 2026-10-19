/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Controlled
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Exponentiation

/-!
# One coherent selected-power stage with shared multiplication storage

The addressed exponent bit controls the actual two-word multiplier. The
exponent word and multiplication words are the complete physical carrier;
no additional control or helper bit is introduced. Every canonical power
word and zero auxiliary word is transformed to the selected product and the
same zero auxiliary word. The unrestricted action remains an exact total
permutation, so coherence is preserved [VBE95, 9511018.tex:372-416].
For larger words, the source selector and exponent bit control only the
BCBC comparisons [G17, paper.tex:276-293,319-334].
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open QuantumAlg.Nat.FixedWidth.UnitExponentiation Nat.FixedWidth
open EncodedBit GateSpec

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

lemma gidneyExponentBit_get (exponentWidth : Nat) (bit : Fin exponentWidth)
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


/-- Control the literal multiplier gates using only the exponent and existing word wires. -/
def stageGates (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth) :
    List (GateSpec (BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity exponentWidth)
      (Multiplication.Accumulate.Gidney.encoding width))) :=
  Multiplication.Gidney.controlledGates exponentWidth width bit modulus (stageUnit base bit)

/-- Both control branches retain the complete exponent and the multiplier's joint action. -/
lemma gidneyExponentStageGates_step (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (bit : Fin exponentWidth) (state : Registers exponentWidth width) :
    stepList (stageGates exponentWidth width modulus base bit) state =
      stageOutput modulus base bit state :=
  Multiplication.Gidney.gidneyControlledUnitMultiplicationGates_step
    exponentWidth width bit modulus (stageUnit base bit) state

/-- Zero-, one-, and two-bit stages retain the original complete control expansion. -/
lemma gidneyExponentStageGates_small (exponentWidth width : Nat) (small : width ≤ 2)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth) :
    stageGates exponentWidth width modulus base bit =
      Multiplication.Accumulate.Gidney.ControlPushdown.originalControlled
        exponentWidth width bit (Multiplication.Gidney.gates width modulus (stageUnit base bit)) :=
  Multiplication.Gidney.gidneyControlledUnitMultiplication_small
    exponentWidth width small bit modulus (stageUnit base bit)

/-- Actual native selected-power stage on the original exponent and two-word carrier. -/
def stageProgram (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding exponentWidth width).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (stageGates exponentWidth width modulus base bit)

/-- Exact all-label action includes both selected and unselected coherent branches. -/
lemma gidneyExponentStage_realizes (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth) :
    UnitaryCircuit.Realizes (encoding exponentWidth width)
      (stageProgram exponentWidth width modulus base bit)
      environment (stageOutput modulus base bit) :=
  realizesList_congrStep (environment := environment) _ _ _
    (gidneyExponentStageGates_step exponentWidth width modulus base bit)

/-- Each canonical selected stage restores the same zero auxiliary word exactly. -/
lemma gidneyExponentStage_clean (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth)
    (exponent : Fin (2 ^ exponentWidth)) (power : Fin (2 ^ width))
    (valid : power.val < modulus.val) :
    (stageProgram exponentWidth width modulus base bit).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding exponentWidth width).width).basisEquiv.symm
            ((encoding exponentWidth width).encode (exponent, power, 0)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding exponentWidth width).width).basisEquiv.symm
          ((encoding exponentWidth width).encode
            (exponent, if exponent.val.testBit bit.val then
              unitProductWord modulus positive (stageUnit base bit) power else power, 0))) := by
  rw [(gidneyExponentStage_realizes exponentWidth width modulus base bit).apply_encoded_ket]
  apply congrArg NormalizedVector.ket
  apply congrArg (QubitLayout.canonical (encoding exponentWidth width).width).basisEquiv.symm
  apply congrArg (encoding exponentWidth width).encode
  unfold stageOutput
  cases selected : exponent.val.testBit bit.val
  · simp only [Bool.false_eq_true, if_false]
  · simp only [if_true,
      unitMultiplicationPairEquiv_clean modulus positive (stageUnit base bit) power valid]

/-- The complete source layout has the exponent and the original two words. -/
lemma gidneyExponentStage_interface (exponentWidth width : Nat) :
    (encoding exponentWidth width).width = exponentWidth + 2 * width ∧
      (QubitLayout.canonical (encoding exponentWidth width).width).systemIdx =
        List.range (exponentWidth + 2 * width) := by
  constructor
  · change exponentWidth + (width + width) = exponentWidth + 2 * width
    omega
  · rw [(show (encoding exponentWidth width).width = exponentWidth + 2 * width from
        by change exponentWidth + (width + width) = _; omega)]
    exact QubitLayout.canonical_systemIdx _

end

end QuantumAlg.MAU.Exponentiation.Gidney
