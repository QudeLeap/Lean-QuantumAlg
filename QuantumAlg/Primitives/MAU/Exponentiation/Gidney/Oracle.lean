/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Copy
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Oracle

/-!
# Actual reversible modular exponentiation with an arbitrary XOR target

The circuit computes on two shared work words, applies the literal CNOT
copy, and executes the adjoint of the same computation. The arbitrary target
receives the modular power by XOR. Both work words return to their compiled
initial values, with exact phase and no reference-factorization assumption
[VBE95, 9511018.tex:372-416].
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open Nat.FixedWidth

private theorem bits_equiv_apply (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (bits : List (Fin exponentWidth)) (state : Registers exponentWidth width) :
    unitPowerBitsEquiv modulus base bits state = outputForBits modulus base bits state := by
  induction bits generalizing state with
  | nil => rfl
  | cons bit bits ih =>
      change unitPowerBitsEquiv modulus base bits (unitPowerStageEquiv modulus base bit state) =
        outputForBits modulus base bits (stageOutput modulus base bit state)
      rw [ih, unitPowerStageEquiv_apply]
      rfl

/-- Place the actual selected-power computation before the separate XOR target. -/
def forwardProgram (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit (Qubits (oracleEncoding exponentWidth width).width) :=
  UnitaryCircuit.prodLeft (n := width) (program exponentWidth width modulus base)

private theorem forward_realizes (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit.Realizes (oracleEncoding exponentWidth width)
      (forwardProgram exponentWidth width modulus base)
      (unitPowerForwardEquiv exponentWidth width modulus base) := by
  apply (UnitaryCircuit.Realizes.prodLeft (right := BinaryLabelEncoding.finIdentity width)
    (gidneyExponent_realizes exponentWidth width modulus base)).congrStep
  rintro ⟨state, target⟩
  exact congrArg (fun output => (output, target))
    (bits_equiv_apply exponentWidth width modulus base (List.ofFn fun bit => bit) state).symm

/-- The literal three-part computation before recording the complete existing carrier. -/
def oracleBody (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit (Qubits (oracleEncoding exponentWidth width).width) :=
  (forwardProgram exponentWidth width modulus base).seq
    ((copyProgram exponentWidth width).seq
      (forwardProgram exponentWidth width modulus base).dagger)

/-- Retain exactly the exponent, two work words, and original arbitrary target. -/
def oracleProgram (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit (Qubits (oracleEncoding exponentWidth width).width) :=
  (oracleBody exponentWidth width modulus base).seq
    (UnitaryCircuit.identity (Qubits (oracleEncoding exponentWidth width).width)
      (List.range (exponentWidth + 3 * width)) List.nodup_range)

/-- Exact total action is defined independently of the actual circuit and its adjoint. -/
theorem gidneyExponentOracle_realizes (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit.Realizes (oracleEncoding exponentWidth width)
      (oracleProgram exponentWidth width modulus base) (unitPowerOracleOutput modulus base) := by
  have forward := forward_realizes exponentWidth width modulus base
  have inverse := forward.dagger_of_rightInverse
    (Equiv.apply_symm_apply (unitPowerForwardEquiv exponentWidth width modulus base))
  apply ((forward.seq ((gidneyExponentCopy_realizes exponentWidth width).seq inverse)).seq
    (UnitaryCircuit.Realizes.identityAt (oracleEncoding exponentWidth width)
      (List.range (exponentWidth + 3 * width)) List.nodup_range)).congrStep
  intro state
  rfl

/-- The arbitrary target receives the power by XOR and both work words are returned exactly. -/
theorem gidneyExponentOracle_clean (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (exponent : Fin (2 ^ exponentWidth))
    (target : Fin (2 ^ width)) :
    (oracleProgram exponentWidth width modulus base).applyNormalized
        (NormalizedVector.ket ((oracleEncoding exponentWidth width).encode
          ((exponent, unitResidueWord modulus positive 1, 0), target))) =
      NormalizedVector.ket ((oracleEncoding exponentWidth width).encode
        ((exponent, unitResidueWord modulus positive 1, 0),
          ⟨target.val ^^^ (unitResidueWord modulus positive (base ^ exponent.val)).val,
            Nat.xor_lt_two_pow target.isLt
              (unitResidueWord modulus positive (base ^ exponent.val)).isLt⟩)) := by
  let initial : Registers exponentWidth width :=
    (exponent, unitResidueWord modulus positive 1, 0)
  let computed : Registers exponentWidth width :=
    (exponent, unitResidueWord modulus positive (base ^ exponent.val), 0)
  let toggled : Fin (2 ^ width) :=
    ⟨target.val ^^^ computed.2.1.val, Nat.xor_lt_two_pow target.isLt computed.2.1.isLt⟩
  have forward (value : Fin (2 ^ width)) :
      (forwardProgram exponentWidth width modulus base).applyNormalized
          (NormalizedVector.ket ((oracleEncoding exponentWidth width).encode (initial, value))) =
        NormalizedVector.ket ((oracleEncoding exponentWidth width).encode (computed, value)) :=
    UnitaryCircuit.Realizes.prodLeft_applyNormalized_encoded_ket_of_eq
      (encoding exponentWidth width) (BinaryLabelEncoding.finIdentity width)
      (program exponentWidth width modulus base) initial computed value
      (gidneyExponent_clean exponentWidth width modulus positive base exponent)
  have copied :
      (copyProgram exponentWidth width).applyNormalized
          (NormalizedVector.ket ((oracleEncoding exponentWidth width).encode (computed, target))) =
        NormalizedVector.ket ((oracleEncoding exponentWidth width).encode (computed, toggled)) :=
    (gidneyExponentCopy_realizes exponentWidth width).apply_encoded_ket (computed, target)
  have restored :
      (forwardProgram exponentWidth width modulus base).dagger.applyNormalized
          (NormalizedVector.ket ((oracleEncoding exponentWidth width).encode (computed, toggled))) =
        NormalizedVector.ket ((oracleEncoding exponentWidth width).encode (initial, toggled)) :=
    (congrArg (forwardProgram exponentWidth width modulus base).dagger.applyNormalized
      (forward toggled)).symm.trans
        (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
          (forwardProgram exponentWidth width modulus base)
          (NormalizedVector.ket ((oracleEncoding exponentWidth width).encode (initial, toggled))))
  have body := UnitaryCircuit.applyNormalized_seq_of_eq (forward target)
    (UnitaryCircuit.applyNormalized_seq_of_eq copied restored)
  exact UnitaryCircuit.applyNormalized_seq_of_eq body
    (UnitaryCircuit.applyNormalized_identity (Qubits (oracleEncoding exponentWidth width).width)
      (List.range (exponentWidth + 3 * width)) List.nodup_range _)

end

end QuantumAlg.MAU.Exponentiation.Gidney
