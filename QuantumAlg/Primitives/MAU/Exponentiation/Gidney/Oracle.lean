/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Copy
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Oracle
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint
import all QuantumAlg.Components.Encoded.BitGates.Realization

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

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth

private lemma bits_equiv_apply (exponentWidth width : Nat)
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
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oracleEncoding exponentWidth width).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix width (program exponentWidth width modulus base)

private lemma forward_realizes (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit.Realizes (oracleEncoding exponentWidth width)
      (forwardProgram exponentWidth width modulus base) environment
      (unitPowerForwardEquiv exponentWidth width modulus base) := by
  apply (UnitaryCircuit.Realizes.onBinaryPrefix
    (right := BinaryLabelEncoding.finIdentity width)
    (gidneyExponent_realizes exponentWidth width modulus base)).congrStep
  rintro ⟨state, target⟩
  exact congrArg (fun output => (output, target))
    (bits_equiv_apply exponentWidth width modulus base (List.ofFn fun bit => bit) state).symm

/-- The literal three-part computation before recording the complete existing carrier. -/
def oracleBody (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oracleEncoding exponentWidth width).width).toQuantum :=
  (forwardProgram exponentWidth width modulus base).seq
    ((copyProgram exponentWidth width).seq
      ((forwardProgram exponentWidth width modulus base).dagger
        (AlgorithmGate.oracleFreeAdjoints .empty)))

/-- The complete exponent, two work words, and arbitrary target share one layout. -/
def oracleProgram (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oracleEncoding exponentWidth width).width).toQuantum :=
  oracleBody exponentWidth width modulus base

/-- Exact total action is defined independently of the actual circuit and its adjoint. -/
lemma gidneyExponentOracle_realizes (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit.Realizes (oracleEncoding exponentWidth width)
      (oracleProgram exponentWidth width modulus base)
      environment (unitPowerOracleOutput modulus base) := by
  have forward := forward_realizes (environment := environment) exponentWidth width modulus base
  have inverse : UnitaryCircuit.Realizes (oracleEncoding exponentWidth width)
      ((forwardProgram exponentWidth width modulus base).dagger
        (AlgorithmGate.oracleFreeAdjoints .empty)) environment
      (unitPowerForwardEquiv exponentWidth width modulus base).symm :=
    forward.dagger_of_rightInverse
      (by
        rw [UnitaryCircuit.dagger_matrix]
        rw [Subsingleton.elim
          ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment) environment]
        exact Unitary.star_eq_inv ((forwardProgram exponentWidth width modulus base).matrix
          environment))
      (Equiv.apply_symm_apply (unitPowerForwardEquiv exponentWidth width modulus base))
  apply (forward.seq ((gidneyExponentCopy_realizes exponentWidth width).seq inverse)).congrStep
  intro state
  rfl

/-- The arbitrary target receives the power by XOR and both work words are returned exactly. -/
lemma gidneyExponentOracle_clean (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (exponent : Fin (2 ^ exponentWidth))
    (target : Fin (2 ^ width)) :
    (oracleProgram exponentWidth width modulus base).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (oracleEncoding exponentWidth width).width).basisEquiv.symm
            ((oracleEncoding exponentWidth width).encode
              ((exponent, unitResidueWord modulus positive 1, 0), target)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (oracleEncoding exponentWidth width).width).basisEquiv.symm
          ((oracleEncoding exponentWidth width).encode
            ((exponent, unitResidueWord modulus positive 1, 0),
              ⟨target.val ^^^ (unitResidueWord modulus positive (base ^ exponent.val)).val,
                Nat.xor_lt_two_pow target.isLt
                  (unitResidueWord modulus positive (base ^ exponent.val)).isLt⟩))) := by
  rw [(gidneyExponentOracle_realizes exponentWidth width modulus base).apply_encoded_ket]
  rw [unitPowerOracleOutput_clean exponentWidth width modulus positive base exponent target]

end

end QuantumAlg.MAU.Exponentiation.Gidney
