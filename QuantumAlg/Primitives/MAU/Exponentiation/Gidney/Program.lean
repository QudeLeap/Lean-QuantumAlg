/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Stage
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Word

/-!
# Actual selected-power fold on shared multiplication storage

Every stage reuses the same two multiplication words. The induction proves
that the auxiliary word is zero at every stage boundary and the current
power is the canonical representative of the selected unit product. The
full increasing-bit schedule computes the complete modular power exactly.
The exponent is unchanged. No parity condition is used, and the initial
power is one modulo the modulus [VBE95, 9511018.tex:372-416].
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open QuantumAlg.Nat.FixedWidth.UnitExponentiation Nat.FixedWidth

/-- Execute a static list of addressed exponent stages in its actual order. -/
def programForBits (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    List (Fin exponentWidth) → UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding exponentWidth width).width).toQuantum
  | [] => UnitaryCircuit.identity AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding exponentWidth width).width).toQuantum
  | bit :: bits => (stageProgram exponentWidth width modulus base bit).seq
      (programForBits exponentWidth width modulus base bits)

/-- Total finite arithmetic action of a list of selected-power stages. -/
def outputForBits {exponentWidth width : Nat} (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    List (Fin exponentWidth) → Registers exponentWidth width → Registers exponentWidth width
  | [], state => state
  | bit :: bits, state => outputForBits modulus base bits (stageOutput modulus base bit state)

/-- The same literal stage sequence realizes its complete all-input arithmetic action. -/
lemma gidneyExponentBits_realizes (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (bits : List (Fin exponentWidth)) :
    UnitaryCircuit.Realizes (encoding exponentWidth width)
      (programForBits exponentWidth width modulus base bits)
      environment (outputForBits modulus base bits) := by
  induction bits with
  | nil =>
      exact UnitaryCircuit.Realizes.identityAt AlgorithmGate.model .empty
        (encoding exponentWidth width) (QubitLayout.canonical _) environment
  | cons bit bits ih =>
      exact (gidneyExponentStage_realizes exponentWidth width modulus base bit).seq ih

private lemma stage_unit_word (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base seed : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth)
    (exponent : Fin (2 ^ exponentWidth)) :
    (stageProgram exponentWidth width modulus base bit).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding exponentWidth width).width).basisEquiv.symm
            ((encoding exponentWidth width).encode
              (exponent, unitResidueWord modulus positive seed, 0)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding exponentWidth width).width).basisEquiv.symm
          ((encoding exponentWidth width).encode
            (exponent, unitResidueWord modulus positive
              (selectedUnit base exponent.val bit * seed), 0))) := by
  have actual := gidneyExponentStage_clean (environment := environment)
    exponentWidth width modulus positive base bit exponent
    (unitResidueWord modulus positive seed) (unitResidueWord_valid modulus positive seed)
  cases selected : exponent.val.testBit bit.val
  · simpa only [selectedUnit, selected, Bool.false_eq_true, if_false, one_mul] using actual
  · simpa only [selectedUnit, selected, if_true, unitProductWord_unitResidueWord] using actual

/-- The zero auxiliary word is returned at every boundary of an arbitrary static stage list. -/
lemma gidneyExponentBits_unit_word (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (bits : List (Fin exponentWidth))
    (exponent : Fin (2 ^ exponentWidth)) (seed : (ZMod modulus.val)ˣ) :
    (programForBits exponentWidth width modulus base bits).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding exponentWidth width).width).basisEquiv.symm
            ((encoding exponentWidth width).encode
              (exponent, unitResidueWord modulus positive seed, 0)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding exponentWidth width).width).basisEquiv.symm
          ((encoding exponentWidth width).encode
            (exponent, unitResidueWord modulus positive
              (scheduledUnit base exponent.val bits * seed), 0))) := by
  induction bits generalizing seed with
  | nil =>
      simpa [programForBits, scheduledUnit] using
        ((UnitaryCircuit.Realizes.identityAt AlgorithmGate.model .empty
          (encoding exponentWidth width) (QubitLayout.canonical _) environment).apply_encoded_ket
          (exponent, unitResidueWord modulus positive seed, 0))
  | cons bit bits ih =>
      have selected := stage_unit_word (environment := environment)
        exponentWidth width modulus positive base seed bit exponent
      have remaining := ih (selectedUnit base exponent.val bit * seed)
      have sameUnit : scheduledUnit base exponent.val bits *
          (selectedUnit base exponent.val bit * seed) =
            scheduledUnit base exponent.val (bit :: bits) * seed := by
        simp only [scheduledUnit, List.map_cons, List.prod_cons]
        ac_rfl
      have sameState := congrArg (fun unit : (ZMod modulus.val)ˣ =>
        NormalizedVector.ket
          ((QubitLayout.canonical (encoding exponentWidth width).width).basisEquiv.symm
            ((encoding exponentWidth width).encode
              (exponent, unitResidueWord modulus positive unit, 0)))) sameUnit
      exact (UnitaryCircuit.applyNormalized_seq
        (stageProgram exponentWidth width modulus base bit)
        (programForBits exponentWidth width modulus base bits) _
        (environment := environment)).trans
          ((congrArg ((programForBits exponentWidth width modulus base bits).applyNormalized
            environment)
            selected).trans (remaining.trans sameState))

/-- Schedule each exponent position once on the complete existing physical carrier. -/
def program (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding exponentWidth width).width).toQuantum :=
  programForBits exponentWidth width modulus base (List.ofFn fun bit => bit)

/-- Exact total action of the complete increasing-bit program, without a workspace premise. -/
lemma gidneyExponent_realizes (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit.Realizes (encoding exponentWidth width)
      (program exponentWidth width modulus base) environment
      (outputForBits modulus base (List.ofFn fun bit => bit)) :=
  gidneyExponentBits_realizes exponentWidth width modulus base _

/-- Canonical initialization computes the exact power and returns the shared auxiliary to zero. -/
lemma gidneyExponent_clean (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (exponent : Fin (2 ^ exponentWidth)) :
    (program exponentWidth width modulus base).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding exponentWidth width).width).basisEquiv.symm
            ((encoding exponentWidth width).encode
              (exponent, unitResidueWord modulus positive 1, 0)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding exponentWidth width).width).basisEquiv.symm
          ((encoding exponentWidth width).encode
            (exponent, unitResidueWord modulus positive (base ^ exponent.val), 0))) := by
  have actual := gidneyExponentBits_unit_word (environment := environment)
    exponentWidth width modulus positive base
    (List.ofFn fun bit => bit) exponent 1
  rw [scheduledUnit_all_eq_pow, mul_one] at actual
  exact actual

/-- The selected full program occupies the declared exponent and two-word layout. -/
lemma gidneyExponent_interface (exponentWidth width : Nat) :
    (encoding exponentWidth width).width = exponentWidth + 2 * width ∧
      (QubitLayout.canonical (encoding exponentWidth width).width).systemIdx =
        List.range (exponentWidth + 2 * width) :=
  gidneyExponentStage_interface exponentWidth width

end

end QuantumAlg.MAU.Exponentiation.Gidney
