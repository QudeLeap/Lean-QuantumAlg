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

open QuantumAlg.Nat.FixedWidth.UnitExponentiation Nat.FixedWidth

/-- Execute a static list of addressed exponent stages in its actual order. -/
def programForBits (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    List (Fin exponentWidth) → UnitaryCircuit (Qubits (encoding exponentWidth width).width)
  | [] => UnitaryCircuit.identity (Qubits (encoding exponentWidth width).width) [] (by simp)
  | bit :: bits => (stageProgram exponentWidth width modulus base bit).seq
      (programForBits exponentWidth width modulus base bits)

/-- Total finite arithmetic action of a list of selected-power stages. -/
def outputForBits {exponentWidth width : Nat} (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    List (Fin exponentWidth) → Registers exponentWidth width → Registers exponentWidth width
  | [], state => state
  | bit :: bits, state => outputForBits modulus base bits (stageOutput modulus base bit state)

/-- The same literal stage sequence realizes its complete all-input arithmetic action. -/
theorem gidneyExponentBits_realizes (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (bits : List (Fin exponentWidth)) :
    UnitaryCircuit.Realizes (encoding exponentWidth width)
      (programForBits exponentWidth width modulus base bits) (outputForBits modulus base bits) := by
  induction bits with
  | nil =>
      exact UnitaryCircuit.Realizes.identity (encoding exponentWidth width)
  | cons bit bits ih =>
      exact (gidneyExponentStage_realizes exponentWidth width modulus base bit).seq ih

private theorem stage_unit_word (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base seed : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth)
    (exponent : Fin (2 ^ exponentWidth)) :
    (stageProgram exponentWidth width modulus base bit).applyNormalized
        (NormalizedVector.ket ((encoding exponentWidth width).encode
          (exponent, unitResidueWord modulus positive seed, 0))) =
      NormalizedVector.ket ((encoding exponentWidth width).encode
        (exponent, unitResidueWord modulus positive (selectedUnit base exponent.val bit * seed),
          0)) := by
  have actual := gidneyExponentStage_clean exponentWidth width modulus positive base bit exponent
    (unitResidueWord modulus positive seed) (unitResidueWord_valid modulus positive seed)
  cases selected : exponent.val.testBit bit.val
  · simpa only [selectedUnit, selected, Bool.false_eq_true, if_false, one_mul] using actual
  · simpa only [selectedUnit, selected, if_true, unitProductWord_unitResidueWord] using actual

/-- The zero auxiliary word is returned at every boundary of an arbitrary static stage list. -/
theorem gidneyExponentBits_unit_word (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (bits : List (Fin exponentWidth))
    (exponent : Fin (2 ^ exponentWidth)) (seed : (ZMod modulus.val)ˣ) :
    (programForBits exponentWidth width modulus base bits).applyNormalized
        (NormalizedVector.ket ((encoding exponentWidth width).encode
          (exponent, unitResidueWord modulus positive seed, 0))) =
      NormalizedVector.ket ((encoding exponentWidth width).encode
        (exponent, unitResidueWord modulus positive
          (scheduledUnit base exponent.val bits * seed), 0)) := by
  induction bits generalizing seed with
  | nil =>
      simpa only [programForBits, scheduledUnit, List.map_nil, List.prod_nil, one_mul] using
        (UnitaryCircuit.applyNormalized_identity (Qubits (encoding exponentWidth width).width)
          [] (by simp) (NormalizedVector.ket ((encoding exponentWidth width).encode
            (exponent, unitResidueWord modulus positive seed, 0))))
  | cons bit bits ih =>
      have selected := stage_unit_word exponentWidth width modulus positive base seed bit exponent
      have remaining := ih (selectedUnit base exponent.val bit * seed)
      have sameUnit : scheduledUnit base exponent.val bits *
          (selectedUnit base exponent.val bit * seed) =
            scheduledUnit base exponent.val (bit :: bits) * seed := by
        simp only [scheduledUnit, List.map_cons, List.prod_cons]
        ac_rfl
      have sameState := congrArg (fun unit : (ZMod modulus.val)ˣ =>
        NormalizedVector.ket (R := Qubits (encoding exponentWidth width).width)
          ((encoding exponentWidth width).encode
          (exponent, unitResidueWord modulus positive unit, 0))) sameUnit
      exact (UnitaryCircuit.applyNormalized_seq
        (stageProgram exponentWidth width modulus base bit)
        (programForBits exponentWidth width modulus base bits) _).trans
          ((congrArg (programForBits exponentWidth width modulus base bits).applyNormalized
            selected).trans (remaining.trans sameState))

theorem gidneyExponentBits_physical_range (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (bits : List (Fin exponentWidth)) :
    (programForBits exponentWidth width modulus base bits).physical_idx ⊆
      List.range (exponentWidth + 2 * width) := by
  induction bits with
  | nil => exact List.nil_subset _
  | cons bit bits ih =>
      exact UnitaryCircuit.seq_physical_idx_subset _ _
        (gidneyExponentStage_physical_range exponentWidth width modulus base bit) ih

/-- Schedule each exponent position once and retain the complete existing physical carrier. -/
def program (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit (Qubits (encoding exponentWidth width).width) :=
  (programForBits exponentWidth width modulus base (List.ofFn fun bit => bit)).seq
    (UnitaryCircuit.identity (Qubits (encoding exponentWidth width).width)
      (List.range (exponentWidth + 2 * width)) List.nodup_range)

/-- Exact total action of the complete increasing-bit program, without a workspace premise. -/
theorem gidneyExponent_realizes (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit.Realizes (encoding exponentWidth width)
      (program exponentWidth width modulus base)
      (outputForBits modulus base (List.ofFn fun bit => bit)) := by
  apply ((gidneyExponentBits_realizes exponentWidth width modulus base
    (List.ofFn fun bit => bit)).seq
      (UnitaryCircuit.Realizes.identityAt (encoding exponentWidth width)
        (List.range (exponentWidth + 2 * width)) List.nodup_range)).congrStep
  intro state
  rfl

/-- Canonical initialization computes the exact power and returns the shared auxiliary to zero. -/
theorem gidneyExponent_clean (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (exponent : Fin (2 ^ exponentWidth)) :
    (program exponentWidth width modulus base).applyNormalized
        (NormalizedVector.ket ((encoding exponentWidth width).encode
          (exponent, unitResidueWord modulus positive 1, 0))) =
      NormalizedVector.ket ((encoding exponentWidth width).encode
        (exponent, unitResidueWord modulus positive (base ^ exponent.val), 0)) := by
  have actual := gidneyExponentBits_unit_word exponentWidth width modulus positive base
    (List.ofFn fun bit => bit) exponent 1
  rw [scheduledUnit_all_eq_pow, mul_one] at actual
  exact (UnitaryCircuit.applyNormalized_seq
    (programForBits exponentWidth width modulus base (List.ofFn fun bit => bit))
    (UnitaryCircuit.identity (Qubits (encoding exponentWidth width).width)
      (List.range (exponentWidth + 2 * width)) List.nodup_range) _).trans
        ((UnitaryCircuit.applyNormalized_identity (Qubits (encoding exponentWidth width).width)
          (List.range (exponentWidth + 2 * width)) List.nodup_range _).trans actual)

theorem gidneyExponent_physical (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (program exponentWidth width modulus base).physical_idx =
      List.range (exponentWidth + 2 * width) := by
  change (programForBits exponentWidth width modulus base
    (List.ofFn fun bit => bit)).physical_idx ∪
      List.range (exponentWidth + 2 * width) = List.range (exponentWidth + 2 * width)
  exact (gidneyExponentBits_physical_range exponentWidth width modulus base
    (List.ofFn fun bit => bit)).union_eq_right

end

end QuantumAlg.MAU.Exponentiation.Gidney
