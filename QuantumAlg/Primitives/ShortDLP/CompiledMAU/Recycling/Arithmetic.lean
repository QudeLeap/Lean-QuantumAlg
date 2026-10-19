/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Program
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Stage
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Exponentiation
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Word
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Word.Multiplication
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fin.Rev

/-!
# One actual control and the existing clean two-word multiplier

This module specializes the existing
literal selected-power stage rather than copying its gate compiler. Clean
statements are internal composition facts after actual bank preparation;
they are not added to a public problem as input certificates. Schedule
permutation is asserted only on the canonical unit/zero-auxiliary subspace.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Arithmetic

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth Nat.FixedWidth.UnitExponentiation

abbrev Registers (width : Nat) := MAU.Exponentiation.Gidney.Registers 1 width

def encoding (width : Nat) : BinaryLabelEncoding (Registers width) :=
  MAU.Exponentiation.Gidney.encoding 1 width

def layout (width : Nat) : QubitLayout (encoding width).width :=
  QubitLayout.canonical (encoding width).width

/-- Reuse the existing literal multiplier with exactly one exponent/control bit. -/
def program {width : Nat} (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty (layout width).toQuantum :=
  MAU.Exponentiation.Gidney.stageProgram 1 width modulus coefficient 0

/-- The unrestricted complete two-word action is retained; no dirty-state claim is omitted. -/
def step {width : Nat} (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (state : Registers width) : Registers width :=
  (state.1, if state.1.val.testBit 0 then
    unitMultiplicationPairEquiv modulus coefficient state.2 else state.2)

/-- The actual stage has exact all-label phase, including its unselected branch. -/
lemma program_realizes {width : Nat} (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    UnitaryCircuit.Realizes (encoding width) (program modulus coefficient) environment
      (step modulus coefficient) := by
  change UnitaryCircuit.Realizes (MAU.Exponentiation.Gidney.encoding 1 width)
    (MAU.Exponentiation.Gidney.stageProgram 1 width modulus coefficient 0) environment
    (step modulus coefficient)
  have unitEq : stageUnit coefficient (0 : Fin 1) = coefficient := by
    simp only [stageUnit, Fin.val_zero, pow_zero, pow_one]
  have actionEq : MAU.Exponentiation.Gidney.stageOutput modulus coefficient (0 : Fin 1) =
      step modulus coefficient := by
    funext state
    change (state.1, if state.1.val.testBit 0 then
      unitMultiplicationPairEquiv modulus (stageUnit coefficient (0 : Fin 1)) state.2
      else state.2) = _
    rw [unitEq]
    rfl
  exact actionEq ▸
    MAU.Exponentiation.Gidney.gidneyExponentStage_realizes 1 width modulus coefficient 0

/-- The internal clean boundary keeps the same power carrier and restores the actual auxiliary. -/
lemma program_clean {width : Nat} (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (coefficient : (ZMod modulus.val)ˣ)
    (control : Fin (2 ^ 1)) (power : Fin (2 ^ width)) (valid : power.val < modulus.val) :
    (program modulus coefficient).applyNormalized environment
        (NormalizedVector.ket ((layout width).basisEquiv.symm
          ((encoding width).encode (control, power, 0)))) =
      NormalizedVector.ket ((layout width).basisEquiv.symm
        ((encoding width).encode
          (control, if control.val.testBit 0 then
            unitProductWord modulus positive coefficient power else power, 0))) := by
  change (MAU.Exponentiation.Gidney.stageProgram 1 width modulus coefficient 0).applyNormalized
      environment
      (NormalizedVector.ket
        ((QubitLayout.canonical (MAU.Exponentiation.Gidney.encoding 1 width).width).basisEquiv.symm
          ((MAU.Exponentiation.Gidney.encoding 1 width).encode (control, power, 0)))) =
    NormalizedVector.ket
      ((QubitLayout.canonical (MAU.Exponentiation.Gidney.encoding 1 width).width).basisEquiv.symm
        ((MAU.Exponentiation.Gidney.encoding 1 width).encode
          (control, if control.val.testBit 0 then
            unitProductWord modulus positive coefficient power else power, 0)))
  have unitEq : stageUnit coefficient (0 : Fin 1) = coefficient := by
    simp only [stageUnit, Fin.val_zero, pow_zero, pow_one]
  simpa only [Fin.val_zero, unitEq] using
    MAU.Exponentiation.Gidney.gidneyExponentStage_clean 1 width modulus positive
      coefficient 0 control power valid

/-- Selecting a bit multiplies any canonical unit seed and returns the same zero auxiliary. -/
lemma program_clean_unit {width : Nat} (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (coefficient seed : (ZMod modulus.val)ˣ)
    (control : Fin (2 ^ 1)) :
    (program modulus coefficient).applyNormalized environment
        (NormalizedVector.ket ((layout width).basisEquiv.symm
          ((encoding width).encode (control, unitResidueWord modulus positive seed, 0)))) =
      NormalizedVector.ket ((layout width).basisEquiv.symm
        ((encoding width).encode
          (control, unitResidueWord modulus positive
            ((if control.val.testBit 0 then coefficient else 1) * seed), 0))) := by
  have actual := program_clean (environment := environment) modulus positive coefficient control
    (unitResidueWord modulus positive seed) (unitResidueWord_valid modulus positive seed)
  cases selected : control.val.testBit 0
  · simpa only [selected, Bool.false_eq_true, if_false, one_mul] using actual
  · simpa only [selected, if_true, unitProductWord_unitResidueWord] using actual

/-- Any permutation of old addressed stages agrees on the internally prepared clean carrier.
The full dirty two-word permutations are deliberately not asserted to commute. -/
lemma clean_schedule_perm (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base seed : (ZMod modulus.val)ˣ) (exponent : Fin (2 ^ exponentWidth))
    (before after : List (Fin exponentWidth)) (same : before.Perm after) :
    (MAU.Exponentiation.Gidney.programForBits
        exponentWidth width modulus base before).applyNormalized environment (NormalizedVector.ket
          ((QubitLayout.canonical
            (MAU.Exponentiation.Gidney.encoding exponentWidth width).width).basisEquiv.symm
              ((MAU.Exponentiation.Gidney.encoding exponentWidth width).encode
                (exponent, unitResidueWord modulus positive seed, 0)))) =
      (MAU.Exponentiation.Gidney.programForBits
        exponentWidth width modulus base after).applyNormalized environment (NormalizedVector.ket
          ((QubitLayout.canonical
            (MAU.Exponentiation.Gidney.encoding exponentWidth width).width).basisEquiv.symm
              ((MAU.Exponentiation.Gidney.encoding exponentWidth width).encode
                (exponent, unitResidueWord modulus positive seed, 0)))) := by
  have products : scheduledUnit base exponent.val before =
      scheduledUnit base exponent.val after :=
    (same.map (selectedUnit base exponent.val)).prod_eq
  rw [MAU.Exponentiation.Gidney.gidneyExponentBits_unit_word
      exponentWidth width modulus positive base before exponent seed,
    MAU.Exponentiation.Gidney.gidneyExponentBits_unit_word
      exponentWidth width modulus positive base after exponent seed,
    products]

/-- Source wire order is big-endian, so descending exponent significance is explicit. -/
def msbBits (bits : Nat) : List (Fin bits) := List.ofFn fun position => position.rev

lemma msbBits_perm (bits : Nat) :
    (msbBits bits).Perm (List.ofFn fun position : Fin bits => position) := by
  simpa only [msbBits, Function.comp_def, Fin.revPerm_apply] using
    (Fin.revPerm (n := bits)).ofFn_comp_perm (fun position : Fin bits => position)

/-- Reorder the existing full arithmetic compiler to MSB-first only on its actual clean seed.
This bridges the old exponent word before the distinct control-recycling proof is applied. -/
lemma old_program_msb_clean (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base seed : (ZMod modulus.val)ˣ) (exponent : Fin (2 ^ exponentWidth)) :
    (MAU.Exponentiation.Gidney.program exponentWidth width modulus base).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical
            (MAU.Exponentiation.Gidney.encoding exponentWidth width).width).basisEquiv.symm
              ((MAU.Exponentiation.Gidney.encoding exponentWidth width).encode
                (exponent, unitResidueWord modulus positive seed, 0)))) =
      (MAU.Exponentiation.Gidney.programForBits exponentWidth width modulus base
          (msbBits exponentWidth)).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical
            (MAU.Exponentiation.Gidney.encoding exponentWidth width).width).basisEquiv.symm
              ((MAU.Exponentiation.Gidney.encoding exponentWidth width).encode
                (exponent, unitResidueWord modulus positive seed, 0)))) := by
  simpa only [MAU.Exponentiation.Gidney.program] using
    clean_schedule_perm exponentWidth width modulus positive base seed exponent
      (List.ofFn fun bit : Fin exponentWidth => bit) (msbBits exponentWidth)
      (msbBits_perm exponentWidth).symm

/-- The carrier contains one control and exactly the original two arithmetic words. -/
lemma width_eq (width : Nat) : (encoding width).width = 1 + 2 * width := by
  change 1 + (width + width) = 1 + 2 * width
  omega

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Arithmetic
