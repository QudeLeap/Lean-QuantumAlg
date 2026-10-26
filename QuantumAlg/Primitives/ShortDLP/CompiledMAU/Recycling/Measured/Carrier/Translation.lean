/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Fourier
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Exponentiation
import Mathlib.Data.Fin.Rev
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Pure unit translations at their original ordered exponent addresses

Only the canonical source unit translations are combined. The actual total
measured arithmetic or dirty matrices are never reordered. Original MSB
addresses recover the same unit power for every input tuple
[GN96, 9511007.tex:214-266].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open QuantumFourierTransform.Semiclassical
open Nat.FixedWidth.UnitExponentiation
open scoped BigOperators

variable {width : Nat} (modulus : BitVec width) [NeZero modulus.toNat]

lemma measuredTranslation_one :
    (unitTranslation modulus 1 : HilbertOperator (Recycling.Carrier.units modulus.toNat)) = 1 := by
  ext row column
  have inverseOne (seed : (Recycling.Carrier.units modulus.toNat).Index) :
      (Equiv.mulLeft (1 : (ZMod modulus.toNat)ˣ)).symm seed = seed := by
    change (1 : (ZMod modulus.toNat)ˣ)⁻¹ * seed = seed
    simp only [inv_one, one_mul]
  simp only [unitTranslation, UnitaryOperator.ofPerm_entry, inverseOne, Matrix.one_apply]

lemma measuredTranslation_mul (first second : (ZMod modulus.toNat)ˣ) :
    (unitTranslation modulus first : HilbertOperator (Recycling.Carrier.units modulus.toNat)) *
        (unitTranslation modulus second : HilbertOperator (Recycling.Carrier.units modulus.toNat)) =
      (unitTranslation modulus (first * second) :
        HilbertOperator (Recycling.Carrier.units modulus.toNat)) := by
  have operators : unitTranslation modulus first * unitTranslation modulus second =
      unitTranslation modulus (first * second) := by
    unfold unitTranslation
    rw [UnitaryOperator.ofPerm_mul]
    apply congrArg (fun permutation : Equiv.Perm (Recycling.Carrier.units modulus.toNat).Index =>
      UnitaryOperator.ofPerm permutation)
    calc
      (Equiv.mulLeft second).symm * (Equiv.mulLeft first).symm =
          Equiv.mulLeft (second⁻¹ * first⁻¹) := by
        rw [Equiv.mulLeft_symm, Equiv.mulLeft_symm, Equiv.mulLeft_mul]
      _ = (Equiv.mulLeft (first * second)).symm := by
        rw [Equiv.mulLeft_symm, mul_inv_rev]
  exact congrArg (fun operator : UnitaryOperator (Recycling.Carrier.units modulus.toNat) =>
    (operator : HilbertOperator (Recycling.Carrier.units modulus.toNat))) operators

private lemma measured_chronological_translations (choices : List (ZMod modulus.toNat)ˣ) :
    Partner.chronologicalProduct (choices.map fun unit =>
      (unitTranslation modulus unit : HilbertOperator (Recycling.Carrier.units modulus.toNat))) =
      (unitTranslation modulus choices.prod :
        HilbertOperator (Recycling.Carrier.units modulus.toNat)) :=
    by
  induction choices with
  | nil => simp only [List.map_nil, Partner.chronologicalProduct, List.prod_nil,
      measuredTranslation_one]
  | cons head tail induction =>
      rw [List.map_cons, Partner.chronologicalProduct, induction, measuredTranslation_mul,
        List.prod_cons]
      exact congrArg (fun unit : (ZMod modulus.toNat)ˣ =>
        (unitTranslation modulus unit : HilbertOperator (Recycling.Carrier.units modulus.toNat)))
        (mul_comm tail.prod head)

private lemma measured_selected_translation (unit : (ZMod modulus.toNat)ˣ) (bit : Fin 2) :
    Partner.selected
        (unitTranslation modulus unit :
          HilbertOperator (Recycling.Carrier.units modulus.toNat)) bit =
      (unitTranslation modulus (if bit = 0 then 1 else unit) :
        HilbertOperator (Recycling.Carrier.units modulus.toNat)) := by
  by_cases zero : bit = 0
  · simp only [Partner.selected, zero, if_true, measuredTranslation_one]
  · simp only [Partner.selected, zero, if_false]

/-- The shared MSB-ordered actual selected translations recover the original full exponent. -/
lemma measuredOrderedWord_power (bits : Nat) (unit : (ZMod modulus.toNat)ˣ) (input : Bits bits) :
    Partner.orderedWord bits
        (fun position => (exponentPowerOperators modulus unit bits position :
          HilbertOperator (Recycling.Carrier.units modulus.toNat))) input =
      (unitTranslation modulus (unit ^ (binaryEquiv bits input).val) :
        HilbertOperator (Recycling.Carrier.units modulus.toNat)) := by
  let choices (position : Fin bits) : (ZMod modulus.toNat)ˣ :=
    if tupleCoordinates bits input position = 0 then 1 else unit ^ (2 ^ position.rev.val)
  have chosen (position : Fin bits) :
      choices position = selectedUnit unit (binaryEquiv bits input).val position.rev := by
    dsimp only [choices, selectedUnit, stageUnit]
    rw [Partner.tuple_bit]
    generalize tupleCoordinates bits input position = bit
    fin_cases bit <;> rfl
  have product : (∏ position : Fin bits, choices position) =
      unit ^ (binaryEquiv bits input).val := by
    calc
      _ = ∏ position : Fin bits, selectedUnit unit (binaryEquiv bits input).val position.rev := by
        apply Finset.prod_congr rfl
        intro position _
        exact chosen position
      _ = ∏ position : Fin bits, selectedUnit unit (binaryEquiv bits input).val position :=
        Equiv.prod_comp (Fin.revPerm (n := bits))
          (selectedUnit unit (binaryEquiv bits input).val)
      _ = _ := by
        have actual := scheduledUnit_all_eq_pow unit (binaryEquiv bits input)
        simpa only [scheduledUnit, List.map_ofFn, List.prod_ofFn, Function.comp_apply] using actual
  have mapped :
      (List.ofFn fun position : Fin bits => (unitTranslation modulus (choices position) :
        HilbertOperator (Recycling.Carrier.units modulus.toNat))) =
      (List.ofFn choices).map fun unit =>
        (unitTranslation modulus unit :
          HilbertOperator (Recycling.Carrier.units modulus.toNat)) := by
    simp only [List.map_ofFn, Function.comp_def]
  unfold Partner.orderedWord
  simp only [exponentPowerOperators, measured_selected_translation]
  change Partner.chronologicalProduct
    (List.ofFn fun position : Fin bits => (unitTranslation modulus (choices position) :
      HilbertOperator (Recycling.Carrier.units modulus.toNat))) = _
  rw [mapped, measured_chronological_translations, List.prod_ofFn, product]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
