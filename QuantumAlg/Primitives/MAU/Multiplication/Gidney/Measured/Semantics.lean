/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Stages
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Stages.Readout
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Arithmetic
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Word.Negative

/-!
# Actual canonical modular multiplication and physical explicit-inverse cleanup

On every canonical original source and zero target, the literal measured
word computes the selected unit product and physically clears the same
original target, flag and two helpers. Cleanup uses actual additions of
negative inverse-unit residues, including modulus one, with no measured
instrument dagger [VBE95, 9511018.tex:333-367; G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The actual original source readout is exactly the selected canonical unit product. -/
lemma multiplicationWord_unit_source_nat (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (coefficient : (ZMod modulus.toNat)ˣ) (initial : Data) (ready : layout.Ready modulus initial)
    (targetZero : (layout.targetWord initial).toNat = 0) :
    (layout.sourceWord
      (wordLabel (layout.multiplicationWord wide modulus (coefficient : ZMod modulus.toNat).val
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val) initial)).toNat =
      if layout.control.get initial then
        ((coefficient : ZMod modulus.toNat).val * (layout.sourceWord initial).toNat) %
          modulus.toNat else (layout.sourceWord initial).toNat := by
  rw [multiplicationWord_source_nat layout wide modulus positive _ _ initial ready,
    targetZero, Nat.zero_add]

/-- The explicitly emitted inverse MAC physically clears the original target on both controls. -/
lemma multiplicationWord_unit_target_zero (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (coefficient : (ZMod modulus.toNat)ˣ) (initial : Data) (ready : layout.Ready modulus initial)
    (sourceBound : (layout.sourceWord initial).toNat < modulus.toNat)
    (targetZero : (layout.targetWord initial).toNat = 0) :
    (layout.targetWord
      (wordLabel (layout.multiplicationWord wide modulus (coefficient : ZMod modulus.toNat).val
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val)
          initial)).toNat = 0 := by
  rw [multiplicationWord_label_stages]
  have actual := inverseMACWord_target_nat layout wide modulus positive
    ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val
    (layout.exchangedLabel wide modulus (coefficient : ZMod modulus.toNat).val initial)
    (exchangedLabel_ready layout wide modulus positive _ initial ready sourceBound)
  change (layout.targetWord
    (layout.multipliedLabel wide modulus (coefficient : ZMod modulus.toNat).val
      ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val initial)).toNat = _
    at actual
  rw [exchangedLabel_control layout wide modulus _ initial ready.clean,
    exchangedLabel_target_nat layout wide modulus positive _ initial ready,
    exchangedLabel_source_nat layout wide modulus positive _ initial ready] at actual
  by_cases enabled : layout.control.get initial = true
  · simp only [if_pos enabled, targetZero, Nat.zero_add] at actual
    exact actual.trans (Nat.FixedWidth.negativeUnitProduct_add_cancel modulus.toNat positive
      coefficient (layout.sourceWord initial).toNat)
  · simp only [if_neg enabled, targetZero] at actual
    exact actual

/-- The same original two helpers and reduction flag are physically zero after the actual word. -/
lemma multiplicationWord_clean_flag (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (coefficient inverseCoefficient : Nat) (initial : Data) (ready : layout.Ready modulus initial)
    (sourceBound : (layout.sourceWord initial).toNat < modulus.toNat) :
    (∀ helper, (layout.clean helper).get
      (wordLabel (layout.multiplicationWord wide modulus coefficient inverseCoefficient)
        initial) = false) ∧
    layout.flag.get
      (wordLabel (layout.multiplicationWord wide modulus coefficient inverseCoefficient)
        initial) = false := by
  rw [multiplicationWord_label_stages]
  have finalReady := multipliedLabel_ready layout wide modulus positive
    coefficient inverseCoefficient initial ready sourceBound
  exact ⟨finalReady.clean, finalReady.flag⟩

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
