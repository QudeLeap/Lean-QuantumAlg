/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Physical.Labels
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Semantics
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Frame
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Stages

/-!
# Complete canonical physical action of the actual measured modular multiplier

The selected canonical product, unchanged original control, zero original
auxiliary, two physically restored helpers and restored flag determine every
wire of the original complete frame. This label theorem is subsequently
used with the actual per-record common-alpha instrument, rather than a
fabricated unitary dagger [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Physical

noncomputable section

open Addition.Gidney.Measured.Instruction

variable {width : Nat}

/-- The independently specified selected canonical modular product on the retained source word. -/
def selectedProduct (modulus : BitVec width) (coefficient : (ZMod modulus.toNat)ˣ)
    (control : Bool) (source : BitVec width) : BitVec width :=
  if control then BitVec.ofNat width
    (((coefficient : ZMod modulus.toNat).val * source.toNat) % modulus.toNat) else source

lemma selectedProduct_toNat (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (coefficient : (ZMod modulus.toNat)ˣ) (control : Bool) (source : BitVec width) :
    (selectedProduct modulus coefficient control source).toNat =
      if control then ((coefficient : ZMod modulus.toNat).val * source.toNat) % modulus.toNat
      else source.toNat := by
  cases control with
  | false => rfl
  | true =>
      change (BitVec.ofNat width
        (((coefficient : ZMod modulus.toNat).val * source.toNat) % modulus.toNat)).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
        ((Nat.mod_lt _ positive).trans modulus.isLt)]
      rw [if_pos rfl]

/-- The actual allocated clean label supplies the exact internal helper/flag/canonical promise. -/
lemma cleanLabel_ready (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (control : Bool) (source : BitVec width) :
    (layout width).Ready modulus (cleanLabel width control source) where
  clean := (cleanLabel_helpers width control source).1
  flag := (cleanLabel_helpers width control source).2
  canonical := by rw [cleanLabel_target]; exact positive

/-- The actual complete arithmetic label is exactly the independent canonical product label. -/
lemma multiplicationWord_cleanLabel (wide : 2 ≤ width) (modulus : BitVec width)
    (positive : 0 < modulus.toNat) (coefficient : (ZMod modulus.toNat)ˣ)
    (control : Bool) (source : BitVec width) (canonical : source.toNat < modulus.toNat) :
    wordLabel ((layout width).multiplicationWord wide modulus
      (coefficient : ZMod modulus.toNat).val
      ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val)
        (cleanLabel width control source) =
      cleanLabel width control (selectedProduct modulus coefficient control source) := by
  let input := cleanLabel width control source
  let coefficientValue := (coefficient : ZMod modulus.toNat).val
  let inverseValue := ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val
  let result := wordLabel
    ((layout width).multiplicationWord wide modulus coefficientValue inverseValue) input
  have ready := cleanLabel_ready modulus positive control source
  have sourceBound : ((layout width).sourceWord input).toNat < modulus.toNat := by
    rw [cleanLabel_source]
    exact canonical
  have targetZero : ((layout width).targetWord input).toNat = 0 := by
    rw [cleanLabel_target]
    rfl
  have sourceNat := Layout.multiplicationWord_unit_source_nat (layout width) wide modulus positive
    coefficient input ready targetZero
  have sourceSame : (layout width).sourceWord result =
      selectedProduct modulus coefficient control source := by
    apply BitVec.eq_of_toNat_eq
    rw [selectedProduct_toNat modulus positive]
    simpa only [result, coefficientValue, inverseValue, input, cleanLabel_control,
      cleanLabel_source] using sourceNat
  have targetSame : (layout width).targetWord result = 0 := by
    apply BitVec.eq_of_toNat_eq
    exact Layout.multiplicationWord_unit_target_zero (layout width) wide modulus positive
      coefficient input ready sourceBound targetZero
  have helpers := Layout.multiplicationWord_clean_flag (layout width) wide modulus positive
    coefficientValue inverseValue input ready sourceBound
  have exchangedReady := Layout.exchangedLabel_ready (layout width) wide modulus positive
    coefficientValue input ready sourceBound
  have controlSame : (layout width).control.get result = control := by
    change (layout width).control.get
      (wordLabel ((layout width).multiplicationWord wide modulus coefficientValue inverseValue)
        input) = control
    rw [Layout.multiplicationWord_label_stages]
    have inverseFrame := Layout.accumulatePrefixWord_frame (layout width) wide modulus
      (Layout.inverseConstant modulus inverseValue) width le_rfl
        ((layout width).exchangedLabel wide modulus coefficientValue input) exchangedReady.clean
    exact inverseFrame.control.trans
      ((Layout.exchangedLabel_control (layout width) wide modulus coefficientValue input
        ready.clean).trans (cleanLabel_control width control source))
  apply label_ext width
  intro port
  rcases port with singleton | index | index | helper | singleton
  · cases singleton
    exact controlSame.trans (cleanLabel_control width control _).symm
  · have actual := congrArg (fun word : BitVec width => word.toNat.testBit index.val) sourceSame
    rw [Layout.multiplicationSourceWord_bit _ _ _ index.isLt] at actual
    have read := Layout.multiplicationSourceWord_bit (layout width)
      (cleanLabel width control (selectedProduct modulus coefficient control source))
      index.val index.isLt
    rw [cleanLabel_source] at read
    exact actual.trans read
  · have actual := congrArg (fun word : BitVec width => word.toNat.testBit index.val) targetSame
    rw [Layout.multiplicationTargetWord_bit _ _ _ index.isLt] at actual
    have zero : ((layout width).target index).get result = false := by simpa using actual
    have read := Layout.multiplicationTargetWord_bit (layout width)
      (cleanLabel width control (selectedProduct modulus coefficient control source))
      index.val index.isLt
    rw [cleanLabel_target] at read
    have outputZero : ((layout width).target index).get
        (cleanLabel width control (selectedProduct modulus coefficient control source)) =
        false := by
      simpa using read.symm
    exact zero.trans outputZero.symm
  · exact (helpers.1 helper).trans
      ((cleanLabel_helpers width control _).1 helper).symm
  · cases singleton
    exact helpers.2.trans (cleanLabel_helpers width control _).2.symm

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Physical
