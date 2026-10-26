/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Source.Carrier
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Coherent
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Physical.Action

/-!
# Canonical unit carrier of the actual constant-workspace measured arithmetic frame

The mathematical comparison keeps both original control values and every
canonical modular-unit seed. The physical auxiliary, two adder helpers and
flag are internally zero. The representation is injective, including modulus
one, and introduces no executable gate [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Carrier

noncomputable section

open MAU.Multiplication.Gidney.Measured

variable {width : Nat} (modulus : BitVec width) [NeZero modulus.toNat]

/-- Canonical fixed-width word of the original modular-unit representative. -/
def unitWord (seed : (ZMod modulus.toNat)ˣ) : BitVec width :=
  BitVec.ofNat width (seed : ZMod modulus.toNat).val

lemma unitWord_toNat (seed : (ZMod modulus.toNat)ˣ) :
    (unitWord modulus seed).toNat = (seed : ZMod modulus.toNat).val := by
  rw [unitWord, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ((ZMod.val_lt (seed : ZMod modulus.toNat)).trans modulus.isLt)]

lemma unitWord_canonical (seed : (ZMod modulus.toNat)ˣ) :
    (unitWord modulus seed).toNat < modulus.toNat := by
  rw [unitWord_toNat]
  exact ZMod.val_lt (seed : ZMod modulus.toNat)

/-- Actual original control/unit labels, with the auxiliary and three helpers physically zero. -/
def physicalLabel (label : (Recycling.Carrier.full modulus.toNat).Index) :
    Physical.Registers width :=
  Physical.cleanLabel width (finTwoEquiv label.1) (unitWord modulus label.2)

/-- Injective actual physical representation of both control values and all canonical unit seeds. -/
def embedding : (Recycling.Carrier.full modulus.toNat).Index ↪
    (Physical.qubits width).toQuantum.register.Index where
  toFun label := (Physical.qubits width).basisEquiv.symm (physicalLabel modulus label)
  inj' := by
    intro first second same
    have labels := (Physical.qubits width).basisEquiv.symm.injective same
    have controls := congrArg (Physical.layout width).control.get labels
    have sources := congrArg (Physical.layout width).sourceWord labels
    change (Physical.layout width).control.get
      (Physical.cleanLabel width (finTwoEquiv first.1) (unitWord modulus first.2)) =
      (Physical.layout width).control.get
      (Physical.cleanLabel width (finTwoEquiv second.1) (unitWord modulus second.2)) at controls
    rw [Physical.cleanLabel_control, Physical.cleanLabel_control] at controls
    change (Physical.layout width).sourceWord
      (Physical.cleanLabel width (finTwoEquiv first.1) (unitWord modulus first.2)) =
      (Physical.layout width).sourceWord
      (Physical.cleanLabel width (finTwoEquiv second.1) (unitWord modulus second.2)) at sources
    rw [Physical.cleanLabel_source, Physical.cleanLabel_source] at sources
    apply Prod.ext (finTwoEquiv.injective controls)
    apply Units.ext
    apply ZMod.val_injective modulus.toNat
    have values := congrArg BitVec.toNat sources
    rwa [unitWord_toNat, unitWord_toNat] at values

/-- Only the internally prepared/reset zero control is retained between original stages. -/
def zeroEmbedding : (Recycling.Carrier.units modulus.toNat).Index ↪
    (Physical.qubits width).toQuantum.register.Index :=
  (⟨fun seed => ((0 : Fin 2), seed), fun _ _ same => congrArg Prod.snd same⟩ :
    (Recycling.Carrier.units modulus.toNat).Index ↪
      (Recycling.Carrier.full modulus.toNat).Index).trans (embedding modulus)

private lemma control_bit (bit : Fin 2) : finTwoEquiv bit = bit.val.testBit 0 := by
  fin_cases bit <;> rfl

/-- The independent canonical product agrees with the same original unit translation action. -/
lemma selectedProduct_unit (positive : 0 < modulus.toNat)
    (coefficient seed : (ZMod modulus.toNat)ˣ) (bit : Fin 2) :
    Physical.selectedProduct modulus coefficient (finTwoEquiv bit) (unitWord modulus seed) =
      unitWord modulus ((if bit.val.testBit 0 then coefficient else 1) * seed) := by
  apply BitVec.eq_of_toNat_eq
  rw [Physical.selectedProduct_toNat modulus positive, control_bit, unitWord_toNat]
  cases selected : bit.val.testBit 0
  · simp only [Bool.false_eq_true, if_false, one_mul, unitWord_toNat]
  · simp only [if_true, unitWord_toNat]
    exact (ZMod.val_mul (coefficient : ZMod modulus.toNat) (seed : ZMod modulus.toNat)).symm

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Carrier
