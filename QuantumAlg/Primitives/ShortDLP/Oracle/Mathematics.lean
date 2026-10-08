/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Primitives.ShortDLP.Layout
import all QuantumAlg.Core.Base
import all QuantumAlg.Util.NumberTheory.Cyclic.Power
import all QuantumAlg.Util.ResidueEncoding

/-!
# Short-DLP group operation mathematics

The integer-fiber bounds, reversible workspace permutation, and induced
operator are independent of the execution model that grants oracle queries.
-/

section

namespace QuantumAlg

noncomputable section

namespace ShortDLP

/-- Source group expression `[a]g ⊙ [-b]x`, written multiplicatively. -/
def oracleValue {N : Nat} (g x : (ZMod N)ˣ) (a b : Nat) : (ZMod N)ˣ :=
  g ^ a * (x ^ b)⁻¹

/-- Integer exponent represented by one short-DLP oracle input when the target
is `g^secret`. -/
def oracleExponent (secret a b : Nat) : Int :=
  (a : Int) - ((b * secret : Nat) : Int)

/-- Translate the possibly negative exponent `a-b*secret` into the finite
interval starting at zero. -/
def oracleFiberIndex (params : RegisterParameters) (secret : Nat)
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell)) : Nat :=
  a.val + (2 ^ params.ell - 1 - b.val) * secret

/-- For a fixed second-register index, the canonical integer-fiber index
determines the first-register index uniquely. -/
theorem oracleFiberIndex_injective_first
    (params : RegisterParameters) (secret : Nat)
    (b : Fin (2 ^ params.ell)) :
    Function.Injective (fun a : Fin (2 ^ firstBits params) =>
      oracleFiberIndex params secret a b) := by
  intro left right hindex
  apply Fin.ext
  change left.val + (2 ^ params.ell - 1 - b.val) * secret =
    right.val + (2 ^ params.ell - 1 - b.val) * secret at hindex
  exact Nat.add_right_cancel hindex

/-- Length of the no-wrap exponent interval used by the short-DLP source. -/
def oracleFiberSpan (params : RegisterParameters) (secret : Nat) : Nat :=
  2 ^ firstBits params + (2 ^ params.ell - 1) * secret

/-- A short logarithm `secret < 2^m` makes the complete integer-exponent
interval no longer than twice the first Fourier-register cardinality. -/
theorem oracleFiberSpan_le_two_mul_firstRegister
    (params : RegisterParameters) (secret : Nat)
    (hsecret : secret < 2 ^ params.m) :
    oracleFiberSpan params secret ≤ 2 * 2 ^ firstBits params := by
  have hproduct :
      (2 ^ params.ell - 1) * secret ≤
        2 ^ params.ell * 2 ^ params.m :=
    Nat.mul_le_mul (Nat.sub_le _ _) (Nat.le_of_lt hsecret)
  unfold oracleFiberSpan firstBits
  rw [pow_add]
  omega

/-- Lower-offset magnitude of the source exponent interval. -/
def oracleFiberOffset (params : RegisterParameters) (secret : Nat) : Nat :=
  (2 ^ params.ell - 1) * secret

/-- Canonical integer exponent represented by an index in the complete source
interval `[-offset, 2^(ell+m)-1]`. -/
def oracleExponentAtIndex (params : RegisterParameters) (secret : Nat)
    (index : Fin (oracleFiberSpan params secret)) : Int :=
  (index.val : Int) - (oracleFiberOffset params secret : Int)

/-- Canonical source-interval indices encode distinct integer exponents. -/
theorem oracleExponentAtIndex_injective
    (params : RegisterParameters) (secret : Nat) :
    Function.Injective (oracleExponentAtIndex params secret) := by
  intro left right h
  apply Fin.ext
  unfold oracleExponentAtIndex at h
  omega

theorem oracleExponent_add_lowerOffset
    (params : RegisterParameters) (secret : Nat)
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell)) :
    oracleExponent secret a.val b.val +
        (((2 ^ params.ell - 1) * secret : Nat) : Int) =
      (oracleFiberIndex params secret a b : Nat) := by
  have hb : b.val ≤ 2 ^ params.ell - 1 := Nat.le_pred_of_lt b.isLt
  have hsplitNat :
      (2 ^ params.ell - 1 - b.val) * secret + b.val * secret =
        (2 ^ params.ell - 1) * secret := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hb]
  have hsplitInt :
      (((2 ^ params.ell - 1 - b.val) * secret : Nat) : Int) +
          ((b.val * secret : Nat) : Int) =
        (((2 ^ params.ell - 1) * secret : Nat) : Int) := by
    exact_mod_cast hsplitNat
  unfold oracleExponent oracleFiberIndex
  push_cast
  omega

theorem oracleFiberIndex_lt_span
    (params : RegisterParameters) (secret : Nat)
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell)) :
    oracleFiberIndex params secret a b < oracleFiberSpan params secret := by
  have hb : b.val ≤ 2 ^ params.ell - 1 := Nat.le_pred_of_lt b.isLt
  have hmul :
      (2 ^ params.ell - 1 - b.val) * secret ≤
        (2 ^ params.ell - 1) * secret :=
    Nat.mul_le_mul_right secret (Nat.sub_le _ _)
  unfold oracleFiberIndex oracleFiberSpan
  omega

/-- The canonical interval index of an actual oracle input decodes back to its
integer exponent. -/
theorem oracleExponentAtIndex_oracleFiberIndex
    (params : RegisterParameters) (secret : Nat)
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell)) :
    oracleExponentAtIndex params secret
        ⟨oracleFiberIndex params secret a b,
          oracleFiberIndex_lt_span params secret a b⟩ =
      oracleExponent secret a.val b.val := by
  have h := oracleExponent_add_lowerOffset params secret a b
  change (oracleFiberIndex params secret a b : Int) -
      (oracleFiberOffset params secret : Int) =
    oracleExponent secret a.val b.val
  unfold oracleFiberOffset
  omega

/-- Any canonical interval exponent and any actual oracle exponent differ by
strictly less than the full interval span. -/
theorem oracleExponentAtIndex_sub_abs_lt_span
    (params : RegisterParameters) (secret : Nat)
    (index : Fin (oracleFiberSpan params secret))
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell)) :
    |oracleExponentAtIndex params secret index -
        oracleExponent secret a.val b.val| <
      (oracleFiberSpan params secret : Int) := by
  let actualIndex : Fin (oracleFiberSpan params secret) :=
    ⟨oracleFiberIndex params secret a b,
      oracleFiberIndex_lt_span params secret a b⟩
  have hfinite := Int.abs_sub_lt_of_lt_lt actualIndex.isLt index.isLt
  change
    |(index.val : Int) - (actualIndex.val : Int)| <
      (oracleFiberSpan params secret : Int) at hfinite
  rw [← oracleExponentAtIndex_oracleFiberIndex params secret a b]
  unfold oracleExponentAtIndex
  simpa only [sub_sub_sub_cancel_right] using hfinite

/-- Two distinct canonical interval exponents differ by strictly less than the
full interval span. -/
theorem oracleExponentAtIndex_sub_abs_lt_span_index
    (params : RegisterParameters) (secret : Nat)
    (left right : Fin (oracleFiberSpan params secret)) :
    |oracleExponentAtIndex params secret left -
        oracleExponentAtIndex params secret right| <
      (oracleFiberSpan params secret : Int) := by
  have hfinite := Int.abs_sub_lt_of_lt_lt right.isLt left.isLt
  change
    |(left.val : Int) - (right.val : Int)| <
      (oracleFiberSpan params secret : Int) at hfinite
  unfold oracleExponentAtIndex
  simpa only [sub_sub_sub_cancel_right] using hfinite

theorem oracleExponent_sub_abs_lt_span
    (params : RegisterParameters) (secret : Nat)
    (leftA : Fin (2 ^ firstBits params))
    (leftB : Fin (2 ^ params.ell))
    (rightA : Fin (2 ^ firstBits params))
    (rightB : Fin (2 ^ params.ell)) :
    |oracleExponent secret leftA.val leftB.val -
        oracleExponent secret rightA.val rightB.val| <
      (oracleFiberSpan params secret : Int) := by
  have hleft := oracleFiberIndex_lt_span params secret leftA leftB
  have hright := oracleFiberIndex_lt_span params secret rightA rightB
  have hfinite := Int.abs_sub_lt_of_lt_lt hright hleft
  rw [← oracleExponent_add_lowerOffset params secret leftA leftB,
    ← oracleExponent_add_lowerOffset params secret rightA rightB] at hfinite
  simpa only [add_sub_add_right_eq_sub] using hfinite

/-- When the target is `g^secret`, the queried group value is the integer
power `g^(a-b*secret)`.  This is the exponent fiber used by the source
probability distribution [E23, arxiv-v5.tex:228-245]. -/
theorem oracleValue_eq_zpow_of_target {N : Nat} (g x : (ZMod N)ˣ)
    (secret a b : Nat) (htarget : x = g ^ secret) :
    oracleValue g x a b = g ^ oracleExponent secret a b := by
  rw [oracleValue, htarget, ← pow_mul]
  rw [← zpow_natCast g a, ← zpow_natCast g (secret * b), ← zpow_neg,
    ← zpow_add]
  unfold oracleExponent
  congr 2
  push_cast
  ring

/-- Under the source's local no-wrap condition, equality of two queried group
values is exactly equality of their integer exponent fibers. -/
theorem oracleValue_eq_oracleValue_iff_exponent_eq_of_abs_sub_lt_orderOf
    {N : Nat} (g x : (ZMod N)ˣ) (secret leftA leftB rightA rightB : Nat)
    (htarget : x = g ^ secret)
    (hsmall :
      |oracleExponent secret leftA leftB -
          oracleExponent secret rightA rightB| < (orderOf g : Int)) :
    oracleValue g x leftA leftB = oracleValue g x rightA rightB ↔
      oracleExponent secret leftA leftB =
        oracleExponent secret rightA rightB := by
  rw [oracleValue_eq_zpow_of_target g x secret leftA leftB htarget,
    oracleValue_eq_zpow_of_target g x secret rightA rightB htarget]
  exact NumberTheory.zpow_eq_zpow_iff_of_abs_sub_lt_orderOf g _ _ hsmall

/-- Under the source order bound, a canonical interval power `g^e` equals an
actual queried value exactly when their integer exponents agree. -/
theorem zpow_at_index_eq_oracleValue_iff_exponent_eq_of_span_le_orderOf
    {N : Nat} {params : RegisterParameters}
    (g x : (ZMod N)ˣ) (secret : Nat)
    (index : Fin (oracleFiberSpan params secret))
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    g ^ oracleExponentAtIndex params secret index =
        oracleValue g x a.val b.val ↔
      oracleExponentAtIndex params secret index =
        oracleExponent secret a.val b.val := by
  rw [oracleValue_eq_zpow_of_target g x secret a.val b.val htarget]
  apply NumberTheory.zpow_eq_zpow_iff_of_abs_sub_lt_orderOf
  exact (oracleExponentAtIndex_sub_abs_lt_span
    params secret index a b).trans_le (by exact_mod_cast horder)

/-- The source order lower bound makes every workspace fiber collision-free
over the complete exponent-register box [E23, arxiv-v5.tex:244-245]. -/
theorem oracleValue_eq_oracleValue_iff_exponent_eq_of_span_le_orderOf
    {N : Nat} {params : RegisterParameters}
    (g x : (ZMod N)ˣ) (secret : Nat)
    (leftA : Fin (2 ^ firstBits params))
    (leftB : Fin (2 ^ params.ell))
    (rightA : Fin (2 ^ firstBits params))
    (rightB : Fin (2 ^ params.ell))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    oracleValue g x leftA.val leftB.val =
        oracleValue g x rightA.val rightB.val ↔
      oracleExponent secret leftA.val leftB.val =
        oracleExponent secret rightA.val rightB.val := by
  apply oracleValue_eq_oracleValue_iff_exponent_eq_of_abs_sub_lt_orderOf
    g x secret leftA.val leftB.val rightA.val rightB.val htarget
  exact (oracleExponent_sub_abs_lt_span
    params secret leftA leftB rightA rightB).trans_le (by exact_mod_cast horder)

/-- Canonical binary encoding of a unit's residue value. -/
def encodeUnit {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (value : (ZMod N)ˣ) : Fin (2 ^ params.workspaceBits) :=
  encoding.encode value

/-- Canonical workspace encoding does not identify distinct units. -/
theorem encodeUnit_injective {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits) :
    Function.Injective (encodeUnit encoding) :=
  encoding.encode_injective

/-- Reversible XOR loading of the selected group value into the workspace. -/
def oracleTarget {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (a : Fin (2 ^ firstBits params))
    (b : Fin (2 ^ params.ell))
    (workspace : Fin (2 ^ params.workspaceBits)) :
    Fin (2 ^ params.workspaceBits) :=
  ⟨Nat.xor workspace.val (encodeUnit encoding (oracleValue g x a.val b.val)).val,
    Nat.xor_lt_two_pow workspace.isLt
      (encodeUnit encoding (oracleValue g x a.val b.val)).isLt⟩

/-- Basis permutation underlying the actual short-DLP group-operation query. -/
def oraclePerm {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    Equiv.Perm
      ((Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) ×
        Fin (2 ^ params.workspaceBits)) where
  toFun input :=
    (input.1, oracleTarget encoding g x input.1.1 input.1.2 input.2)
  invFun input :=
    (input.1, oracleTarget encoding g x input.1.1 input.1.2 input.2)
  left_inv input := by
    ext <;> simp [oracleTarget, Nat.xor_assoc]
  right_inv input := by
    ext <;> simp [oracleTarget, Nat.xor_assoc]

@[simp]
theorem oraclePerm_symm {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    (oraclePerm encoding g x).symm = oraclePerm encoding g x :=
  rfl

/-- Metadata-free unitary induced by the short-DLP basis permutation. -/
def tripleEquiv (params : RegisterParameters) :
    ((Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) ×
        Fin (2 ^ params.workspaceBits)) ≃
      Fin (2 ^ totalQubits params) :=
  (Equiv.prodCongr
      (prodEquiv (m := firstBits params) (n := params.ell))
      (Equiv.refl (Fin (2 ^ params.workspaceBits)))).trans
    (prodEquiv
      (m := firstBits params + params.ell) (n := params.workspaceBits))

/-- Metadata-free unitary induced by the short-DLP basis permutation. -/
def oracleOperator {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) : UnitaryOperator (Qubits (totalQubits params)) :=
  UnitaryOperator.ofPerm
    ((tripleEquiv params).permCongr (oraclePerm encoding g x))

end ShortDLP

end

end QuantumAlg

end
