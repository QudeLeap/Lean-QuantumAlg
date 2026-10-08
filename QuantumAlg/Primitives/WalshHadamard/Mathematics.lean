/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.WalshHadamard.Uniform
public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Primitives.WalshHadamard.Uniform
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Components.Kets
import all QuantumAlg.Components.Gates.Operator
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.Fin

/-!
# Walsh-Hadamard matrix mathematics

The original parity signs and normalized transform describe the mathematical
operator independently of its native gate implementation
[dW19, qcnotes.tex:1005-1006]. The Boolean oracle type is a mathematical function;
its actual query access must be declared separately by an executable client.
-/

namespace QuantumAlg.WalshHadamard

open NormalizedVector Gate

noncomputable section

variable {n : Nat}

/-- A Boolean oracle on `2^n` input labels. -/
public abbrev Oracle (n : ℕ) : Type := Fin (2 ^ n) → Bool

/-- The phase `(-1)^{f x}`, written as a complex scalar. -/
def phaseSign (f : Oracle n) (x : Fin (2 ^ n)) : ℂ :=
  if f x then -1 else 1

/-! ### The Walsh-Hadamard transform -/

/-- The bit of a basis label used in the Walsh-Hadamard character. The bit
order only affects nonzero rows; the zero row used by Deutsch-Jozsa is
independent of it. -/
public def bit (x : Fin (2 ^ n)) (k : Fin n) : Bool := x.val.testBit k.val

/-- Parity of the bitwise inner product of two basis labels. -/
public def dotParity (x y : Fin (2 ^ n)) : Bool :=
  Odd ((Finset.univ.filter fun k : Fin n => bit x k && bit y k).card)

/-- The Walsh-Hadamard sign `(-1)^{x · y}`. -/
public def walshSign (x y : Fin (2 ^ n)) : ℂ := if dotParity x y then -1 else 1

@[simp]
theorem walshSign_zero_left (x : Fin (2 ^ n)) :
    walshSign (0 : Fin (2 ^ n)) x = 1 := by
  unfold walshSign dotParity bit
  simp

@[simp]
theorem walshSign_zero_right (x : Fin (2 ^ n)) :
    walshSign x (0 : Fin (2 ^ n)) = 1 := by
  unfold walshSign dotParity bit
  simp

theorem dotParity_comm (x y : Fin (2 ^ n)) : dotParity x y = dotParity y x := by
  have hset : (Finset.univ.filter fun k : Fin n => bit x k && bit y k)
      = Finset.univ.filter fun k : Fin n => bit y k && bit x k := by
    apply Finset.filter_congr
    intro k _
    rw [Bool.and_comm]
  unfold dotParity
  rw [hset]

@[simp]
theorem bit_prodEquiv_zero (left : Fin (2 ^ n)) (right : Fin (2 ^ 1)) :
    bit (prodEquiv (m := n) (n := 1) (left, right)) 0 = bit right 0 := by
  exact prodEquiv_testBit_right left right 0

@[simp]
theorem bit_prodEquiv_succ (left : Fin (2 ^ n)) (right : Fin (2 ^ 1))
    (k : Fin n) :
    bit (prodEquiv (m := n) (n := 1) (left, right)) k.succ = bit left k := by
  simpa [bit, Nat.add_comm] using prodEquiv_testBit_left left right k

@[simp]
private theorem decide_even_eq_not_decide_odd (value : Nat) :
    decide (Even value) = !decide (Odd value) := by
  rw [← decide_not, decide_eq_decide, Nat.not_odd_iff_even]

/-- Appending one low qubit adds its Boolean product to the Walsh inner-product
parity. This pins the analytical bit convention to the structural tensor
convention used by `UnitaryCircuit.tensorQubits`. -/
theorem dotParity_prodEquiv (leftX leftY : Fin (2 ^ n))
    (rightX rightY : Fin (2 ^ 1)) :
    dotParity (prodEquiv (m := n) (n := 1) (leftX, rightX))
        (prodEquiv (m := n) (n := 1) (leftY, rightY)) =
      (dotParity leftX leftY ^^
        Bool.and (bit rightX 0) (bit rightY 0)) := by
  unfold dotParity
  rw [Fin.card_filter_univ_succ]
  simp only [bit_prodEquiv_zero, bit_prodEquiv_succ]
  cases hx : bit rightX 0 <;> cases hy : bit rightY 0 <;>
    simp [Nat.odd_add_one]

@[simp]
theorem dotParity_one (x y : Fin (2 ^ 1)) :
    dotParity x y = Bool.and (bit x 0) (bit y 0) := by
  unfold dotParity
  rw [Fin.card_filter_univ_succ]
  cases hx : bit x 0 <;> cases hy : bit y 0 <;> simp

/-- The Walsh character of a big-endian product label factors into the
characters of its high and low components. -/
theorem walshSign_prodEquiv (leftX leftY : Fin (2 ^ n))
    (rightX rightY : Fin (2 ^ 1)) :
    walshSign (prodEquiv (m := n) (n := 1) (leftX, rightX))
        (prodEquiv (m := n) (n := 1) (leftY, rightY)) =
      walshSign leftX leftY * walshSign rightX rightY := by
  unfold walshSign
  rw [dotParity_prodEquiv, dotParity_one]
  cases hleft : dotParity leftX leftY <;>
    cases hright : Bool.and (bit rightX 0) (bit rightY 0) <;>
    simp

theorem walshSign_comm (x y : Fin (2 ^ n)) : walshSign x y = walshSign y x := by
  unfold walshSign
  rw [dotParity_comm]

@[simp]
public theorem walshSign_mul_self (x y : Fin (2 ^ n)) :
    walshSign x y * walshSign x y = 1 := by
  unfold walshSign
  by_cases h : dotParity x y <;> simp [h]

@[simp]
theorem star_walshSign (x y : Fin (2 ^ n)) :
    star (walshSign x y) = walshSign x y := by
  unfold walshSign
  by_cases h : dotParity x y <;> simp [h]

@[simp]
theorem norm_walshSign (x y : Fin (2 ^ n)) : ‖walshSign x y‖ = 1 := by
  unfold walshSign
  by_cases h : dotParity x y <;> simp [h]

/-! ### Walsh-character orthogonality -/

/-- Flip bit `k` of a basis label. -/
def flipBit (x : Fin (2 ^ n)) (k : Fin n) : Fin (2 ^ n) :=
  ⟨x.val ^^^ 2 ^ k.val,
    Nat.xor_lt_two_pow x.isLt (Nat.pow_lt_pow_right one_lt_two k.isLt)⟩

theorem bit_flipBit (x : Fin (2 ^ n)) (k k' : Fin n) :
    bit (flipBit x k) k' = (bit x k' ^^ decide (k = k')) := by
  change (x.val ^^^ 2 ^ k.val).testBit k'.val = (bit x k' ^^ decide (k = k'))
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  congr 1
  rw [decide_eq_decide]
  exact Fin.val_inj

theorem flipBit_flipBit (x : Fin (2 ^ n)) (k : Fin n) :
    flipBit (flipBit x k) k = x := by
  unfold flipBit
  ext
  simp

theorem flipBit_ne (x : Fin (2 ^ n)) (k : Fin n) : flipBit x k ≠ x := by
  intro h
  have hb := congrArg (fun y : Fin (2 ^ n) => bit y k) h
  simp [bit_flipBit] at hb

/-- Flipping bit `k` of `x` toggles the parity `x · z` exactly when bit `k`
of `z` is set. -/
theorem dotParity_flipBit (x z : Fin (2 ^ n)) (k : Fin n) :
    dotParity (flipBit x k) z = (dotParity x z ^^ bit z k) := by
  unfold dotParity
  cases hz : bit z k
  · rw [Bool.xor_false]
    have hset : (Finset.univ.filter fun k' : Fin n => bit (flipBit x k) k' && bit z k')
        = Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
      apply Finset.filter_congr
      intro k' _
      rcases eq_or_ne k k' with rfl | hk
      · simp [bit_flipBit, hz]
      · simp [bit_flipBit, hk]
    rw [hset]
  · rw [Bool.xor_true]
    by_cases hx : bit x k
    · have hmem : k ∈ Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
        simp [hx, hz]
      have hset : (Finset.univ.filter fun k' : Fin n => bit (flipBit x k) k' && bit z k')
          = (Finset.univ.filter fun k' : Fin n => bit x k' && bit z k').erase k := by
        ext k'
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
        rcases eq_or_ne k' k with rfl | hk
        · simp [bit_flipBit, hx]
        · simp [bit_flipBit, hk, Ne.symm hk]
      rw [hset, ← decide_not, decide_eq_decide,
        ← Finset.card_erase_add_one hmem, Nat.odd_add_one, not_not]
    · have hnot : k ∉ Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
        simp [hx]
      have hset : (Finset.univ.filter fun k' : Fin n => bit (flipBit x k) k' && bit z k')
          = insert k (Finset.univ.filter fun k' : Fin n => bit x k' && bit z k') := by
        ext k'
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
        rcases eq_or_ne k' k with rfl | hk
        · simp [bit_flipBit, hx, hz]
        · simp [bit_flipBit, hk, Ne.symm hk]
      rw [hset, Finset.card_insert_of_notMem hnot, ← decide_not,
        decide_eq_decide, Nat.odd_add_one]

/-- Two distinct labels differ at some bit. -/
theorem exists_bit_ne {y s : Fin (2 ^ n)} (h : y ≠ s) :
    ∃ k : Fin n, bit y k ≠ bit s k := by
  by_contra hall
  push Not at hall
  refine h (Fin.val_injective (Nat.eq_of_testBit_eq fun i => ?_))
  by_cases hi : i < n
  · exact hall ⟨i, hi⟩
  · push Not at hi
    have hy : y.val < 2 ^ i := lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by norm_num) hi)
    have hs : s.val < 2 ^ i := lt_of_lt_of_le s.isLt (Nat.pow_le_pow_right (by norm_num) hi)
    rw [Nat.testBit_lt_two_pow hy, Nat.testBit_lt_two_pow hs]

private theorem if_xor_true (a : Bool) :
    (if (a ^^ true) = true then (-1 : ℂ) else 1) = -(if a = true then -1 else 1) := by
  cases a <;> simp

/-- Flipping a bit on which `y` and `s` disagree negates the product of their
Walsh signs. -/
theorem walshSign_mul_walshSign_flipBit {y s : Fin (2 ^ n)} {k : Fin n}
    (hk : bit y k ≠ bit s k) (x : Fin (2 ^ n)) :
    walshSign y (flipBit x k) * walshSign s (flipBit x k)
      = -(walshSign y x * walshSign s x) := by
  unfold walshSign
  simp only [dotParity_comm y (flipBit x k), dotParity_comm s (flipBit x k),
    dotParity_flipBit, dotParity_comm x y, dotParity_comm x s]
  cases hy : bit y k <;> cases hs : bit s k
  · exact absurd (hy.trans hs.symm) hk
  · rw [Bool.xor_false, if_xor_true]
    ring
  · rw [Bool.xor_false, if_xor_true]
    ring
  · exact absurd (hy.trans hs.symm) hk

/-- Walsh-character orthogonality: for `y ≠ s` the signed sum over all basis
labels cancels in pairs under the bit-flip involution. -/
theorem sum_walshSign_mul_walshSign {y s : Fin (2 ^ n)} (h : y ≠ s) :
    ∑ x, walshSign y x * walshSign s x = 0 := by
  obtain ⟨k, hk⟩ := exists_bit_ne h
  refine Finset.sum_involution (fun x _ => flipBit x k)
    (fun x _ => ?_) (fun x _ _ => flipBit_ne x k)
    (fun x _ => Finset.mem_univ _) (fun x _ => flipBit_flipBit x k)
  rw [walshSign_mul_walshSign_flipBit hk x]
  ring

theorem sum_walshSign_mul_walshSign_eq (y s : Fin (2 ^ n)) :
    ∑ x, walshSign y x * walshSign s x =
      if y = s then ((2 ^ n : ℕ) : ℂ) else 0 := by
  by_cases hys : y = s
  · subst hys
    rw [if_pos rfl]
    simp only [walshSign_mul_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  · rw [if_neg hys, sum_walshSign_mul_walshSign hys]

@[simp]
theorem invSqrtCard_mul_self (n : ℕ) :
    invSqrtCard n * invSqrtCard n = (((2 ^ n : ℕ) : ℂ)⁻¹) := by
  rw [invSqrtCard, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ))]
  norm_num

/-- The Walsh normalization factors multiplicatively when one low qubit is
appended to the register. -/
theorem invSqrtCard_succ (n : ℕ) :
    invSqrtCard (n + 1) = invSqrtCard n * invSqrt2 := by
  rw [invSqrtCard, invSqrtCard, invSqrt2]
  rw [pow_succ, Nat.cast_mul, Real.sqrt_mul (by positivity)]
  norm_num
  ac_rfl

/-- A Boolean phase has unit norm. -/
@[simp]
theorem norm_phaseSign (f : Oracle n) (x : Fin (2 ^ n)) :
    ‖phaseSign f x‖ = 1 := by
  unfold phaseSign
  by_cases h : f x <;> simp [h]

/-- Certified metadata-free Walsh-Hadamard operator. -/
public def hadamardLayerOperator (n : ℕ) : UnitaryOperator (Qubits n) :=
  let op : HilbertOperator (Qubits n) :=
    fun y x => invSqrtCard n * walshSign y x
  UnitaryOperator.ofMatrix op
    (by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      ext y s
      rw [Matrix.mul_apply]
      calc
        ∑ x, (invSqrtCard n * walshSign y x) *
              star (invSqrtCard n * walshSign s x)
            = ∑ x, (invSqrtCard n * invSqrtCard n) *
                (walshSign y x * walshSign s x) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [star_mul, star_invSqrtCard, star_walshSign]
              ring
        _ = (invSqrtCard n * invSqrtCard n) *
              ∑ x, walshSign y x * walshSign s x := by
              rw [Finset.mul_sum]
        _ = (((2 ^ n : ℕ) : ℂ)⁻¹) *
              (if y = s then ((2 ^ n : ℕ) : ℂ) else 0) := by
              rw [invSqrtCard_mul_self, sum_walshSign_mul_walshSign_eq]
        _ = (1 : HilbertOperator (Qubits n)) y s := by
              by_cases hys : y = s
              · subst s
                rw [if_pos rfl, Matrix.one_apply_eq]
                exact inv_mul_cancel₀
                  (Nat.cast_ne_zero.mpr (pow_ne_zero n two_ne_zero))
              · rw [if_neg hys, Matrix.one_apply_ne hys, mul_zero])

@[simp]
theorem hadamardLayerOperator_apply (n : ℕ) (y x : Fin (2 ^ n)) :
    hadamardLayerOperator n y x = invSqrtCard n * walshSign y x := rfl



end

end QuantumAlg.WalshHadamard
