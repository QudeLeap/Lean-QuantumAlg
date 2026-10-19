/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Blocks
public import QuantumAlg.Components.Kets
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
public import QuantumAlg.Primitives.WalshHadamard.Uniform
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
import all QuantumAlg.Primitives.WalshHadamard.Uniform
import all QuantumAlg.Util.FinPow
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Arithmetic

/-!
# Tensor form of finite-cyclic residual blocks

Aligned interval blocks split into a fixed high label, a zero source qubit,
and a uniform low suffix.  These identities connect the arithmetic block
invariant to actual separated-wire native gates.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderExpansion.PositiveGapExpansion

noncomputable section

variable {N : Nat}

private lemma prodEquiv_value {leftWidth rightWidth : Nat}
    (left : Fin (2 ^ leftWidth)) (right : Fin (2 ^ rightWidth)) :
    (prodEquiv (m := leftWidth) (n := rightWidth) (left, right)).val =
      right.val + 2 ^ rightWidth * left.val := rfl

/-- The computational-basis vector at a binary label of the given width. -/
public abbrev basisKetVec {width : Nat} (index : Fin (2 ^ width)) :
    HilbertVector (Qubits width) :=
  (NormalizedVector.ket (R := Qubits width) index).vec

@[simp] public lemma basisKetVec_zero_one :
    basisKetVec (0 : Fin (2 ^ 1)) =
      (NormalizedVector.ket0 : HilbertVector (Qubits 1)) :=
  rfl

/-- The high prefix of an aligned residual block, after discarding its zero
source bit and all lower free positions. -/
@[expose] public def residualHigh (b : PositiveGapExpansion N)
    (m : Fin (b.gaps + 1)) : Nat :=
  b.tailMass m / 2 ^ (b.ell m + 1)

public lemma tailMass_eq_residualHigh_mul (b : PositiveGapExpansion N)
    (m : Fin (b.gaps + 1)) :
    b.tailMass m = 2 ^ (b.ell m + 1) * b.residualHigh m := by
  unfold residualHigh
  rw [Nat.mul_comm, Nat.div_mul_cancel (b.pow_succ_ell_dvd_tailMass m)]

public lemma ell_lt_width (b : PositiveGapExpansion N)
    (m : Fin (b.gaps + 1)) : b.ell m < b.width := by
  unfold width last
  have hle : b.ell m ≤ b.ell (Fin.last b.gaps) :=
    b.ell_strict.monotone (Fin.le_last m)
  omega

private lemma first_lt_width (b : PositiveGapExpansion N) : b.first < b.width := by
  unfold first
  exact b.ell_lt_width (0 : Fin (b.gaps + 1))

public lemma residualHigh_lt (b : PositiveGapExpansion N)
    (m : Fin (b.gaps + 1)) :
    b.residualHigh m < 2 ^ (b.width - b.ell m - 1) := by
  have hbit : b.ell m < b.width := b.ell_lt_width m
  have hpow :
      2 ^ b.width =
        2 ^ (b.width - b.ell m - 1) * 2 ^ (b.ell m + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hproduct :
      b.residualHigh m * 2 ^ (b.ell m + 1) <
        2 ^ (b.width - b.ell m - 1) * 2 ^ (b.ell m + 1) := by
    calc
      b.residualHigh m * 2 ^ (b.ell m + 1) = b.tailMass m := by
        unfold residualHigh
        exact Nat.div_mul_cancel (b.pow_succ_ell_dvd_tailMass m)
      _ < 2 ^ b.width := b.tailMass_lt_pow_width m
      _ = 2 ^ (b.width - b.ell m - 1) * 2 ^ (b.ell m + 1) := hpow
  exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mp hproduct

/-- The fixed high-coordinate label of a residual support block. -/
@[expose] public def residualHighLabel (b : PositiveGapExpansion N)
    (m : Fin (b.gaps + 1)) :
    Fin (2 ^ (b.width - b.ell m - 1)) :=
  ⟨b.residualHigh m, b.residualHigh_lt m⟩

@[simp]
public lemma residualHighLabel_val (b : PositiveGapExpansion N)
    (m : Fin (b.gaps + 1)) : (b.residualHighLabel m).val = b.residualHigh m :=
  rfl

/-- The interval support of a residual block is exactly its high fixed prefix,
its own zero source bit, and arbitrary lower coordinates.  This is the
coordinate form that connects the source arithmetic to actual tensor-placed
gates. -/
private lemma residualSupport_iff_tensor_bits (b : PositiveGapExpansion N)
    (m : Fin (b.gaps + 1))
    (high : Fin (2 ^ (b.width - b.ell m - 1)))
    (bit : Fin (2 ^ 1)) (low : Fin (2 ^ b.ell m)) :
    b.residualSupport m
        (prodEquiv
          (m := b.width - b.ell m - 1) (n := 1 + b.ell m)
          (high, prodEquiv (m := 1) (n := b.ell m) (bit, low))).val ↔
      high = b.residualHighLabel m ∧ bit = 0 := by
  let q := 2 ^ b.ell m
  let p := 2 ^ (1 + b.ell m)
  let r := b.residualHigh m
  let lower : Fin (2 ^ (1 + b.ell m)) :=
    prodEquiv (m := 1) (n := b.ell m) (bit, low)
  let address : Fin (2 ^ ((b.width - b.ell m - 1) + (1 + b.ell m))) :=
    prodEquiv (m := b.width - b.ell m - 1) (n := 1 + b.ell m)
      (high, lower)
  have hqle : q ≤ p := by
    dsimp [q, p]
    rw [show 1 + b.ell m = b.ell m + 1 by omega, pow_succ]
    omega
  have htail : b.tailMass m = p * r := by
    dsimp [p, r]
    simpa [Nat.add_comm] using b.tailMass_eq_residualHigh_mul m
  have haddress : address.val = lower.val + p * high.val := by
    dsimp [address, p]
    exact prodEquiv_value high lower
  have hlower : lower.val = low.val + q * bit.val := by
    dsimp [lower, q]
    exact prodEquiv_value bit low
  have hquotHigh : address.val / p = high.val := by
    dsimp [address, p]
    simpa only [Equiv.symm_apply_apply] using
      (prodEquiv_symm_fst_val
        (m := b.width - b.ell m - 1) (n := 1 + b.ell m)
        (prodEquiv
          (m := b.width - b.ell m - 1) (n := 1 + b.ell m)
          (high, lower))).symm
  have hquotBit : lower.val / q = bit.val := by
    dsimp [lower, q]
    simpa only [Equiv.symm_apply_apply] using
      (prodEquiv_symm_fst_val (m := 1) (n := b.ell m)
        (prodEquiv (m := 1) (n := b.ell m) (bit, low))).symm
  change b.residualSupport m address.val ↔ _
  constructor
  · rintro ⟨hlo, hhi⟩
    have hdiv : address.val / p = r := by
      apply Nat.div_eq_of_lt_le
      · simpa [htail, Nat.mul_comm] using hlo
      · calc
          address.val < b.tailMass m + q := hhi
          _ ≤ b.tailMass m + p := Nat.add_le_add_left hqle _
          _ = (r + 1) * p := by rw [htail]; ring
    have hhighval : high.val = r := hquotHigh.symm.trans hdiv
    have hhigh : high = b.residualHighLabel m := by
      apply Fin.ext
      simpa [r] using hhighval
    have hlowerlt : lower.val < q := by
      have hrewritten : lower.val + p * r < p * r + q := by
        simpa [haddress, hhighval, htail] using hhi
      omega
    have hbitval : bit.val = 0 := by
      calc
        bit.val = lower.val / q := hquotBit.symm
        _ = 0 := Nat.div_eq_of_lt hlowerlt
    exact ⟨hhigh, Fin.ext hbitval⟩
  · rintro ⟨hhigh, hbit⟩
    subst high
    subst bit
    have haddress' : address.val = b.tailMass m + low.val := by
      calc
        address.val = lower.val + p * (b.residualHighLabel m).val := haddress
        _ = low.val + p * r := by
          rw [hlower]
          simp [residualHighLabel_val, r]
        _ = b.tailMass m + low.val := by rw [htail]; omega
    unfold residualSupport
    constructor
    · rw [haddress']
      omega
    · rw [haddress']
      exact Nat.add_lt_add_left low.isLt _

/-- The raw interval definition of a residual block is equal to its aligned
tensor presentation: a fixed high prefix, a zero source bit, and an actual
low Walsh-uniform block. -/
public lemma residualBlock_tensor_factor (b : PositiveGapExpansion N)
    (m : Fin (b.gaps + 1)) :
    b.residualBlock m =
      UnitaryCircuit.castQubitWidthVec (by
        have hbit : b.ell m < b.width := b.ell_lt_width m
        omega : (b.width - b.ell m - 1) + (1 + b.ell m) = b.width)
        (HilbertVector.tensor
          (basisKetVec (b.residualHighLabel m))
          (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
            (WalshHadamard.uniformState (b.ell m) :
              HilbertVector (Qubits (b.ell m))))) := by
  have hbit : b.ell m < b.width := b.ell_lt_width m
  have hwidth : (b.width - b.ell m - 1) + (1 + b.ell m) = b.width := by
    omega
  apply WithLp.ofLp_injective
  funext index
  rw [UnitaryCircuit.castQubitWidthVec_apply]
  generalize hsourceIndex : UnitaryCircuit.castQubitWidthIndex hwidth.symm index = sourceIndex
  have hindexVal : index.val = sourceIndex.val := by
    rw [← hsourceIndex]
    simp only [UnitaryCircuit.castQubitWidthIndex_val]
  rcases (prodEquiv
    (m := b.width - b.ell m - 1) (n := 1 + b.ell m)).surjective sourceIndex with
    ⟨⟨high, lower⟩, rfl⟩
  rcases (prodEquiv (m := 1) (n := b.ell m)).surjective lower with
    ⟨⟨bit, low⟩, rfl⟩
  rw [residualBlock_apply]
  change (if b.tailMass m ≤ index.val ∧
      index.val < b.tailMass m + 2 ^ b.ell m then
      WalshHadamard.invSqrtCard (b.ell m) else 0) = _
  rw [hindexVal]
  simp only [show
    (b.tailMass m ≤
          (prodEquiv
            (m := b.width - b.ell m - 1) (n := 1 + b.ell m)
            (high, prodEquiv (m := 1) (n := b.ell m) (bit, low))).val ∧
        (prodEquiv
          (m := b.width - b.ell m - 1) (n := 1 + b.ell m)
          (high, prodEquiv (m := 1) (n := b.ell m) (bit, low))).val <
            b.tailMass m + 2 ^ b.ell m) ↔
      high = b.residualHighLabel m ∧ bit = 0 by
        simpa only [residualSupport] using
          b.residualSupport_iff_tensor_bits m high bit low]
  simp only [HilbertVector.tensor_apply_prod]
  by_cases hhigh : high = b.residualHighLabel m
  · subst high
    fin_cases bit <;>
      simp [basisKetVec, NormalizedVector.ket0_apply, NormalizedVector.ket_apply,
        WalshHadamard.uniformState_apply]
  · simp [basisKetVec, NormalizedVector.ket0_apply,
      NormalizedVector.ket_apply, hhigh]

private def betweenMass (b : PositiveGapExpansion N)
    (left right : Fin (b.gaps + 1)) : Nat :=
  ∑ index : Fin (b.gaps + 1),
    if left.val < index.val ∧ index.val < right.val then
      2 ^ b.ell index else 0

private def gapLowerMass (b : PositiveGapExpansion N)
    (left right : Fin (b.gaps + 1)) : Nat :=
  ∑ index : Fin (b.gaps + 1),
    if left.val ≤ index.val ∧ index.val < right.val then
      2 ^ b.ell index else 0

private lemma filtered_powers_lt_pow (b : PositiveGapExpansion N)
    (predicate : Fin (b.gaps + 1) → Prop) [DecidablePred predicate]
    (upper : Nat) (below : ∀ index, predicate index → b.ell index < upper) :
    (∑ index : Fin (b.gaps + 1),
      if predicate index then 2 ^ b.ell index else 0) < 2 ^ upper := by
  classical
  rw [← Finset.sum_filter]
  rw [← Finset.sum_image b.ell_strict.injective.injOn]
  exact Nat.geomSum_lt (m := 2)
    (s := (Finset.univ.filter predicate).image b.ell) (n := upper) (by omega)
    (by
      intro exponent member
      rcases Finset.mem_image.mp member with ⟨index, indexMember, rfl⟩
      exact below index (Finset.mem_filter.mp indexMember).2)

private lemma gapLowerMass_lt_pow (b : PositiveGapExpansion N)
    {left right : Fin (b.gaps + 1)} (_before : left.val < right.val) :
    b.gapLowerMass left right < 2 ^ b.ell right := by
  unfold gapLowerMass
  apply b.filtered_powers_lt_pow
    (fun index => left.val ≤ index.val ∧ index.val < right.val) (b.ell right)
  intro index bounded
  exact b.ell_strict bounded.2

private lemma tailMass_eq_tailMass_add_current_add_between
    (b : PositiveGapExpansion N) {left right : Fin (b.gaps + 1)}
    (before : left.val < right.val) :
    b.tailMass left = b.tailMass right + 2 ^ b.ell right +
      b.betweenMass left right := by
  have current : 2 ^ b.ell right = ∑ index : Fin (b.gaps + 1),
      if index = right then 2 ^ b.ell index else 0 := by simp
  rw [current]
  unfold tailMass betweenMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  by_cases aboveLeft : left.val < index.val
  · by_cases belowRight : index.val < right.val
    · have notAboveRight : ¬ right.val < index.val := by omega
      have notCurrent : index ≠ right := by
        intro equal
        subst index
        exact (Nat.lt_irrefl right.val) belowRight
      simp [aboveLeft, belowRight, notAboveRight, notCurrent]
    · have rightLe : right.val ≤ index.val := Nat.le_of_not_gt belowRight
      by_cases currentIndex : index = right
      · subst index
        simp [before]
      · have aboveRight : right.val < index.val := by
          apply Nat.lt_of_le_of_ne rightLe
          intro equal
          apply currentIndex
          exact Fin.ext equal.symm
        simp [aboveLeft, belowRight, aboveRight, currentIndex]
  · have notAboveRight : ¬ right.val < index.val := by omega
    have notCurrent : index ≠ right := by
      intro equal
      subst index
      exact aboveLeft before
    simp [aboveLeft, notAboveRight, notCurrent]

private lemma gapLowerMass_eq_betweenMass_add_current
    (b : PositiveGapExpansion N) {left right : Fin (b.gaps + 1)}
    (before : left.val < right.val) :
    b.gapLowerMass left right = b.betweenMass left right + 2 ^ b.ell left := by
  have current : 2 ^ b.ell left = ∑ index : Fin (b.gaps + 1),
      if index = left then 2 ^ b.ell index else 0 := by simp
  rw [current]
  unfold gapLowerMass betweenMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  by_cases currentIndex : index = left
  · subst index
    simp [before]
  · by_cases between : left.val < index.val ∧ index.val < right.val
    · have inside : left.val ≤ index.val ∧ index.val < right.val :=
        ⟨Nat.le_of_lt between.1, between.2⟩
      simp [currentIndex, between, inside]
    · have notInside : ¬ (left.val ≤ index.val ∧ index.val < right.val) := by
        intro inside
        apply between
        constructor
        · exact lt_of_le_of_ne inside.1 (by
            intro equal
            apply currentIndex
            exact Fin.ext equal.symm)
        · exact inside.2
      have notInsideFin : ¬ (left ≤ index ∧ index < right) := by
        intro inside
        apply notInside
        exact ⟨by simpa using inside.1, by simpa using inside.2⟩
      have notBetweenFin : ¬ (left < index ∧ index < right) := by
        intro inside
        apply between
        exact ⟨by simpa using inside.1, by simpa using inside.2⟩
      simp [currentIndex, notBetweenFin, notInsideFin]

private lemma testBit_true_of_pow_mul_odd_add_lt
    (bit quotient remainder : Nat) (remainderSmall : remainder < 2 ^ bit) :
    (2 ^ bit * (2 * quotient + 1) + remainder).testBit bit = true := by
  have powerPositive : 0 < 2 ^ bit := Nat.two_pow_pos _
  have quotientValue :
      (2 ^ bit * (2 * quotient + 1) + remainder) / 2 ^ bit =
        2 * quotient + 1 := by
    calc
      (2 ^ bit * (2 * quotient + 1) + remainder) / 2 ^ bit =
          (remainder + 2 ^ bit * (2 * quotient + 1)) / 2 ^ bit := by
            rw [Nat.add_comm]
      _ = remainder / 2 ^ bit + (2 * quotient + 1) :=
          Nat.add_mul_div_left _ _ powerPositive
      _ = 2 * quotient + 1 := by
          rw [Nat.div_eq_of_lt remainderSmall, zero_add]
  have odd : Nat.bodd (2 * quotient + 1) = true := by
    rw [show 2 * quotient + 1 = Nat.succ (2 * quotient) by omega,
      Nat.bodd_succ, Nat.bodd_mul, Nat.bodd_two]
    simp
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, quotientValue]
  rw [← Nat.bodd_eq_one_and_ne_zero]
  exact odd

/-- Every address in an earlier residual block has every later source bit
set, so later open controls are inactive on that block. -/
public lemma residualSupport_testBit_true_of_lt (b : PositiveGapExpansion N)
    {left right : Fin (b.gaps + 1)} (before : left.val < right.val)
    {index : Nat} (support : b.residualSupport left index) :
    index.testBit (b.ell right) = true := by
  rcases support with ⟨lower, upper⟩
  let offset := index - b.tailMass left
  have indexEq : index = b.tailMass left + offset := by
    dsimp [offset]
    exact (Nat.add_sub_of_le lower).symm
  have offsetSmall : offset < 2 ^ b.ell left := by
    dsimp [offset]
    omega
  have tailSplit := b.tailMass_eq_tailMass_add_current_add_between before
  have gapSmall := b.gapLowerMass_lt_pow before
  have gapSplit := b.gapLowerMass_eq_betweenMass_add_current before
  have remainderSmall : b.betweenMass left right + offset < 2 ^ b.ell right := by
    calc
      b.betweenMass left right + offset <
          b.betweenMass left right + 2 ^ b.ell left :=
        Nat.add_lt_add_left offsetSmall _
      _ = b.gapLowerMass left right := gapSplit.symm
      _ < 2 ^ b.ell right := gapSmall
  have normalForm : index =
      2 ^ b.ell right * (2 * b.residualHigh right + 1) +
        (b.betweenMass left right + offset) := by
    rw [indexEq, tailSplit, b.tailMass_eq_residualHigh_mul]
    rw [pow_succ]
    ring
  rw [normalForm]
  exact testBit_true_of_pow_mul_odd_add_lt
    (b.ell right) (b.residualHigh right)
    (b.betweenMass left right + offset) remainderSmall

/-- Enlarging the binary register adds only an all-zero high prefix to every
aligned residual block. -/
public lemma residualBlockAt_eq_padding (b : PositiveGapExpansion N)
    (registerWidth : Nat) (fits : b.width ≤ registerWidth)
    (source : Fin (b.gaps + 1)) :
    b.residualBlockAt registerWidth source =
      UnitaryCircuit.castQubitWidthVec (Nat.sub_add_cancel fits)
        (HilbertVector.tensor
          (basisKetVec (0 : Fin (2 ^ (registerWidth - b.width))))
          (b.residualBlock source)) := by
  let same := Nat.sub_add_cancel fits
  apply WithLp.ofLp_injective
  funext address
  rw [UnitaryCircuit.castQubitWidthVec_apply]
  generalize sourceEq : UnitaryCircuit.castQubitWidthIndex same.symm address = sourceAddress
  have addressVal : address.val = sourceAddress.val := by
    rw [← sourceEq]
    simp only [UnitaryCircuit.castQubitWidthIndex_val]
  obtain ⟨⟨high, low⟩, rfl⟩ :=
    (prodEquiv (m := registerWidth - b.width) (n := b.width)).surjective sourceAddress
  rw [HilbertVector.tensor_apply_prod, residualBlockAt_apply, residualBlock_apply]
  by_cases highZero : high = 0
  · subst high
    have lowVal :
        address.val = low.val := by
      rw [addressVal]
      simp [prodEquiv_value]
    rw [lowVal]
    simp [basisKetVec, NormalizedVector.ket_apply]
  · have highPositive : 1 ≤ high.val := by
      exact Nat.one_le_iff_ne_zero.mpr (fun zero => highZero (Fin.ext zero))
    have addressLarge : 2 ^ b.width ≤ address.val := by
      rw [addressVal]
      change 2 ^ b.width ≤ low.val + 2 ^ b.width * high.val
      have scaled : 2 ^ b.width ≤ 2 ^ b.width * high.val := by
        simpa using Nat.mul_le_mul_left (2 ^ b.width) highPositive
      omega
    have outside : ¬ b.residualSupport source address.val := by
      intro support
      have blockBound := b.tailMass_add_current_le source
      have orderFits := b.fits_proof
      have addressBelow : address.val < 2 ^ b.width :=
        (support.2.trans_le blockBound).trans_le orderFits
      exact (Nat.not_lt_of_ge addressLarge) addressBelow
    rw [if_neg outside]
    simp [basisKetVec, NormalizedVector.ket_apply, highZero]

end

end QuantumAlg.FiniteCyclicDLP.OrderExpansion.PositiveGapExpansion
