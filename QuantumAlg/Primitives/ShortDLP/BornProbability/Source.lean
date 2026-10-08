/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.PMF
import all QuantumAlg.Primitives.ShortDLP.Oracle.Mathematics
import all QuantumAlg.Primitives.ShortDLP.Measurement
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Util.Complex
import all QuantumAlg.Util.NumberTheory.CenteredResidue
import all QuantumAlg.Util.Real.ReciprocalSquareTail
import Mathlib.Algebra.Order.Chebyshev

/-!
# Source Fourier fibers for short discrete logarithms

These finite sums, interval identities, and exact source formulas depend on
register mathematics and the specified group permutation. Their connection
to the actual declared circuit is proved separately.
-/

section

namespace QuantumAlg

open NormalizedVector
open scoped BigOperators

noncomputable section

namespace ShortDLP
namespace BornProbability

/-- Raw state after uniform preparation and the group-operation query, before
the two inverse-QFT readouts. -/
def postOracleVec {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) : HilbertVector (Qubits (totalQubits params)) :=
  WithLp.toLp 2 fun basis =>
    let triple := (tripleEquiv params).symm basis
    if triple.2 = encodeUnit encoding
        (oracleValue g x triple.1.1.val triple.1.2.val) then
      WalshHadamard.invSqrtCard (firstBits params) *
        WalshHadamard.invSqrtCard params.ell
    else
      0

/-- Source-shaped basis amplitude expressed as the double inverse-QFT sum over
the encoded group-operation fibers. Its execution bridge is separate. -/
def circuitAmplitude {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (y : Fin (2 ^ params.workspaceBits)) : Complex :=
  ∑ a : Fin (2 ^ firstBits params),
    ∑ b : Fin (2 ^ params.ell),
      star (invSqrtN (firstBits params) *
          ω (firstBits params) ^ (a.val * j.val)) *
        star (invSqrtN params.ell *
          ω params.ell ^ (b.val * k.val)) *
        if y = encodeUnit encoding (oracleValue g x a.val b.val) then
          WalshHadamard.invSqrtCard (firstBits params) *
            WalshHadamard.invSqrtCard params.ell
        else
          0

/-- Common normalization of one complete prepare/query/inverse-QFT amplitude:
one uniform-preparation and one inverse-QFT factor for each exponent register. -/
def fourierNormalization (params : RegisterParameters) : Complex :=
  invSqrtN (firstBits params) * invSqrtN params.ell *
    WalshHadamard.invSqrtCard (firstBits params) *
      WalshHadamard.invSqrtCard params.ell

/-- Squared common normalization in source cardinality form: one reciprocal
factor for preparation and one for inverse QFT on each exponent register. -/
theorem norm_sq_fourierNormalization (params : RegisterParameters) :
    ‖fourierNormalization params‖ ^ 2 =
      ((2 : Real) ^ firstBits params)⁻¹ *
        ((2 : Real) ^ params.ell)⁻¹ *
        ((2 : Real) ^ firstBits params)⁻¹ *
        ((2 : Real) ^ params.ell)⁻¹ := by
  have hWalsh (bits : Nat) :
      ‖WalshHadamard.invSqrtCard bits‖ ^ 2 =
        ((2 : Real) ^ bits)⁻¹ := by
    simp
  calc
    ‖fourierNormalization params‖ ^ 2 =
        ‖invSqrtN (firstBits params)‖ ^ 2 *
          ‖invSqrtN params.ell‖ ^ 2 *
          ‖WalshHadamard.invSqrtCard (firstBits params)‖ ^ 2 *
          ‖WalshHadamard.invSqrtCard params.ell‖ ^ 2 := by
            simp only [fourierNormalization, norm_mul]
            ring
    _ = _ := by
      rw [norm_sq_invSqrtN, norm_sq_invSqrtN, hWalsh, hWalsh]

/-- Source-shaped normalization `2^{-2(m+2ℓ)}` from Eq. (2)'s probability
denominator [E23, arxiv-v5.tex:233-264]. -/
theorem norm_sq_fourierNormalization_source (params : RegisterParameters) :
    ‖fourierNormalization params‖ ^ 2 =
      (((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ := by
  rw [norm_sq_fourierNormalization]
  rw [← mul_inv, ← mul_inv, ← mul_inv]
  congr 1
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 1
  unfold firstBits
  omega

/-- Unnormalized Fourier character sum over one encoded group-value fiber.
This is the finite complex sum that is squared and marginalized in the source
distribution [E23, arxiv-v5.tex:233-257]. -/
def fourierFiberSum {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (y : Fin (2 ^ params.workspaceBits)) : Complex :=
  ∑ a : Fin (2 ^ firstBits params),
    ∑ b : Fin (2 ^ params.ell),
      if y = encodeUnit encoding (oracleValue g x a.val b.val) then
        star (ω (firstBits params) ^ (a.val * j.val)) *
          star (ω params.ell ^ (b.val * k.val))
      else
        0

/-- Fourier character sum over all exponent-register pairs that represent one
fixed integer exponent `e = a-b*secret`. -/
def exponentFiberPhaseSum {params : RegisterParameters}
    (secret : Nat) (exponent : Int)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) : Complex :=
  ∑ a : Fin (2 ^ firstBits params),
    ∑ b : Fin (2 ^ params.ell),
      if oracleExponent secret a.val b.val = exponent then
        star (ω (firstBits params) ^ (a.val * j.val)) *
          star (ω params.ell ^ (b.val * k.val))
      else
        0

/-- Natural frequency governing the geometric character on one exponent
fiber.  This is the source combination `secret * j + 2^m * k`
[E23, arxiv-v5.tex:247-257]. -/
def phaseFrequencyNat {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) : Nat :=
  secret * j.val + 2 ^ params.m * k.val

/-- Integer view of the source Fourier frequency. -/
def phaseFrequency {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) : Int :=
  phaseFrequencyNat secret j k

/-- Signed principal representative of the source Fourier frequency. -/
def centeredPhaseFrequency {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) : Int :=
  NumberTheory.centeredResidue (2 ^ firstBits params)
    (phaseFrequencyNat secret j k)

/-- Quotient block whose modular negation selects the second-register outcome
placing `secret*j + 2^m*k` in the centered `2^m` residue interval. -/
def principalPhaseBlock {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) : Nat :=
  let modulus := 2 ^ params.m
  let value := secret * j.val
  value / modulus + if 2 * (value % modulus) ≤ modulus then 0 else 1

/-- Canonical second-register companion for a first-register outcome.  Its
phase frequency is the centered residue of `secret*j` modulo `2^m`. -/
def principalSecondIndex {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) : Fin (2 ^ params.ell) :=
  ⟨NumberTheory.modularNegation (2 ^ params.ell)
      (principalPhaseBlock secret j),
    NumberTheory.modularNegation_lt (Nat.two_pow_pos params.ell)⟩

/-- The canonical companion realizes exactly the centered `2^m` residue,
including the negative half of the narrow source window. -/
theorem centeredPhaseFrequency_principalSecondIndex
    {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) :
    centeredPhaseFrequency secret j (principalSecondIndex secret j) =
      NumberTheory.centeredResidue (2 ^ params.m) (secret * j.val) := by
  let modulus := 2 ^ params.m
  let secondCard := 2 ^ params.ell
  let period := 2 ^ firstBits params
  let value := secret * j.val
  let residue := value % modulus
  have hmodulusPos : 0 < modulus := by
    exact Nat.two_pow_pos _
  have hsecondPos : 0 < secondCard := by
    exact Nat.two_pow_pos _
  have hperiodEq : period = modulus * secondCard := by
    unfold period modulus secondCard firstBits
    rw [pow_add]
    ac_rfl
  have hperiodPos : 0 < period := by
    rw [hperiodEq]
    exact Nat.mul_pos hmodulusPos hsecondPos
  have hmodulusLePeriod : modulus ≤ period := by
    rw [hperiodEq]
    exact Nat.le_mul_of_pos_right modulus hsecondPos
  have hresidueLt : residue < modulus := by
    exact Nat.mod_lt value hmodulusPos
  have hvalueDecomposition :
      value = modulus * (value / modulus) + residue := by
    exact (Nat.div_add_mod value modulus).symm
  have hcompanionMod :
      (principalPhaseBlock secret j +
          (principalSecondIndex secret j).val) % secondCard = 0 := by
    simpa [principalSecondIndex, secondCard] using
      (NumberTheory.add_modularNegation_mod_eq_zero
        (value := principalPhaseBlock secret j) hsecondPos)
  by_cases hhalf : 2 * residue ≤ modulus
  · have hblock : principalPhaseBlock secret j = value / modulus := by
      simp [principalPhaseBlock, value, modulus, residue, hhalf]
    rw [hblock] at hcompanionMod
    have hdivisible : secondCard ∣
        value / modulus + (principalSecondIndex secret j).val :=
      Nat.dvd_iff_mod_eq_zero.mpr hcompanionMod
    obtain ⟨cofactor, hcofactor⟩ := hdivisible
    have hphaseEq : phaseFrequencyNat secret j
        (principalSecondIndex secret j) =
          period * cofactor + residue := by
      unfold phaseFrequencyNat
      change value + modulus * (principalSecondIndex secret j).val = _
      rw [hvalueDecomposition]
      calc
        modulus * (value / modulus) + residue +
            modulus * (principalSecondIndex secret j).val =
          modulus * (value / modulus +
            (principalSecondIndex secret j).val) + residue := by ring
        _ = modulus * (secondCard * cofactor) + residue := by
          rw [hcofactor]
        _ = period * cofactor + residue := by rw [hperiodEq]; ring
    have hphaseMod : phaseFrequencyNat secret j
        (principalSecondIndex secret j) ≡ residue [MOD period] := by
      rw [hphaseEq]
      exact Nat.ModEq.modulus_mul_add
    have hresidueLtPeriod : residue < period :=
      hresidueLt.trans_le hmodulusLePeriod
    have hhalfPeriod : 2 * residue ≤ period :=
      hhalf.trans hmodulusLePeriod
    calc
      centeredPhaseFrequency secret j (principalSecondIndex secret j) =
          (residue : Int) := by
        unfold centeredPhaseFrequency
        apply NumberTheory.centeredResidue_eq_natCast_of_modEq
          hresidueLtPeriod hhalfPeriod
        simpa [period] using hphaseMod
      _ = NumberTheory.centeredResidue modulus value := by
        symm
        exact NumberTheory.centeredResidue_eq_natCast_of_modEq
          hresidueLt hhalf (Nat.mod_modEq value modulus).symm
      _ = NumberTheory.centeredResidue (2 ^ params.m)
          (secret * j.val) := rfl
  · have hupperHalf : modulus < 2 * residue :=
      Nat.lt_of_not_ge hhalf
    have hblock : principalPhaseBlock secret j = value / modulus + 1 := by
      simp [principalPhaseBlock, value, modulus, residue, hhalf]
    rw [hblock] at hcompanionMod
    have hdivisible : secondCard ∣
        value / modulus + 1 + (principalSecondIndex secret j).val :=
      Nat.dvd_iff_mod_eq_zero.mpr hcompanionMod
    obtain ⟨cofactor, hcofactor⟩ := hdivisible
    have hphaseSum : phaseFrequencyNat secret j
          (principalSecondIndex secret j) + (modulus - residue) =
        period * cofactor := by
      unfold phaseFrequencyNat
      change value + modulus * (principalSecondIndex secret j).val +
          (modulus - residue) = _
      rw [hvalueDecomposition]
      have hresidueAdd : residue + (modulus - residue) = modulus :=
        Nat.add_sub_of_le (Nat.le_of_lt hresidueLt)
      calc
        modulus * (value / modulus) + residue +
              modulus * (principalSecondIndex secret j).val +
            (modulus - residue) =
          modulus * (value / modulus) +
              modulus * (principalSecondIndex secret j).val +
                (residue + (modulus - residue)) := by ac_rfl
        _ = modulus * (value / modulus) +
              modulus * (principalSecondIndex secret j).val + modulus := by
            rw [hresidueAdd]
        _ = modulus * (value / modulus + 1 +
            (principalSecondIndex secret j).val) := by ring
        _ = modulus * (secondCard * cofactor) := by rw [hcofactor]
        _ = period * cofactor := by rw [hperiodEq]; ring
    let upperResidue := period + residue - modulus
    have hupperResidueAdd : upperResidue + (modulus - residue) =
        period := by
      unfold upperResidue
      omega
    have hphaseZero : phaseFrequencyNat secret j
          (principalSecondIndex secret j) + (modulus - residue) ≡
        0 [MOD period] := by
      rw [hphaseSum]
      simp [Nat.ModEq]
    have hupperZero : upperResidue + (modulus - residue) ≡
        0 [MOD period] := by
      rw [hupperResidueAdd]
      simp [Nat.ModEq]
    have hphaseMod : phaseFrequencyNat secret j
        (principalSecondIndex secret j) ≡ upperResidue [MOD period] :=
      Nat.ModEq.add_right_cancel' (modulus - residue)
        (hphaseZero.trans hupperZero.symm)
    have hupperResidueLt : upperResidue < period := by
      unfold upperResidue
      omega
    have hupperResidueHalf : period < 2 * upperResidue := by
      unfold upperResidue
      omega
    calc
      centeredPhaseFrequency secret j (principalSecondIndex secret j) =
          (upperResidue : Int) - period := by
        unfold centeredPhaseFrequency
        apply NumberTheory.centeredResidue_eq_sub_of_modEq
          hupperResidueLt hupperResidueHalf
        simpa [period] using hphaseMod
      _ = (residue : Int) - modulus := by
        unfold upperResidue
        omega
      _ = NumberTheory.centeredResidue modulus value := by
        symm
        exact NumberTheory.centeredResidue_eq_sub_of_modEq
          hresidueLt hupperHalf (Nat.mod_modEq value modulus).symm
      _ = NumberTheory.centeredResidue (2 ^ params.m)
          (secret * j.val) := rfl

/-- Split a first-register index into its high `ell` bits and low `m` bits.
The low block controls `secret*j mod 2^m`; the high block supplies the
`2^ell` repetitions in the source's narrow-good-pair count. -/
def firstIndexFromBlocks (params : RegisterParameters)
    (high : Fin (2 ^ params.ell)) (low : Fin (2 ^ params.m)) :
    Fin (2 ^ firstBits params) :=
  Fin.cast (by unfold firstBits; rw [pow_add])
    (finProdFinEquiv (high, low))

@[simp]
theorem firstIndexFromBlocks_val (params : RegisterParameters)
    (high : Fin (2 ^ params.ell)) (low : Fin (2 ^ params.m)) :
    (firstIndexFromBlocks params high low).val =
      low.val + 2 ^ params.m * high.val := by
  simp [firstIndexFromBlocks, finProdFinEquiv]

/-- At least half of the actual first-register outcomes have `secret*j`
inside the centered quarter-window modulo `2^m`.  This lifts the quantum-free
two-adic count through all `2^ell` high-bit repetitions. -/
theorem firstRegister_narrowGood_card_ge
    {params : RegisterParameters} (secret : Nat)
    (hm : 2 ≤ params.m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ params.m) :
    2 ^ (firstBits params - 1) ≤
      (Finset.univ.filter fun j : Fin (2 ^ firstBits params) =>
        NumberTheory.centeredModDistance (2 ^ params.m)
          (secret * j.val) ≤ 2 ^ (params.m - 2)).card := by
  classical
  let lowGood := Finset.univ.filter fun low : Fin (2 ^ params.m) =>
    NumberTheory.centeredModDistance (2 ^ params.m)
      (secret * low.val) ≤ 2 ^ (params.m - 2)
  let source := (Finset.univ : Finset (Fin (2 ^ params.ell))).product lowGood
  let target := Finset.univ.filter fun j : Fin (2 ^ firstBits params) =>
    NumberTheory.centeredModDistance (2 ^ params.m)
      (secret * j.val) ≤ 2 ^ (params.m - 2)
  let lift : Fin (2 ^ params.ell) × Fin (2 ^ params.m) →
      Fin (2 ^ firstBits params) := fun pair =>
    firstIndexFromBlocks params pair.1 pair.2
  have hliftInjective : Function.Injective lift := by
    intro left right heq
    have hprod : finProdFinEquiv left = finProdFinEquiv right := by
      apply Fin.ext
      have hval := congrArg Fin.val heq
      simpa [lift, firstIndexFromBlocks] using hval
    exact finProdFinEquiv.injective hprod
  have hliftMaps : Set.MapsTo lift (↑source : Set _)
      (↑target : Set _) := by
    intro pair hpair
    rcases Finset.mem_product.mp hpair with ⟨_highMem, hlowMem⟩
    have hlowGood : NumberTheory.centeredModDistance (2 ^ params.m)
        (secret * pair.2.val) ≤ 2 ^ (params.m - 2) :=
      (Finset.mem_filter.mp hlowMem).2
    have hliftMod : (lift pair).val ≡ pair.2.val [MOD 2 ^ params.m] := by
      unfold lift
      rw [firstIndexFromBlocks_val]
      rw [Nat.add_comm]
      exact Nat.ModEq.modulus_mul_add
    have hscaledMod : secret * (lift pair).val ≡
        secret * pair.2.val [MOD 2 ^ params.m] :=
      hliftMod.mul_left secret
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [NumberTheory.centeredModDistance_eq_of_modEq hscaledMod]
    exact hlowGood
  have hsourceLeTarget : source.card ≤ target.card :=
    Finset.card_le_card_of_injOn lift hliftMaps hliftInjective.injOn
  have hlowCount : 2 ^ (params.m - 1) ≤ lowGood.card := by
    exact NumberTheory.pow_two_half_le_card_centered_mul_quarter
      hm hsecretPos hsecretLt
  have hsourceCard : source.card =
      2 ^ params.ell * lowGood.card := by
    simp [source]
  have hsourceLower : 2 ^ params.ell * 2 ^ (params.m - 1) ≤
      source.card := by
    rw [hsourceCard]
    exact Nat.mul_le_mul_left _ hlowCount
  have hpowEq : 2 ^ params.ell * 2 ^ (params.m - 1) =
      2 ^ (firstBits params - 1) := by
    rw [← pow_add]
    unfold firstBits
    congr 1
    omega
  rw [← hpowEq]
  exact hsourceLower.trans hsourceLeTarget

/-- Ekerå–Håstad's narrow good-pair event: the centered Fourier frequency lies
inside the quarter-width window `2^(m-2)` [EH17, source.tex:500-537]. -/
def NarrowGoodPair (params : RegisterParameters) (secret : Nat)
    (sample : Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) : Prop :=
  (centeredPhaseFrequency secret sample.1 sample.2).natAbs ≤
    2 ^ (params.m - 2)

/-- Finite set of all narrow good pairs in the two measured registers. -/
def narrowGoodPairs (params : RegisterParameters) (secret : Nat) :
    Finset (Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) := by
  classical
  exact Finset.univ.filter fun pair => NarrowGoodPair params secret pair

/-- First-register indices whose principal second-register companion is a
narrow-good pair. -/
def narrowGoodFirstIndices (params : RegisterParameters) (secret : Nat) :
    Finset (Fin (2 ^ firstBits params)) := by
  classical
  exact Finset.univ.filter fun j =>
    NumberTheory.centeredModDistance (2 ^ params.m)
      (secret * j.val) ≤ 2 ^ (params.m - 2)

/-- The actual two-register outcome space contains at least
`2^(m+ell-1)` narrow good pairs.  Each good first-register outcome is paired
with its canonical second-register companion. -/
theorem narrowGoodPair_card_ge
    {params : RegisterParameters} (secret : Nat)
    (hm : 2 ≤ params.m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ params.m) :
    2 ^ (firstBits params - 1) ≤
      (narrowGoodPairs params secret).card := by
  classical
  let source := Finset.univ.filter fun j : Fin (2 ^ firstBits params) =>
    NumberTheory.centeredModDistance (2 ^ params.m)
      (secret * j.val) ≤ 2 ^ (params.m - 2)
  let target := Finset.univ.filter fun pair :
      Fin (2 ^ firstBits params) × Fin (2 ^ params.ell) =>
    NarrowGoodPair params secret pair
  let companion : Fin (2 ^ firstBits params) →
      Fin (2 ^ firstBits params) × Fin (2 ^ params.ell) := fun j =>
    (j, principalSecondIndex secret j)
  have hcompanionInjective : Function.Injective companion := by
    intro left right heq
    exact congrArg Prod.fst heq
  have hcompanionMaps : Set.MapsTo companion (↑source : Set _)
      (↑target : Set _) := by
    intro j hj
    have hgood : NumberTheory.centeredModDistance (2 ^ params.m)
        (secret * j.val) ≤ 2 ^ (params.m - 2) :=
      (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold companion NarrowGoodPair
    rw [centeredPhaseFrequency_principalSecondIndex,
      NumberTheory.natAbs_centeredResidue (Nat.two_pow_pos params.m)]
    exact hgood
  have hsourceLeTarget : source.card ≤ target.card :=
    Finset.card_le_card_of_injOn companion hcompanionMaps
      hcompanionInjective.injOn
  simpa [narrowGoodPairs, target] using
    (firstRegister_narrowGood_card_ge secret hm hsecretPos hsecretLt).trans
      hsourceLeTarget

/-- There are enough narrow-good first-register indices to select exactly the
source lower-bound cardinality. -/
theorem exists_exactNarrowGoodFirstIndices
    {params : RegisterParameters} (secret : Nat)
    (hm : 2 ≤ params.m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ params.m) :
    ∃ selected : Finset (Fin (2 ^ firstBits params)),
      selected ⊆ narrowGoodFirstIndices params secret ∧
        selected.card = 2 ^ (firstBits params - 1) := by
  obtain ⟨selected, hsubset, hcard⟩ :=
    Finset.exists_subset_card_eq
      (firstRegister_narrowGood_card_ge secret hm hsecretPos hsecretLt)
  exact ⟨selected, hsubset, hcard⟩

/-- A proof-side exact-cardinality subset of the narrow-good first indices.
No runtime algorithm branches on this noncomputable witness. -/
noncomputable def exactNarrowGoodFirstIndices
    {params : RegisterParameters} (secret : Nat)
    (hm : 2 ≤ params.m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ params.m) :
    Finset (Fin (2 ^ firstBits params)) :=
  Classical.choose
    (exists_exactNarrowGoodFirstIndices secret hm hsecretPos hsecretLt)

theorem exactNarrowGoodFirstIndices_subset
    {params : RegisterParameters} (secret : Nat)
    (hm : 2 ≤ params.m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ params.m) :
    exactNarrowGoodFirstIndices secret hm hsecretPos hsecretLt ⊆
      narrowGoodFirstIndices params secret :=
  (Classical.choose_spec
    (exists_exactNarrowGoodFirstIndices secret hm hsecretPos hsecretLt)).1

theorem exactNarrowGoodFirstIndices_card
    {params : RegisterParameters} (secret : Nat)
    (hm : 2 ≤ params.m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ params.m) :
    (exactNarrowGoodFirstIndices secret hm hsecretPos hsecretLt).card =
      2 ^ (firstBits params - 1) :=
  (Classical.choose_spec
    (exists_exactNarrowGoodFirstIndices secret hm hsecretPos hsecretLt)).2

/-- Inject each first-register index into its principal narrow-good pair. -/
def principalGoodPairEmbedding (params : RegisterParameters) (secret : Nat) :
    Fin (2 ^ firstBits params) ↪
      Fin (2 ^ firstBits params) × Fin (2 ^ params.ell) where
  toFun := fun j => (j, principalSecondIndex secret j)
  inj' := by
    intro left right heq
    exact congrArg Prod.fst heq

/-- Exact-size proof core used to minorize the actual Born distribution. -/
noncomputable def exactNarrowGoodCore
    {params : RegisterParameters} (secret : Nat)
    (hm : 2 ≤ params.m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ params.m) :
    Finset (Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) :=
  (exactNarrowGoodFirstIndices secret hm hsecretPos hsecretLt).map
    (principalGoodPairEmbedding params secret)

theorem exactNarrowGoodCore_card
    {params : RegisterParameters} (secret : Nat)
    (hm : 2 ≤ params.m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ params.m) :
    (exactNarrowGoodCore secret hm hsecretPos hsecretLt).card =
      2 ^ (firstBits params - 1) := by
  rw [exactNarrowGoodCore, Finset.card_map,
    exactNarrowGoodFirstIndices_card]

theorem exactNarrowGoodCore_mem_narrowGoodPairs
    {params : RegisterParameters} (secret : Nat)
    (hm : 2 ≤ params.m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ params.m)
    {pair : Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)}
    (hpair : pair ∈ exactNarrowGoodCore secret hm hsecretPos hsecretLt) :
    pair ∈ narrowGoodPairs params secret := by
  classical
  rw [exactNarrowGoodCore, Finset.mem_map] at hpair
  rcases hpair with ⟨j, hj, rfl⟩
  have hjgood : j ∈ narrowGoodFirstIndices params secret :=
    exactNarrowGoodFirstIndices_subset secret hm hsecretPos hsecretLt hj
  have hdistance :
      NumberTheory.centeredModDistance (2 ^ params.m) (secret * j.val) ≤
        2 ^ (params.m - 2) :=
    (Finset.mem_filter.mp hjgood).2
  rw [narrowGoodPairs, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  unfold NarrowGoodPair
  change
    (centeredPhaseFrequency secret j
      (principalSecondIndex secret j)).natAbs ≤ 2 ^ (params.m - 2)
  rw [centeredPhaseFrequency_principalSecondIndex,
    NumberTheory.natAbs_centeredResidue (Nat.two_pow_pos params.m)]
  exact hdistance

/-- Integer lattice coordinate obtained after dividing the centered frequency
offset by the `2^m` spacing between neighboring second-register phases. -/
def scaledFrequencyIndex {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) : Int :=
  ((((secret * j.val : Nat) : Int) - centeredPhaseFrequency secret j k) /
    ((2 ^ params.m : Nat) : Int))

/-- Real center of the `2^m`-spaced frequency lattice for a fixed first
Fourier-register outcome. -/
def scaledFrequencyCenter {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) : Real :=
  ((secret * j.val : Nat) : Real) / (2 : Real) ^ params.m

/-- The centered phase frequency is exactly the real lattice displacement
from `secret*j / 2^m` to its integral scaled-frequency coordinate. -/
theorem centeredPhaseFrequency_eq_base_sub_scaled
    {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) :
    centeredPhaseFrequency secret j k =
      ((secret * j.val : Nat) : Int) -
        ((2 ^ params.m : Nat) : Int) *
          scaledFrequencyIndex secret j k := by
  have hmod : Int.ModEq (2 ^ firstBits params)
      (centeredPhaseFrequency secret j k)
      (phaseFrequencyNat secret j k) := by
    exact NumberTheory.centeredResidue_modEq
      (2 ^ firstBits params) (phaseFrequencyNat secret j k)
  have hspacingDvdPeriod :
      (((2 ^ params.m : Nat) : Int)) ∣
        (((2 ^ firstBits params : Nat) : Int)) := by
    refine ⟨((2 ^ params.ell : Nat) : Int), ?_⟩
    push_cast
    simp only [firstBits, pow_add]
    ring
  have hperiodDvdDifference :
      (((2 ^ firstBits params : Nat) : Int)) ∣
        ((phaseFrequencyNat secret j k : Nat) : Int) -
          centeredPhaseFrequency secret j k :=
    Int.modEq_iff_dvd.mp hmod
  have hspacingDvdDifference :
      (((2 ^ params.m : Nat) : Int)) ∣
        ((phaseFrequencyNat secret j k : Nat) : Int) -
          centeredPhaseFrequency secret j k :=
    hspacingDvdPeriod.trans hperiodDvdDifference
  have hspacingDvdK :
      (((2 ^ params.m : Nat) : Int)) ∣
        (((2 ^ params.m * k.val : Nat) : Int)) := by
    refine ⟨(k.val : Int), ?_⟩
    push_cast
    ring
  have hbaseDvd :
      (((2 ^ params.m : Nat) : Int)) ∣
        (((secret * j.val : Nat) : Int) -
          centeredPhaseFrequency secret j k) := by
    obtain ⟨cofactor, hcofactor⟩ :=
      hspacingDvdDifference.sub hspacingDvdK
    refine ⟨cofactor, ?_⟩
    calc
      ((secret * j.val : Nat) : Int) -
          centeredPhaseFrequency secret j k =
        (((phaseFrequencyNat secret j k : Nat) : Int) -
          centeredPhaseFrequency secret j k) -
            (((2 ^ params.m * k.val : Nat) : Int)) := by
              unfold phaseFrequencyNat
              push_cast
              ring
      _ = ((2 ^ params.m : Nat) : Int) * cofactor := hcofactor
  have hcancel := Int.ediv_mul_cancel hbaseDvd
  unfold scaledFrequencyIndex
  rw [mul_comm] at hcancel
  omega

/-- Absolute centered frequency equals the lattice spacing times the distance
from the real center to the associated integral lattice point. -/
theorem abs_centeredPhaseFrequency_eq_spacing_mul_distance
    {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) :
    |(centeredPhaseFrequency secret j k : Real)| =
      (2 : Real) ^ params.m *
        |scaledFrequencyCenter secret j -
          (scaledFrequencyIndex secret j k : Real)| := by
  have hspacingPos : 0 < (2 : Real) ^ params.m := pow_pos (by norm_num) _
  rw [centeredPhaseFrequency_eq_base_sub_scaled secret j k]
  push_cast
  calc
    |((secret : Real) * (j.val : Real) -
        (2 : Real) ^ params.m *
          (scaledFrequencyIndex secret j k : Real))| =
      |(2 : Real) ^ params.m *
        (scaledFrequencyCenter secret j -
          (scaledFrequencyIndex secret j k : Real))| := by
            congr 1
            unfold scaledFrequencyCenter
            field_simp [ne_of_gt hspacingPos]
            push_cast
            ring
    _ = (2 : Real) ^ params.m *
        |scaledFrequencyCenter secret j -
          (scaledFrequencyIndex secret j k : Real)| := by
            rw [abs_mul, abs_of_pos hspacingPos]

/-- For a fixed first-register outcome, distinct second-register outcomes land
at distinct points of the scaled integer frequency lattice. -/
theorem scaledFrequencyIndex_injective {params : RegisterParameters}
    (secret : Nat) (j : Fin (2 ^ firstBits params)) :
    Function.Injective (fun k : Fin (2 ^ params.ell) =>
      scaledFrequencyIndex secret j k) := by
  intro left right hindex
  change scaledFrequencyIndex secret j left =
    scaledFrequencyIndex secret j right at hindex
  have hcentered : centeredPhaseFrequency secret j left =
      centeredPhaseFrequency secret j right := by
    rw [centeredPhaseFrequency_eq_base_sub_scaled secret j left,
      centeredPhaseFrequency_eq_base_sub_scaled secret j right, hindex]
  have hmodLeft : Int.ModEq (2 ^ firstBits params)
      (centeredPhaseFrequency secret j left)
      (phaseFrequencyNat secret j left) :=
    NumberTheory.centeredResidue_modEq
      (2 ^ firstBits params) (phaseFrequencyNat secret j left)
  have hmodRight : Int.ModEq (2 ^ firstBits params)
      (centeredPhaseFrequency secret j right)
      (phaseFrequencyNat secret j right) :=
    NumberTheory.centeredResidue_modEq
      (2 ^ firstBits params) (phaseFrequencyNat secret j right)
  have hmiddle : Int.ModEq (2 ^ firstBits params)
      (centeredPhaseFrequency secret j left)
      (phaseFrequencyNat secret j right) := by
    rw [hcentered]
    exact hmodRight
  have hphaseMod : Int.ModEq (2 ^ firstBits params)
      (phaseFrequencyNat secret j left)
      (phaseFrequencyNat secret j right) :=
    hmodLeft.symm.trans hmiddle
  have hdiv : (((2 ^ firstBits params : Nat) : Int)) ∣
      ((phaseFrequencyNat secret j right : Nat) : Int) -
        ((phaseFrequencyNat secret j left : Nat) : Int) :=
    Int.modEq_iff_dvd.mp hphaseMod
  have hfinite :
      |(right.val : Int) - (left.val : Int)| <
        ((2 ^ params.ell : Nat) : Int) :=
    Int.abs_sub_lt_of_lt_lt left.isLt right.isLt
  have hspacingPos : (0 : Int) < ((2 ^ params.m : Nat) : Int) := by
    positivity
  have hdifference :
      ((phaseFrequencyNat secret j right : Nat) : Int) -
          ((phaseFrequencyNat secret j left : Nat) : Int) =
        ((2 ^ params.m : Nat) : Int) *
          ((right.val : Int) - (left.val : Int)) := by
    unfold phaseFrequencyNat
    push_cast
    ring
  have habs :
      |((phaseFrequencyNat secret j right : Nat) : Int) -
          ((phaseFrequencyNat secret j left : Nat) : Int)| <
        ((2 ^ firstBits params : Nat) : Int) := by
    calc
      |((phaseFrequencyNat secret j right : Nat) : Int) -
          ((phaseFrequencyNat secret j left : Nat) : Int)| =
        ((2 ^ params.m : Nat) : Int) *
          |(right.val : Int) - (left.val : Int)| := by
            rw [hdifference, abs_mul, abs_of_pos hspacingPos]
      _ < ((2 ^ params.m : Nat) : Int) *
          ((2 ^ params.ell : Nat) : Int) :=
            Int.mul_lt_mul_of_pos_left hfinite hspacingPos
      _ = ((2 ^ firstBits params : Nat) : Int) := by
            push_cast
            simp only [firstBits, pow_add]
            ring
  have hzero := Int.eq_zero_of_abs_lt_dvd hdiv habs
  rw [hdifference] at hzero
  have hdelta : (right.val : Int) - (left.val : Int) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hspacingPos)
  apply Fin.ext
  omega

@[simp]
theorem phaseFrequency_eq_natCast {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) :
    phaseFrequency secret j k = phaseFrequencyNat secret j k := rfl

/-- Reducing the frequency to its centered representative does not change the
Fourier character. -/
theorem omega_neg_phaseFrequency_eq_centered {params : RegisterParameters}
    (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) :
    ω (firstBits params) ^ (-phaseFrequency secret j k) =
      ω (firstBits params) ^ (-centeredPhaseFrequency secret j k) := by
  have hmod : Int.ModEq (2 ^ firstBits params)
      (-phaseFrequency secret j k) (-centeredPhaseFrequency secret j k) := by
    simpa [phaseFrequency, centeredPhaseFrequency] using
      (NumberTheory.centeredResidue_modEq
        (2 ^ firstBits params) (phaseFrequencyNat secret j k)).neg.symm
  have hdiv : ((2 ^ firstBits params : Nat) : Int) ∣
      (-phaseFrequency secret j k) - (-centeredPhaseFrequency secret j k) :=
    Int.modEq_iff_dvd.mp hmod.symm
  have hpow : ω (firstBits params) ^
      ((-phaseFrequency secret j k) - (-centeredPhaseFrequency secret j k)) = 1 :=
    (omega_zpow_eq_one_iff (firstBits params) _).2 hdiv
  rw [zpow_sub₀ (omega_ne_zero (firstBits params)),
    div_eq_one_iff_eq (zpow_ne_zero _ (omega_ne_zero (firstBits params)))] at hpow
  exact hpow

/-- Multiplying the Fourier frequency by a natural progression index preserves
the centered representative of the same character. -/
theorem omega_neg_mul_phaseFrequency_eq_centered
    {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (index : Nat) :
    ω (firstBits params) ^
        (-((index : Int) * phaseFrequency secret j k)) =
      ω (firstBits params) ^
        (-((index : Int) * centeredPhaseFrequency secret j k)) := by
  calc
    ω (firstBits params) ^
        (-((index : Int) * phaseFrequency secret j k)) =
      (ω (firstBits params) ^ (-phaseFrequency secret j k)) ^ index := by
        rw [← zpow_natCast, ← zpow_mul]
        congr 2
        ring
    _ = (ω (firstBits params) ^
        (-centeredPhaseFrequency secret j k)) ^ index := by
          rw [omega_neg_phaseFrequency_eq_centered]
    _ = ω (firstBits params) ^
        (-((index : Int) * centeredPhaseFrequency secret j k)) := by
          rw [← zpow_natCast, ← zpow_mul]
          congr 2
          ring

/-- The centered source frequency lies on the principal half-period. -/
theorem centeredPhaseFrequency_principal {params : RegisterParameters}
    (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) :
    2 * (centeredPhaseFrequency secret j k).natAbs ≤
      2 ^ firstBits params := by
  exact NumberTheory.two_mul_natAbs_centeredResidue_le (by positivity)

/-- On a fixed integer-exponent fiber, the double inverse-QFT character is a
global phase times a character whose frequency is `secret*j + 2^m*k`.  Thus
the remaining fiber sum is a one-dimensional finite geometric sum rather than
an unconstrained two-register sum. -/
theorem fiberPhase_eq_global_mul_character {params : RegisterParameters}
    (secret : Nat) (exponent : Int)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell))
    (hfiber : oracleExponent secret a.val b.val = exponent) :
    star (ω (firstBits params) ^ (a.val * j.val)) *
        star (ω params.ell ^ (b.val * k.val)) =
      ω (firstBits params) ^ (-(exponent * (j.val : Int))) *
        ω (firstBits params) ^
          (-((b.val : Int) * phaseFrequency secret j k)) := by
  rw [star_omega_pow, star_omega_pow]
  have hscale :
      ω params.ell ^ (-(b.val * k.val : Nat) : Int) =
        ω (firstBits params) ^
          (((2 ^ params.m : Nat) : Int) *
            (-((b.val : Int) * (k.val : Int)))) := by
    simpa [firstBits] using
      (omega_add_pow_two_zpow_mul params.ell params.m
        (-((b.val : Int) * (k.val : Int)))).symm
  rw [hscale, ← zpow_add₀ (omega_ne_zero (firstBits params)),
    ← zpow_add₀ (omega_ne_zero (firstBits params))]
  congr 1
  unfold oracleExponent at hfiber
  unfold phaseFrequency phaseFrequencyNat
  push_cast at hfiber ⊢
  linear_combination -(j.val : Int) * hfiber

/-- The residual character sum after removing the global phase from one
integer-exponent fiber.  Its summand depends on the pair only through the
second exponent `b`; the fiber predicate selects the finite contiguous range
that survives. -/
def exponentFiberCharacterSum {params : RegisterParameters}
    (secret : Nat) (exponent : Int)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) : Complex :=
  ∑ a : Fin (2 ^ firstBits params),
    ∑ b : Fin (2 ^ params.ell),
      if oracleExponent secret a.val b.val = exponent then
        ω (firstBits params) ^
          (-((b.val : Int) * phaseFrequency secret j k))
      else
        0

/-- Every integer-exponent fiber sum factors into an irrelevant global phase
and the one-frequency character sum. -/
theorem exponentFiberPhaseSum_eq_global_mul_characterSum
    {params : RegisterParameters} (secret : Nat) (exponent : Int)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) :
    exponentFiberPhaseSum secret exponent j k =
      ω (firstBits params) ^ (-(exponent * (j.val : Int))) *
        exponentFiberCharacterSum secret exponent j k := by
  classical
  unfold exponentFiberPhaseSum exponentFiberCharacterSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hfiber : oracleExponent secret a.val b.val = exponent
  · rw [if_pos hfiber, if_pos hfiber,
      fiberPhase_eq_global_mul_character secret exponent j k a b hfiber]
  · simp [hfiber]

/-- A second-register exponent is valid for a fixed integer fiber exactly
when some first-register exponent represents that fiber. -/
def FiberBValid {params : RegisterParameters} (secret : Nat)
    (exponent : Int) (b : Fin (2 ^ params.ell)) : Prop :=
  ∃ a : Fin (2 ^ firstBits params),
    oracleExponent secret a.val b.val = exponent

/-- The surviving second-register indices of an exponent fiber form the
explicit integer interval `0 ≤ exponent + b*secret < 2^(ell+m)`. -/
theorem fiberBValid_iff_int_interval {params : RegisterParameters}
    (secret : Nat) (exponent : Int) (b : Fin (2 ^ params.ell)) :
    FiberBValid secret exponent b ↔
      0 ≤ exponent + ((b.val * secret : Nat) : Int) ∧
        exponent + ((b.val * secret : Nat) : Int) <
          ((2 ^ firstBits params : Nat) : Int) := by
  constructor
  · rintro ⟨a, ha⟩
    have haValue :
        (a.val : Int) = exponent + ((b.val * secret : Nat) : Int) := by
      unfold oracleExponent at ha
      omega
    constructor
    · rw [← haValue]
      exact Int.natCast_nonneg a.val
    · rw [← haValue]
      exact_mod_cast a.isLt
  · rintro ⟨hlower, hupper⟩
    let aValue : Nat :=
      Int.toNat (exponent + ((b.val * secret : Nat) : Int))
    have haValue :
        (aValue : Int) = exponent + ((b.val * secret : Nat) : Int) := by
      exact Int.toNat_of_nonneg hlower
    have haLt : aValue < 2 ^ firstBits params := by
      rw [← haValue] at hupper
      exact_mod_cast hupper
    refine ⟨⟨aValue, haLt⟩, ?_⟩
    unfold oracleExponent
    rw [haValue]
    omega

/-- One-dimensional geometric sum obtained after eliminating the uniquely
determined first-register exponent. -/
def exponentFiberGeometricSum {params : RegisterParameters}
    (secret : Nat) (exponent : Int)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) : Complex := by
  classical
  exact ∑ b : Fin (2 ^ params.ell),
    if FiberBValid secret exponent b then
      ω (firstBits params) ^
        (-((b.val : Int) * phaseFrequency secret j k))
    else
      0

/-- Fully explicit interval form of the exponent-fiber geometric sum. -/
def exponentFiberIntervalSum {params : RegisterParameters}
    (secret : Nat) (exponent : Int)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) : Complex := by
  classical
  exact ∑ b : Fin (2 ^ params.ell),
    if 0 ≤ exponent + ((b.val * secret : Nat) : Int) ∧
        exponent + ((b.val * secret : Nat) : Int) <
          ((2 ^ firstBits params : Nat) : Int) then
      ω (firstBits params) ^
        (-((b.val : Int) * phaseFrequency secret j k))
    else
      0

/-- The existential fiber indicator and the explicit contiguous-interval
indicator define the same geometric sum. -/
theorem exponentFiberGeometricSum_eq_intervalSum
    {params : RegisterParameters} (secret : Nat) (exponent : Int)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) :
    exponentFiberGeometricSum secret exponent j k =
      exponentFiberIntervalSum secret exponent j k := by
  classical
  unfold exponentFiberGeometricSum exponentFiberIntervalSum
  apply Finset.sum_congr rfl
  intro b _hb
  rw [fiberBValid_iff_int_interval]
  by_cases hinterval :
      0 ≤ exponent + ((b.val * secret : Nat) : Int) ∧
        exponent + ((b.val * secret : Nat) : Int) <
          ((2 ^ firstBits params : Nat) : Int)
  · simp
  · simp

/-- Finite set of second-register indices that survive on one integer
exponent fiber. -/
def exponentFiberBSet {params : RegisterParameters} (secret : Nat)
    (exponent : Int) : Finset (Fin (2 ^ params.ell)) := by
  classical
  exact Finset.univ.filter (FiberBValid secret exponent)

@[simp]
theorem mem_exponentFiberBSet_iff {params : RegisterParameters}
    {secret : Nat} {exponent : Int} {b : Fin (2 ^ params.ell)} :
    b ∈ exponentFiberBSet secret exponent ↔
      FiberBValid secret exponent b := by
  classical
  simp [exponentFiberBSet]

/-- The explicit interval sum is the character sum over exactly the surviving
second-register indices. -/
theorem exponentFiberIntervalSum_eq_sum_bSet
    {params : RegisterParameters} (secret : Nat) (exponent : Int)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) :
    exponentFiberIntervalSum secret exponent j k =
      ∑ b ∈ exponentFiberBSet (params := params) secret exponent,
        ω (firstBits params) ^
          (-((b.val : Int) * phaseFrequency secret j k)) := by
  classical
  rw [← exponentFiberGeometricSum_eq_intervalSum]
  unfold exponentFiberGeometricSum exponentFiberBSet
  rw [Finset.sum_filter]

/-- Valid second-register indices are order-convex: if two endpoints lie on
one exponent fiber, every index between them lies on the same fiber. -/
theorem fiberBValid_of_between {params : RegisterParameters}
    {secret : Nat} {exponent : Int}
    {left middle right : Fin (2 ^ params.ell)}
    (hleft : FiberBValid secret exponent left)
    (hright : FiberBValid secret exponent right)
    (hlm : left ≤ middle) (hmr : middle ≤ right) :
    FiberBValid secret exponent middle := by
  rw [fiberBValid_iff_int_interval] at hleft hright ⊢
  have hlmMul : left.val * secret ≤ middle.val * secret :=
    Nat.mul_le_mul_right secret hlm
  have hmrMul : middle.val * secret ≤ right.val * secret :=
    Nat.mul_le_mul_right secret hmr
  have hlmMulInt :
      ((left.val * secret : Nat) : Int) ≤
        ((middle.val * secret : Nat) : Int) := by
    exact_mod_cast hlmMul
  have hmrMulInt :
      ((middle.val * secret : Nat) : Int) ≤
        ((right.val * secret : Nat) : Int) := by
    exact_mod_cast hmrMul
  constructor <;> omega

/-- Every nonempty exponent fiber is a contiguous finite interval. -/
theorem exponentFiberBSet_eq_Icc {params : RegisterParameters}
    (secret : Nat) (exponent : Int)
    (hne : (exponentFiberBSet (params := params) secret exponent).Nonempty) :
    exponentFiberBSet (params := params) secret exponent =
      Finset.Icc
        ((exponentFiberBSet (params := params) secret exponent).min' hne)
        ((exponentFiberBSet (params := params) secret exponent).max' hne) := by
  classical
  let fiberSet := exponentFiberBSet (params := params) secret exponent
  ext b
  simp only [Finset.mem_Icc]
  constructor
  · intro hb
    exact ⟨fiberSet.min'_le b hb, fiberSet.le_max' b hb⟩
  · rintro ⟨hmin, hmax⟩
    have hminValid : FiberBValid secret exponent (fiberSet.min' hne) := by
      exact mem_exponentFiberBSet_iff.mp (fiberSet.min'_mem hne)
    have hmaxValid : FiberBValid secret exponent (fiberSet.max' hne) := by
      exact mem_exponentFiberBSet_iff.mp (fiberSet.max'_mem hne)
    exact mem_exponentFiberBSet_iff.mpr
      (fiberBValid_of_between hminValid hmaxValid hmin hmax)

/-- Every actual exponent-fiber interval obeys the reciprocal centered-frequency
bound used in the E23 `zeta` tail estimate [E23, arxiv-v5.tex:549-579]. -/
theorem norm_exponentFiberIntervalSum_le
    {params : RegisterParameters} (secret : Nat) (exponent : Int)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (hfrequency : centeredPhaseFrequency secret j k ≠ 0) :
    ‖exponentFiberIntervalSum secret exponent j k‖ ≤
      ((2 ^ firstBits params : Nat) : Real) /
        (2 * ((centeredPhaseFrequency secret j k).natAbs : Real)) := by
  classical
  let fiberSet := exponentFiberBSet (params := params) secret exponent
  by_cases hne : fiberSet.Nonempty
  · let lower := fiberSet.min' hne
    let upper := fiberSet.max' hne
    have hlower : lower ≤ upper := fiberSet.min'_le_max' hne
    have hcenteredSum :
        (∑ b ∈ Finset.Icc lower upper,
            ω (firstBits params) ^
              (-((b.val : Int) * phaseFrequency secret j k))) =
          ∑ b ∈ Finset.Icc lower upper,
            ω (firstBits params) ^
              ((b.val : Int) * (-centeredPhaseFrequency secret j k)) := by
      apply Finset.sum_congr rfl
      intro b _hb
      calc
        ω (firstBits params) ^
            (-((b.val : Int) * phaseFrequency secret j k)) =
          ω (firstBits params) ^
            (-((b.val : Int) * centeredPhaseFrequency secret j k)) :=
              omega_neg_mul_phaseFrequency_eq_centered secret j k b.val
        _ = ω (firstBits params) ^
            ((b.val : Int) * (-centeredPhaseFrequency secret j k)) := by
              congr 2
              ring
    rw [exponentFiberIntervalSum_eq_sum_bSet,
      exponentFiberBSet_eq_Icc secret exponent hne, hcenteredSum,
      sum_Icc_omega_zpow_eq_shifted_range
        (-centeredPhaseFrequency secret j k) lower upper hlower]
    simp only [norm_mul, norm_zpow, norm_omega, one_zpow, one_mul]
    simpa only [Int.natAbs_neg] using
      (norm_sum_range_omega_zpow_mul_le
        (firstBits params) (upper.val + 1 - lower.val)
        (-centeredPhaseFrequency secret j k)
        (by simpa only [Int.natAbs_neg] using
          centeredPhaseFrequency_principal secret j k)
        (neg_ne_zero.mpr hfrequency))
  · have hempty : fiberSet = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [exponentFiberIntervalSum_eq_sum_bSet]
    change ‖∑ b ∈ fiberSet,
      ω (firstBits params) ^
        (-((b.val : Int) * phaseFrequency secret j k))‖ ≤ _
    rw [hempty]
    simp only [Finset.sum_empty, norm_zero]
    positivity

/-- For the Ekerå–Håstad narrow good-pair window, every actual integer
exponent fiber contributes at least half its squared cardinality to the source
Fourier weight [EH17, source.tex:645-690]. -/
theorem norm_exponentFiberIntervalSum_sq_ge_half_card
    {params : RegisterParameters} (secret : Nat) (exponent : Int)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (hm : 2 ≤ params.m)
    (hgood : (centeredPhaseFrequency secret j k).natAbs ≤
      2 ^ (params.m - 2)) :
    (((exponentFiberBSet (params := params) secret exponent).card : Real) ^ 2) /
        2 ≤
      ‖exponentFiberIntervalSum secret exponent j k‖ ^ 2 := by
  classical
  let fiberSet := exponentFiberBSet (params := params) secret exponent
  by_cases hne : fiberSet.Nonempty
  · let lower := fiberSet.min' hne
    let upper := fiberSet.max' hne
    have hlower : lower ≤ upper := fiberSet.min'_le_max' hne
    have hcardEq :
        fiberSet.card = upper.val + 1 - lower.val := by
      rw [show fiberSet = Finset.Icc lower upper from
        exponentFiberBSet_eq_Icc secret exponent hne]
      exact Fin.card_Icc lower upper
    have hcardLe : fiberSet.card ≤ 2 ^ params.ell := by
      calc
        fiberSet.card ≤ (Finset.univ : Finset (Fin (2 ^ params.ell))).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = 2 ^ params.ell := by simp
    have hproductNat :
        4 * (fiberSet.card *
          (centeredPhaseFrequency secret j k).natAbs) ≤
          2 ^ firstBits params := by
      have hmul := Nat.mul_le_mul hcardLe hgood
      have hpow : 4 * (2 ^ params.ell * 2 ^ (params.m - 2)) =
          2 ^ firstBits params := by
        rw [show 4 = 2 ^ 2 by norm_num, ← pow_add, ← pow_add]
        unfold firstBits
        congr 1
        omega
      calc
        4 * (fiberSet.card *
            (centeredPhaseFrequency secret j k).natAbs) ≤
          4 * (2 ^ params.ell * 2 ^ (params.m - 2)) :=
            Nat.mul_le_mul_left 4 hmul
        _ = 2 ^ firstBits params := hpow
    have habsFrequency :
        |(centeredPhaseFrequency secret j k : Real)| =
          ((centeredPhaseFrequency secret j k).natAbs : Real) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      norm_num
    have hperiodPos : 0 < (2 : Real) ^ firstBits params := by positivity
    have hproductReal :
        4 * ((fiberSet.card : Real) *
          |(centeredPhaseFrequency secret j k : Real)|) ≤
          (2 : Real) ^ firstBits params := by
      rw [habsFrequency]
      exact_mod_cast hproductNat
    have hratio :
        (fiberSet.card : Real) *
            |(centeredPhaseFrequency secret j k : Real)| /
            (2 : Real) ^ firstBits params ≤
          1 / 4 := by
      rw [div_le_iff₀ hperiodPos]
      linarith
    have hangle :
        Real.pi *
            ((fiberSet.card : Real) *
              (|(centeredPhaseFrequency secret j k : Real)| /
                (2 : Real) ^ firstBits params)) ≤
          Real.pi / 4 := by
      calc
        Real.pi *
            ((fiberSet.card : Real) *
              (|(centeredPhaseFrequency secret j k : Real)| /
                (2 : Real) ^ firstBits params)) =
          Real.pi *
            (((fiberSet.card : Real) *
              |(centeredPhaseFrequency secret j k : Real)|) /
                (2 : Real) ^ firstBits params) := by ring
        _ ≤ Real.pi * (1 / 4 : Real) :=
          mul_le_mul_of_nonneg_left hratio Real.pi_pos.le
        _ = Real.pi / 4 := by ring
    have hlowerNorm := norm_sum_range_omega_zpow_mul_ge_of_angle_le
      (firstBits params) (upper.val + 1 - lower.val)
      (-centeredPhaseFrequency secret j k) (by
        simpa only [Int.cast_neg, abs_neg, hcardEq] using hangle)
    have hnormEq :
        ‖exponentFiberIntervalSum secret exponent j k‖ =
          ‖∑ offset ∈ Finset.range (upper.val + 1 - lower.val),
            ω (firstBits params) ^
              ((offset : Int) * (-centeredPhaseFrequency secret j k))‖ := by
      rw [exponentFiberIntervalSum_eq_sum_bSet,
        exponentFiberBSet_eq_Icc secret exponent hne]
      have hcenteredSum :
          (∑ b ∈ Finset.Icc lower upper,
              ω (firstBits params) ^
                (-((b.val : Int) * phaseFrequency secret j k))) =
            ∑ b ∈ Finset.Icc lower upper,
              ω (firstBits params) ^
                ((b.val : Int) * (-centeredPhaseFrequency secret j k)) := by
        apply Finset.sum_congr rfl
        intro b _hb
        calc
          ω (firstBits params) ^
              (-((b.val : Int) * phaseFrequency secret j k)) =
            ω (firstBits params) ^
              (-((b.val : Int) * centeredPhaseFrequency secret j k)) :=
                omega_neg_mul_phaseFrequency_eq_centered secret j k b.val
          _ = ω (firstBits params) ^
              ((b.val : Int) * (-centeredPhaseFrequency secret j k)) := by
                congr 2
                ring
      rw [hcenteredSum,
        sum_Icc_omega_zpow_eq_shifted_range
          (-centeredPhaseFrequency secret j k) lower upper hlower,
        norm_mul, norm_zpow, norm_omega, one_zpow, one_mul]
    have hnorm :
        (fiberSet.card : Real) *
            (Real.sin (Real.pi / 4) / (Real.pi / 4)) ≤
          ‖exponentFiberIntervalSum secret exponent j k‖ := by
      rw [hnormEq, hcardEq]
      exact hlowerNorm
    have hfactorNonneg :
        0 ≤ Real.sin (Real.pi / 4) / (Real.pi / 4) := by
      rw [Real.sin_pi_div_four]
      positivity
    have hcardNonneg : 0 ≤ (fiberSet.card : Real) := Nat.cast_nonneg _
    have hnormNonneg : 0 ≤ ‖exponentFiberIntervalSum secret exponent j k‖ :=
      norm_nonneg _
    have hsecantSq := one_half_le_sq_sin_pi_div_four_div
    have hscaledNonneg :
        0 ≤ (fiberSet.card : Real) *
          (Real.sin (Real.pi / 4) / (Real.pi / 4)) :=
      mul_nonneg hcardNonneg hfactorNonneg
    have hnormSq :
        ((fiberSet.card : Real) *
            (Real.sin (Real.pi / 4) / (Real.pi / 4))) ^ 2 ≤
          ‖exponentFiberIntervalSum secret exponent j k‖ ^ 2 :=
      (sq_le_sq₀ hscaledNonneg hnormNonneg).2 hnorm
    change (((fiberSet.card : Real) ^ 2) / 2) ≤ _
    calc
      ((fiberSet.card : Real) ^ 2) / 2 ≤
          (fiberSet.card : Real) ^ 2 *
            (Real.sin (Real.pi / 4) / (Real.pi / 4)) ^ 2 := by
        simpa [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hsecantSq
            (sq_nonneg (fiberSet.card : Real))
      _ = ((fiberSet.card : Real) *
          (Real.sin (Real.pi / 4) / (Real.pi / 4))) ^ 2 := by ring
      _ ≤ _ := hnormSq
  · have hempty : fiberSet = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change (((fiberSet.card : Real) ^ 2) / 2) ≤ _
    rw [hempty]
    simp


private theorem fiberA_unique {params : RegisterParameters}
    (secret : Nat) (exponent : Int) (b : Fin (2 ^ params.ell))
    {left right : Fin (2 ^ firstBits params)}
    (hleft : oracleExponent secret left.val b.val = exponent)
    (hright : oracleExponent secret right.val b.val = exponent) :
    left = right := by
  apply Fin.ext
  unfold oracleExponent at hleft hright
  omega

private def oracleFiberInputIndex (params : RegisterParameters) (secret : Nat)
    (pair : Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) :
    Fin (oracleFiberSpan params secret) :=
  ⟨oracleFiberIndex params secret pair.1 pair.2,
    oracleFiberIndex_lt_span params secret pair.1 pair.2⟩

/-- For one canonical exponent interval index, the number of input pairs in
its complete integer-exponent fiber is the number of surviving second-register
indices. -/
private theorem card_oracleFiberInputIndex_eq_exponentFiberBSet
    (params : RegisterParameters) (secret : Nat)
    (index : Fin (oracleFiberSpan params secret)) :
    ((Finset.univ :
        Finset (Fin (2 ^ firstBits params) × Fin (2 ^ params.ell))).filter
      (fun pair => oracleFiberInputIndex params secret pair = index)).card =
      (exponentFiberBSet (params := params) secret
        (oracleExponentAtIndex params secret index)).card := by
  classical
  refine Finset.card_bij (fun pair _ => pair.2) ?_ ?_ ?_
  · intro pair hpair
    rw [Finset.mem_filter] at hpair
    apply mem_exponentFiberBSet_iff.mpr
    refine ⟨pair.1, ?_⟩
    rw [← oracleExponentAtIndex_oracleFiberIndex
      params secret pair.1 pair.2]
    exact congrArg (oracleExponentAtIndex params secret) hpair.2
  · rintro ⟨leftA, leftB⟩ hleft ⟨rightA, rightB⟩ hright hsecond
    simp only at hsecond
    subst rightB
    rw [Finset.mem_filter] at hleft hright
    apply Prod.ext
    · apply oracleFiberIndex_injective_first params secret leftB
      have hindex :
          oracleFiberInputIndex params secret (leftA, leftB) =
            oracleFiberInputIndex params secret (rightA, leftB) :=
        hleft.2.trans hright.2.symm
      exact congrArg Fin.val hindex
    · rfl
  · intro b hb
    obtain ⟨a, ha⟩ := mem_exponentFiberBSet_iff.mp hb
    refine ⟨(a, b), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    apply oracleExponentAtIndex_injective params secret
    change oracleExponentAtIndex params secret
        ⟨oracleFiberIndex params secret a b,
          oracleFiberIndex_lt_span params secret a b⟩ =
      oracleExponentAtIndex params secret index
    rw [oracleExponentAtIndex_oracleFiberIndex]
    exact ha

/-- The canonical integer-exponent fibers partition all input pairs, so the
sum of their second-register cardinalities is the full two-register input
cardinality. -/
theorem sum_card_exponentFiberBSet
    (params : RegisterParameters) (secret : Nat) :
    (∑ index : Fin (oracleFiberSpan params secret),
      (exponentFiberBSet (params := params) secret
        (oracleExponentAtIndex params secret index)).card) =
      2 ^ firstBits params * 2 ^ params.ell := by
  classical
  calc
    (∑ index : Fin (oracleFiberSpan params secret),
        (exponentFiberBSet (params := params) secret
          (oracleExponentAtIndex params secret index)).card) =
      ∑ index : Fin (oracleFiberSpan params secret),
        ((Finset.univ :
            Finset (Fin (2 ^ firstBits params) × Fin (2 ^ params.ell))).filter
          (fun pair => oracleFiberInputIndex params secret pair = index)).card := by
        apply Finset.sum_congr rfl
        intro index _hindex
        exact (card_oracleFiberInputIndex_eq_exponentFiberBSet
          params secret index).symm
    _ = (Finset.univ :
        Finset (Fin (2 ^ firstBits params) × Fin (2 ^ params.ell))).card := by
      symm
      exact Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ :
          Finset (Fin (2 ^ firstBits params) × Fin (2 ^ params.ell))))
        (t := (Finset.univ : Finset (Fin (oracleFiberSpan params secret))))
        (f := oracleFiberInputIndex params secret)
        (by intro pair _hpair; exact Finset.mem_univ _)
    _ = 2 ^ firstBits params * 2 ^ params.ell := by simp

/-! ## Exact first-register marginal -/

/-- The second-register vector supported on one integer-exponent fiber after
the first inverse-QFT phase has been fixed.  Its nonzero coordinates all have
unit norm; the second inverse QFT therefore preserves the fiber cardinality
exactly. -/
def exponentFiberSecondRegisterVector {params : RegisterParameters}
    (secret : Nat) (exponent : Int)
    (j : Fin (2 ^ firstBits params)) : HilbertVector (Qubits params.ell) := by
  classical
  exact WithLp.toLp 2 fun b =>
    if FiberBValid secret exponent b then
      ω (firstBits params) ^
        (-((b.val : Int) * (secret * j.val : Nat)))
    else 0

/-- Applying the inverse QFT to the fiber-supported second-register vector
gives the interval Fourier sum, including its exact normalization. -/
theorem inverseQFT_exponentFiberSecondRegisterVector_apply
    {params : RegisterParameters} (secret : Nat) (exponent : Int)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) :
    ((QFTOperator params.ell)⁻¹).applyVec
        (exponentFiberSecondRegisterVector secret exponent j) k =
      invSqrtN params.ell *
        exponentFiberIntervalSum secret exponent j k := by
  classical
  rw [UnitaryOperator.applyVec_apply]
  unfold exponentFiberIntervalSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [invQFTOperator_entry]
  simp only [exponentFiberSecondRegisterVector]
  by_cases hvalid : FiberBValid secret exponent b
  · have hinter :
        0 ≤ exponent + ((b.val * secret : Nat) : Int) ∧
          exponent + ((b.val * secret : Nat) : Int) <
            ((2 ^ firstBits params : Nat) : Int) :=
      (fiberBValid_iff_int_interval secret exponent b).mp hvalid
    rw [if_pos hvalid, if_pos hinter]
    have hscale :
        ω params.ell ^ (-((b.val : Int) * (k.val : Int))) =
          ω (firstBits params) ^
            (((2 ^ params.m : Nat) : Int) *
              (-((b.val : Int) * (k.val : Int)))) := by
      simpa [firstBits] using
        (omega_add_pow_two_zpow_mul params.ell params.m
          (-((b.val : Int) * (k.val : Int)))).symm
    rw [hscale]
    calc
      (invSqrtN params.ell * ω (firstBits params) ^
          (((2 ^ params.m : Nat) : Int) *
            (-((b.val : Int) * (k.val : Int))))) *
          ω (firstBits params) ^
            (-((b.val : Int) * (secret * j.val : Nat))) =
        invSqrtN params.ell *
          (ω (firstBits params) ^
              (((2 ^ params.m : Nat) : Int) *
                (-((b.val : Int) * (k.val : Int)))) *
            ω (firstBits params) ^
              (-((b.val : Int) * (secret * j.val : Nat)))) := by ring
      _ = invSqrtN params.ell *
          ω (firstBits params) ^
            ((((2 ^ params.m : Nat) : Int) *
                (-((b.val : Int) * (k.val : Int)))) +
              (-((b.val : Int) * (secret * j.val : Nat)))) := by
        rw [zpow_add₀ (omega_ne_zero (firstBits params))]
      _ = invSqrtN params.ell *
          ω (firstBits params) ^
            (-((b.val : Int) * phaseFrequency secret j k)) := by
        congr 2
        unfold phaseFrequency phaseFrequencyNat
        push_cast
        ring
  · have hinter :
        ¬ (0 ≤ exponent + ((b.val * secret : Nat) : Int) ∧
          exponent + ((b.val * secret : Nat) : Int) <
            ((2 ^ firstBits params : Nat) : Int)) := fun h =>
      hvalid ((fiberBValid_iff_int_interval secret exponent b).mpr h)
    rw [if_neg hvalid, if_neg hinter]
    simp

/-- Parseval identity for one exponent fiber: summing the squared interval
Fourier sums over every second-register output gives `2^ell` times the exact
fiber cardinality. -/
theorem sum_normSq_exponentFiberIntervalSum
    {params : RegisterParameters} (secret : Nat) (exponent : Int)
    (j : Fin (2 ^ firstBits params)) :
    (∑ k : Fin (2 ^ params.ell),
        ‖exponentFiberIntervalSum secret exponent j k‖ ^ 2) =
      (2 : Real) ^ params.ell *
        (exponentFiberBSet (params := params) secret exponent).card := by
  classical
  let input := exponentFiberSecondRegisterVector secret exponent j
  let output : HilbertVector (Qubits params.ell) := WithLp.toLp 2 fun k =>
    invSqrtN params.ell * exponentFiberIntervalSum secret exponent j k
  have hnorm := UnitaryOperator.norm_applyVec
    ((QFTOperator params.ell)⁻¹) input
  have happly :
      ((QFTOperator params.ell)⁻¹).applyVec input = output := by
    ext k
    exact inverseQFT_exponentFiberSecondRegisterVector_apply
      secret exponent j k
  rw [happly] at hnorm
  have hsquared := congrArg (fun value : Real => value ^ 2) hnorm
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2] at hsquared
  dsimp [input, output, exponentFiberSecondRegisterVector] at hsquared
  have hleft :
      (∑ k : Fin (2 ^ params.ell),
          ‖invSqrtN params.ell *
            exponentFiberIntervalSum secret exponent j k‖ ^ 2) =
        ((2 : Real) ^ params.ell)⁻¹ *
          ∑ k : Fin (2 ^ params.ell),
            ‖exponentFiberIntervalSum secret exponent j k‖ ^ 2 := by
    simp_rw [norm_mul, mul_pow]
    rw [← Finset.mul_sum, norm_sq_invSqrtN]
  have hright :
      (∑ b : Fin (2 ^ params.ell),
          ‖if FiberBValid secret exponent b then
              ω (firstBits params) ^
                (-((b.val : Int) *
                  ((secret : Int) * (j.val : Int))))
            else 0‖ ^ 2) =
        (exponentFiberBSet (params := params) secret exponent).card := by
    calc
      (∑ b : Fin (2 ^ params.ell),
          ‖if FiberBValid secret exponent b then
              ω (firstBits params) ^
                (-((b.val : Int) *
                  ((secret : Int) * (j.val : Int))))
            else 0‖ ^ 2) =
        ∑ b ∈ (Finset.univ.filter fun b : Fin (2 ^ params.ell) =>
            FiberBValid secret exponent b), (1 : Real) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro b _hb
          by_cases hvalid : FiberBValid secret exponent b <;>
            simp [hvalid]
      _ = (exponentFiberBSet (params := params) secret exponent).card := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 1
  rw [hleft, hright] at hsquared
  have hpowPos : 0 < (2 : Real) ^ params.ell := by positivity
  calc
    (∑ k : Fin (2 ^ params.ell),
        ‖exponentFiberIntervalSum secret exponent j k‖ ^ 2) =
      (2 : Real) ^ params.ell *
        (((2 : Real) ^ params.ell)⁻¹ *
          ∑ k : Fin (2 ^ params.ell),
            ‖exponentFiberIntervalSum secret exponent j k‖ ^ 2) := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpowPos), one_mul]
    _ = (2 : Real) ^ params.ell *
        (exponentFiberBSet (params := params) secret exponent).card := by
      rw [hsquared]

/-- Cauchy–Schwarz turns the exact fiber-cardinality partition into a lower
bound for the sum of squared fiber cardinalities.  The denominator uses the
source interval bound `span ≤ 2·2^(m+ℓ)` [EH17, source.tex:540-570]. -/
theorem sq_sum_card_exponentFiberBSet_div_le
    (params : RegisterParameters) (secret : Nat)
    (hsecret : secret < 2 ^ params.m) :
    ((((2 : Real) ^ firstBits params) * (2 : Real) ^ params.ell) ^ 2) /
        (2 * (2 : Real) ^ firstBits params) ≤
      ∑ index : Fin (oracleFiberSpan params secret),
        ((exponentFiberBSet (params := params) secret
          (oracleExponentAtIndex params secret index)).card : Real) ^ 2 := by
  let fiberCard : Fin (oracleFiberSpan params secret) → Real :=
    fun index =>
      ((exponentFiberBSet (params := params) secret
        (oracleExponentAtIndex params secret index)).card : Real)
  have hsum :
      (∑ index : Fin (oracleFiberSpan params secret), fiberCard index) =
        (2 : Real) ^ firstBits params * (2 : Real) ^ params.ell := by
    dsimp only [fiberCard]
    exact_mod_cast sum_card_exponentFiberBSet params secret
  have hcauchy :
      (∑ index : Fin (oracleFiberSpan params secret), fiberCard index) ^ 2 ≤
        (oracleFiberSpan params secret : Real) *
          ∑ index : Fin (oracleFiberSpan params secret), fiberCard index ^ 2 := by
    simpa only [Finset.sum_const_zero, Finset.sum_filter, Finset.mem_univ,
      true_and, Finset.card_univ, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ :
          Finset (Fin (oracleFiberSpan params secret))))
        (f := fiberCard))
  have hspan :
      (oracleFiberSpan params secret : Real) ≤
        2 * (2 : Real) ^ firstBits params := by
    exact_mod_cast
      oracleFiberSpan_le_two_mul_firstRegister params secret hsecret
  have hsquaresNonneg :
      0 ≤ ∑ index : Fin (oracleFiberSpan params secret), fiberCard index ^ 2 :=
    Finset.sum_nonneg fun _index _hindex => sq_nonneg _
  have hscaled := hcauchy.trans
    (mul_le_mul_of_nonneg_right hspan hsquaresNonneg)
  rw [hsum] at hscaled
  rw [div_le_iff₀ (by positivity :
    0 < 2 * (2 : Real) ^ firstBits params)]
  simpa only [fiberCard, mul_comm] using hscaled

/-- The residual double character sum is exactly its single-variable
geometric form; no probability model or detached mass certificate is used. -/
theorem exponentFiberCharacterSum_eq_geometricSum
    {params : RegisterParameters} (secret : Nat) (exponent : Int)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) :
    exponentFiberCharacterSum secret exponent j k =
      exponentFiberGeometricSum secret exponent j k := by
  classical
  unfold exponentFiberCharacterSum exponentFiberGeometricSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hvalid : FiberBValid secret exponent b
  · rw [if_pos hvalid]
    obtain ⟨a₀, ha₀⟩ := hvalid
    rw [Finset.sum_eq_single a₀]
    · simp [ha₀]
    · intro a _ha hne
      have hnot : ¬ oracleExponent secret a.val b.val = exponent := by
        intro ha
        exact hne (fiberA_unique secret exponent b ha ha₀)
      simp [hnot]
    · simp
  · rw [if_neg hvalid]
    apply Finset.sum_eq_zero
    intro a _ha
    have hnot : ¬ oracleExponent secret a.val b.val = exponent := by
      intro ha
      exact hvalid ⟨a, ha⟩
    simp [hnot]

/-- Under the no-wrap order condition [E23, arxiv-v5.tex:244-245], a concrete
encoded group-value fiber is exactly the corresponding integer-exponent fiber. -/
theorem fourierFiberSum_at_oracleValue_eq_exponentFiberPhaseSum
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (representativeA : Fin (2 ^ firstBits params))
    (representativeB : Fin (2 ^ params.ell))
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    fourierFiberSum encoding g x j k
        (encodeUnit encoding
          (oracleValue g x representativeA.val representativeB.val)) =
      exponentFiberPhaseSum secret
        (oracleExponent secret representativeA.val representativeB.val) j k := by
  classical
  unfold fourierFiberSum exponentFiberPhaseSum
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  have hgroupIff :
      encodeUnit encoding
          (oracleValue g x representativeA.val representativeB.val) =
          encodeUnit encoding (oracleValue g x a.val b.val) ↔
        oracleExponent secret representativeA.val representativeB.val =
          oracleExponent secret a.val b.val := by
    constructor
    · intro hencoded
      apply (oracleValue_eq_oracleValue_iff_exponent_eq_of_span_le_orderOf
        g x secret representativeA representativeB a b htarget horder).mp
      exact encodeUnit_injective encoding hencoded
    · intro hexponent
      apply congrArg (encodeUnit encoding)
      exact (oracleValue_eq_oracleValue_iff_exponent_eq_of_span_le_orderOf
        g x secret representativeA representativeB a b htarget horder).mpr
          hexponent
  by_cases hencoded :
      encodeUnit encoding
          (oracleValue g x representativeA.val representativeB.val) =
        encodeUnit encoding (oracleValue g x a.val b.val)
  · have hexponent :
        oracleExponent secret a.val b.val =
          oracleExponent secret representativeA.val representativeB.val :=
      (hgroupIff.mp hencoded).symm
    simp [hencoded, hexponent]
  · have hnotExponent :
        ¬ oracleExponent secret a.val b.val =
          oracleExponent secret representativeA.val representativeB.val := by
      intro hexponent
      exact hencoded (hgroupIff.mpr hexponent.symm)
    simp [hencoded, hnotExponent]

/-- Canonical representative-free version of the workspace-fiber theorem.
Every exponent in the complete source interval indexes its own encoded group
power; empty exponent fibers simply yield the zero character sum. -/
theorem fourierFiberSum_at_exponentIndex_eq_exponentFiberPhaseSum
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (index : Fin (oracleFiberSpan params secret))
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    fourierFiberSum encoding g x j k
        (encodeUnit encoding
          (g ^ oracleExponentAtIndex params secret index)) =
      exponentFiberPhaseSum secret
        (oracleExponentAtIndex params secret index) j k := by
  classical
  unfold fourierFiberSum exponentFiberPhaseSum
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  have hgroupIff :
      encodeUnit encoding (g ^ oracleExponentAtIndex params secret index) =
          encodeUnit encoding (oracleValue g x a.val b.val) ↔
        oracleExponentAtIndex params secret index =
          oracleExponent secret a.val b.val := by
    constructor
    · intro hencoded
      apply (zpow_at_index_eq_oracleValue_iff_exponent_eq_of_span_le_orderOf
        g x secret index a b htarget horder).mp
      exact encodeUnit_injective encoding hencoded
    · intro hexponent
      apply congrArg (encodeUnit encoding)
      exact (zpow_at_index_eq_oracleValue_iff_exponent_eq_of_span_le_orderOf
        g x secret index a b htarget horder).mpr hexponent
  by_cases hencoded :
      encodeUnit encoding (g ^ oracleExponentAtIndex params secret index) =
        encodeUnit encoding (oracleValue g x a.val b.val)
  · have hexponent := hgroupIff.mp hencoded
    rw [if_pos hencoded, if_pos hexponent.symm]
  · have hnotExponent :
        ¬ oracleExponent secret a.val b.val =
          oracleExponentAtIndex params secret index := by
      intro hexponent
      exact hencoded (hgroupIff.mpr hexponent.symm)
    rw [if_neg hencoded, if_neg hnotExponent]

/-- The circuit amplitude is the source-shaped Fourier fiber sum multiplied by
its single common normalization.  In particular, the resource-bearing Circuit
and the probability formula are now connected before any analytic lower bound
is introduced. -/
theorem circuitAmplitude_eq_fourierNormalization_mul_fiberSum
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (y : Fin (2 ^ params.workspaceBits)) :
    circuitAmplitude encoding g x j k y =
      fourierNormalization params * fourierFiberSum encoding g x j k y := by
  classical
  unfold circuitAmplitude fourierNormalization fourierFiberSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hfiber :
      y = encodeUnit encoding (oracleValue g x a.val b.val)
  · simp only [hfiber, if_pos, star_mul, star_invSqrtN]
    ring
  · simp [hfiber]

/-- Representative-free source amplitude for a canonical exponent interval
index. -/
theorem circuitAmplitude_at_exponentIndex_eq_intervalSum
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (index : Fin (oracleFiberSpan params secret))
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    circuitAmplitude encoding g x j k
        (encodeUnit encoding
          (g ^ oracleExponentAtIndex params secret index)) =
      fourierNormalization params *
        (ω (firstBits params) ^
            (-(oracleExponentAtIndex params secret index *
              (j.val : Int))) *
          exponentFiberIntervalSum secret
            (oracleExponentAtIndex params secret index) j k) := by
  rw [circuitAmplitude_eq_fourierNormalization_mul_fiberSum,
    fourierFiberSum_at_exponentIndex_eq_exponentFiberPhaseSum
      encoding g x secret index j k htarget horder,
    exponentFiberPhaseSum_eq_global_mul_characterSum,
    exponentFiberCharacterSum_eq_geometricSum,
    exponentFiberGeometricSum_eq_intervalSum]

/-- Representative-free source Eq. (2) weight for a canonical exponent
interval index. -/
theorem normSq_circuitAmplitude_at_exponentIndex_eq_sourceFormula
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (index : Fin (oracleFiberSpan params secret))
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    ‖circuitAmplitude encoding g x j k
        (encodeUnit encoding
          (g ^ oracleExponentAtIndex params secret index))‖ ^ 2 =
      (((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
        ‖exponentFiberIntervalSum secret
          (oracleExponentAtIndex params secret index) j k‖ ^ 2 := by
  rw [circuitAmplitude_at_exponentIndex_eq_intervalSum
    encoding g x secret index j k htarget horder]
  calc
    ‖fourierNormalization params *
        (ω (firstBits params) ^
            (-(oracleExponentAtIndex params secret index * (j.val : Int))) *
          exponentFiberIntervalSum secret
            (oracleExponentAtIndex params secret index) j k)‖ ^ 2 =
      ‖fourierNormalization params‖ ^ 2 *
        ‖exponentFiberIntervalSum secret
          (oracleExponentAtIndex params secret index) j k‖ ^ 2 := by
            simp only [norm_mul, norm_zpow, norm_omega, one_zpow, one_mul]
            ring
    _ = _ := by rw [norm_sq_fourierNormalization_source]

/-- At every actually queried workspace value, the source-shaped amplitude
is exactly the source geometric interval sum, up to the common normalization
and a unit-modulus global phase. -/
theorem circuitAmplitude_at_oracleValue_eq_intervalSum
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (representativeA : Fin (2 ^ firstBits params))
    (representativeB : Fin (2 ^ params.ell))
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    circuitAmplitude encoding g x j k
        (encodeUnit encoding
          (oracleValue g x representativeA.val representativeB.val)) =
      fourierNormalization params *
        (ω (firstBits params) ^
            (-(oracleExponent secret representativeA.val representativeB.val *
              (j.val : Int))) *
          exponentFiberIntervalSum secret
            (oracleExponent secret representativeA.val representativeB.val)
            j k) := by
  rw [circuitAmplitude_eq_fourierNormalization_mul_fiberSum,
    fourierFiberSum_at_oracleValue_eq_exponentFiberPhaseSum
      encoding g x secret representativeA representativeB j k htarget horder,
    exponentFiberPhaseSum_eq_global_mul_characterSum,
    exponentFiberCharacterSum_eq_geometricSum,
    exponentFiberGeometricSum_eq_intervalSum]

/-- Squared amplitude at a queried workspace value is the squared norm of the
explicit interval sum times the common normalization; the global phase has
unit norm and contributes no probability mass. -/
theorem normSq_circuitAmplitude_at_oracleValue_eq_intervalSum
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (representativeA : Fin (2 ^ firstBits params))
    (representativeB : Fin (2 ^ params.ell))
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    ‖circuitAmplitude encoding g x j k
        (encodeUnit encoding
          (oracleValue g x representativeA.val representativeB.val))‖ ^ 2 =
      ‖fourierNormalization params‖ ^ 2 *
        ‖exponentFiberIntervalSum secret
          (oracleExponent secret representativeA.val representativeB.val)
          j k‖ ^ 2 := by
  rw [circuitAmplitude_at_oracleValue_eq_intervalSum
    encoding g x secret representativeA representativeB j k htarget horder]
  simp only [norm_mul, norm_zpow, norm_omega, one_zpow, one_mul]
  ring

/-- Source Eq. (2) for one oracle workspace fiber: the Born weight is
`2^{-2(m+2ℓ)}` times the squared norm of the contiguous geometric sum. -/
theorem normSq_circuitAmplitude_at_oracleValue_eq_sourceFormula
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (representativeA : Fin (2 ^ firstBits params))
    (representativeB : Fin (2 ^ params.ell))
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    ‖circuitAmplitude encoding g x j k
        (encodeUnit encoding
          (oracleValue g x representativeA.val representativeB.val))‖ ^ 2 =
      (((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
        ‖exponentFiberIntervalSum secret
          (oracleExponent secret representativeA.val representativeB.val)
          j k‖ ^ 2 := by
  rw [normSq_circuitAmplitude_at_oracleValue_eq_intervalSum
      encoding g x secret representativeA representativeB j k htarget horder,
    norm_sq_fourierNormalization_source]

/-- Workspace basis values outside the actual group-operation image have zero
amplitude.  Hence marginalization introduces no probability mass beyond the
integer exponent fibers analyzed above. -/
theorem circuitAmplitude_eq_zero_of_not_oracleRange
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (workspace : Fin (2 ^ params.workspaceBits))
    (hout : ∀ (a : Fin (2 ^ firstBits params))
      (b : Fin (2 ^ params.ell)),
        workspace ≠ encodeUnit encoding (oracleValue g x a.val b.val)) :
    circuitAmplitude encoding g x j k workspace = 0 := by
  classical
  unfold circuitAmplitude
  apply Finset.sum_eq_zero
  intro a _ha
  apply Finset.sum_eq_zero
  intro b _hb
  simp [hout a b]

/-- Injective workspace encoding of the complete canonical exponent interval.
The source order bound prevents modular group-power collisions. -/
def exponentWorkspaceEmbedding {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g : (ZMod N)ˣ) (secret : Nat)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    Fin (oracleFiberSpan params secret) ↪
      Fin (2 ^ params.workspaceBits) where
  toFun := fun index =>
    encodeUnit encoding (g ^ oracleExponentAtIndex params secret index)
  inj' := by
    intro left right hencoded
    have hgroup := encodeUnit_injective encoding hencoded
    have hexponent :
        oracleExponentAtIndex params secret left =
          oracleExponentAtIndex params secret right :=
      (NumberTheory.zpow_eq_zpow_iff_of_abs_sub_lt_orderOf g _ _
        ((oracleExponentAtIndex_sub_abs_lt_span_index
          params secret left right).trans_le (by exact_mod_cast horder))).mp hgroup
    apply Fin.ext
    unfold oracleExponentAtIndex at hexponent
    omega

/-- Every workspace value queried by an actual exponent-register pair lies in
the canonical exponent embedding. -/
theorem oracleWorkspace_mem_exponentWorkspaceEmbedding
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (horder : oracleFiberSpan params secret ≤ orderOf g)
    (htarget : x = g ^ secret)
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell)) :
    encodeUnit encoding (oracleValue g x a.val b.val) ∈
      Finset.univ.map
        (exponentWorkspaceEmbedding encoding g secret horder) := by
  let index : Fin (oracleFiberSpan params secret) :=
    ⟨oracleFiberIndex params secret a b,
      oracleFiberIndex_lt_span params secret a b⟩
  apply Finset.mem_map.mpr
  refine ⟨index, Finset.mem_univ _, ?_⟩
  apply congrArg (encodeUnit encoding)
  rw [oracleExponentAtIndex_oracleFiberIndex params secret a b]
  exact (oracleValue_eq_zpow_of_target g x secret a.val b.val htarget).symm

/-- Marginalizing the complete workspace is equivalent to summing over the
canonical integer exponent interval.  The source order hypothesis makes this
an injective reindexing; workspace values outside the queried group orbit have
zero amplitude. -/
theorem workspaceMarginal_eq_exponentIndexSum
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    (∑ workspace : Fin (2 ^ params.workspaceBits),
        ENNReal.ofReal
          (‖circuitAmplitude encoding g x j k workspace‖ ^ 2)) =
      ∑ index : Fin (oracleFiberSpan params secret),
        ENNReal.ofReal
          (‖circuitAmplitude encoding g x j k
            (exponentWorkspaceEmbedding encoding g secret horder index)‖ ^ 2) := by
  classical
  let embedding := exponentWorkspaceEmbedding encoding g secret horder
  calc
    (∑ workspace : Fin (2 ^ params.workspaceBits),
        ENNReal.ofReal
          (‖circuitAmplitude encoding g x j k workspace‖ ^ 2)) =
        ∑ workspace ∈
            (Finset.univ : Finset (Fin (oracleFiberSpan params secret))).map
              embedding,
          ENNReal.ofReal
            (‖circuitAmplitude encoding g x j k workspace‖ ^ 2) := by
      symm
      apply Finset.sum_subset (by simp)
      intro workspace _hworkspace hnot
      rw [circuitAmplitude_eq_zero_of_not_oracleRange
        encoding g x j k workspace]
      · simp
      · intro a b hworkspace
        apply hnot
        rw [hworkspace]
        exact oracleWorkspace_mem_exponentWorkspaceEmbedding
          encoding g x secret horder htarget a b
    _ = ∑ index : Fin (oracleFiberSpan params secret),
        ENNReal.ofReal
          (‖circuitAmplitude encoding g x j k
            (exponentWorkspaceEmbedding encoding g secret horder index)‖ ^ 2) := by
      rw [Finset.sum_map]

end BornProbability
end ShortDLP

end

end QuantumAlg

end
