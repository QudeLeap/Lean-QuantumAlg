/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.PMF
import all QuantumAlg.Primitives.ShortDLP
import all QuantumAlg.Util.Complex
import all QuantumAlg.Util.NumberTheory.CenteredResidue
import all QuantumAlg.Util.Real.ReciprocalSquareTail
import Mathlib.Algebra.Order.Chebyshev

/-!
# Born probabilities for the short-discrete-logarithm circuit

This module derives amplitudes and terminal probabilities from the actual
prepare/query/two-inverse-QFT circuit.  It does not accept a detached
measurement model, source distribution, decoder, or probability floor.
-/

section

namespace QuantumAlg

open NormalizedVector
open scoped BigOperators

noncomputable section

namespace ShortDLP
namespace BornProbability

/-- The normalized state produced by the complete short-DLP circuit. -/
def evolvedState {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) : QubitLayout.State (layout params) where
  state := PureState.ofNormalized
    ((circuit encoding g x).applyNormalized (inputState params).normalized)
    (circuit encoding g x).physical_idx
  system_idx_eq := by simp [circuit_physical_idx, layout_systemIdx]

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

/-- Basis amplitude of the actual circuit, expressed as the double inverse-QFT
sum over the encoded group-operation fibers. -/
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

/-- At every actually queried workspace value, the stored circuit amplitude
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

/-- Source Eq. (2) for one actual circuit workspace fiber: the Born weight is
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

/-- Three nested qubit-register tensors evaluate coordinatewise through the
canonical three-register equivalence. -/
theorem tensor3_apply_tripleEquiv (params : RegisterParameters)
    (left : HilbertVector (Qubits (firstBits params)))
    (middle : HilbertVector (Qubits params.ell))
    (right : HilbertVector (Qubits params.workspaceBits))
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell))
    (y : Fin (2 ^ params.workspaceBits)) :
    HilbertVector.tensor (HilbertVector.tensor left middle) right
        (tripleEquiv params ((a, b), y)) =
      (left a * middle b) * right y := by
  change HilbertVector.tensor (HilbertVector.tensor left middle) right
      (prodEquiv (prodEquiv (a, b), y)) = _
  rw [HilbertVector.tensor_apply_prod, HilbertVector.tensor_apply_prod]

@[simp]
theorem outerProdEquiv_symm_tripleEquiv (params : RegisterParameters)
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell))
    (y : Fin (2 ^ params.workspaceBits)) :
    (prodEquiv
      (m := firstBits params + params.ell)
      (n := params.workspaceBits)).symm
        (tripleEquiv params ((a, b), y)) =
      (prodEquiv (a, b), y) := by
  change (prodEquiv
      (m := firstBits params + params.ell)
      (n := params.workspaceBits)).symm
        (prodEquiv (prodEquiv (a, b), y)) = _
  rw [Equiv.symm_apply_apply]

theorem oracleTarget_eq_zero_iff {N : Nat}
    {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (a : Fin (2 ^ firstBits params))
    (b : Fin (2 ^ params.ell))
    (workspace : Fin (2 ^ params.workspaceBits)) :
    oracleTarget encoding g x a b workspace = 0 ↔
      workspace = encodeUnit encoding (oracleValue g x a.val b.val) := by
  constructor
  · intro h
    have htwice := congrArg (oracleTarget encoding g x a b) h
    simpa [oracleTarget, Nat.xor_assoc] using htwice
  · intro h
    subst workspace
    apply Fin.ext
    simp [oracleTarget]

/-- The two preparation layers send their all-zero basis input to the tensor
product of the two uniform exponent-register states. -/
theorem exponentPreparation_apply_zero (params : RegisterParameters) :
    (exponentPreparation params).applyVec
        (NormalizedVector.ket
          (R := Qubits (firstBits params + params.ell))
          (prodEquiv
            ((0 : Fin (2 ^ firstBits params)),
              (0 : Fin (2 ^ params.ell)))) :
          HilbertVector (Qubits (firstBits params + params.ell))) =
      HilbertVector.tensor
        (WalshHadamard.uniformState (firstBits params) :
          HilbertVector (Qubits (firstBits params)))
        (WalshHadamard.uniformState params.ell :
          HilbertVector (Qubits params.ell)) := by
  rw [← NormalizedVector.tensor_ket]
  change (exponentPreparation params).matrix.applyVec
      (HilbertVector.tensor
        (NormalizedVector.ket
          (R := Qubits (firstBits params))
          (0 : Fin (2 ^ firstBits params)) :
          HilbertVector (Qubits (firstBits params)))
        (NormalizedVector.ket
          (R := Qubits params.ell) (0 : Fin (2 ^ params.ell)) :
          HilbertVector (Qubits params.ell))) = _
  rw [exponentPreparation, tensorConsecutive,
    UnitaryCircuit.tensorQubits_matrix, UnitaryOperator.tensor_applyVec_tensor]
  simp only [UnitaryCircuit.shiftPhysicalIdx_matrix]
  congr 1
  · rw [WalshHadamard.hadamardLayer_matrix]
    exact congrArg
      (fun state : NormalizedVector (Qubits (firstBits params)) =>
        (state : HilbertVector (Qubits (firstBits params))))
      WalshHadamard.hadamardLayerOperator_apply_zero
  · rw [WalshHadamard.hadamardLayer_matrix]
    exact congrArg
      (fun state : NormalizedVector (Qubits params.ell) =>
        (state : HilbertVector (Qubits params.ell)))
      WalshHadamard.hadamardLayerOperator_apply_zero

/-- The complete preparation circuit produces two uniform exponent registers
and leaves an arbitrary fixed workspace basis label unchanged. -/
theorem preparation_apply_basisWorkspace (params : RegisterParameters)
    (workspace : Fin (2 ^ params.workspaceBits)) :
    (preparationCircuit params).applyVec
        (NormalizedVector.ket
          (R := Qubits (totalQubits params))
          (tripleIndex params
            (0 : Fin (2 ^ firstBits params))
            (0 : Fin (2 ^ params.ell)) workspace) :
          HilbertVector (Qubits (totalQubits params))) =
      HilbertVector.tensor
        (HilbertVector.tensor
          (WalshHadamard.uniformState (firstBits params) :
            HilbertVector (Qubits (firstBits params)))
          (WalshHadamard.uniformState params.ell :
            HilbertVector (Qubits params.ell)))
        (NormalizedVector.ket
          (R := Qubits params.workspaceBits) workspace :
          HilbertVector (Qubits params.workspaceBits)) := by
  change (preparationCircuit params).matrix.applyVec
      (NormalizedVector.ket
        (R := Qubits
          (firstBits params + params.ell + params.workspaceBits))
        (prodEquiv
          (prodEquiv
              ((0 : Fin (2 ^ firstBits params)),
                (0 : Fin (2 ^ params.ell))),
            workspace)) :
        HilbertVector (Qubits
          (firstBits params + params.ell + params.workspaceBits))) = _
  rw [← NormalizedVector.tensor_ket, ← NormalizedVector.tensor_ket]
  simp only [NormalizedVector.coe_tensor]
  unfold preparationCircuit withWorkspace
  simp only [id_eq, totalQubits]
  rw [UnitaryCircuit.tensorQubits_matrix,
    UnitaryOperator.tensor_applyVec_tensor]
  change HilbertVector.tensor
      ((exponentPreparation params).applyVec _)
      ((UnitaryCircuit.identity (Qubits params.workspaceBits)
        (List.range' (firstBits params + params.ell) params.workspaceBits)
        _).applyVec _) = _
  rw [UnitaryCircuit.applyVec_identity]
  have hexponentZero :
      HilbertVector.tensor
          (NormalizedVector.ket
            (R := Qubits (firstBits params))
            (0 : Fin (2 ^ firstBits params)) :
            HilbertVector (Qubits (firstBits params)))
          (NormalizedVector.ket
            (R := Qubits params.ell) (0 : Fin (2 ^ params.ell)) :
            HilbertVector (Qubits params.ell)) =
        (NormalizedVector.ket
          (R := Qubits (firstBits params + params.ell))
          (prodEquiv
            ((0 : Fin (2 ^ firstBits params)),
              (0 : Fin (2 ^ params.ell)))) :
          HilbertVector (Qubits (firstBits params + params.ell))) := by
    exact congrArg
      (fun state : NormalizedVector
          (Qubits (firstBits params + params.ell)) =>
        (state : HilbertVector
          (Qubits (firstBits params + params.ell))))
      (NormalizedVector.tensor_ket
        (0 : Fin (2 ^ firstBits params))
        (0 : Fin (2 ^ params.ell)))
  rw [hexponentZero, exponentPreparation_apply_zero]

/-- The complete preparation circuit produces two uniform exponent registers
and leaves the workspace in the zero basis state. -/
theorem preparation_apply_input (params : RegisterParameters) :
    (preparationCircuit params).applyVec
        (NormalizedVector.ket
          (R := Qubits (totalQubits params))
          (0 : Fin (2 ^ totalQubits params)) :
          HilbertVector (Qubits (totalQubits params))) =
      HilbertVector.tensor
        (HilbertVector.tensor
          (WalshHadamard.uniformState (firstBits params) :
            HilbertVector (Qubits (firstBits params)))
          (WalshHadamard.uniformState params.ell :
            HilbertVector (Qubits params.ell)))
        (NormalizedVector.ket
          (R := Qubits params.workspaceBits)
          (0 : Fin (2 ^ params.workspaceBits)) :
          HilbertVector (Qubits params.workspaceBits)) := by
  change (preparationCircuit params).matrix.applyVec
      (NormalizedVector.ket
        (R := Qubits
          (firstBits params + params.ell + params.workspaceBits))
        (prodEquiv
          (prodEquiv
              ((0 : Fin (2 ^ firstBits params)),
                (0 : Fin (2 ^ params.ell))),
            (0 : Fin (2 ^ params.workspaceBits)))) :
        HilbertVector (Qubits
          (firstBits params + params.ell + params.workspaceBits))) = _
  rw [← NormalizedVector.tensor_ket, ← NormalizedVector.tensor_ket]
  simp only [NormalizedVector.coe_tensor]
  unfold preparationCircuit withWorkspace
  simp only [id_eq, totalQubits]
  rw [UnitaryCircuit.tensorQubits_matrix,
    UnitaryOperator.tensor_applyVec_tensor]
  change HilbertVector.tensor
      ((exponentPreparation params).applyVec _)
      ((UnitaryCircuit.identity (Qubits params.workspaceBits)
        (List.range' (firstBits params + params.ell) params.workspaceBits)
        _).applyVec _) = _
  rw [UnitaryCircuit.applyVec_identity]
  have hexponentZero :
      HilbertVector.tensor
          (NormalizedVector.ket
            (R := Qubits (firstBits params))
            (0 : Fin (2 ^ firstBits params)) :
            HilbertVector (Qubits (firstBits params)))
          (NormalizedVector.ket
            (R := Qubits params.ell) (0 : Fin (2 ^ params.ell)) :
            HilbertVector (Qubits params.ell)) =
        (NormalizedVector.ket
          (R := Qubits (firstBits params + params.ell))
          (prodEquiv
            ((0 : Fin (2 ^ firstBits params)),
              (0 : Fin (2 ^ params.ell)))) :
          HilbertVector (Qubits (firstBits params + params.ell))) := by
    exact congrArg
      (fun state : NormalizedVector
          (Qubits (firstBits params + params.ell)) =>
        (state : HilbertVector
          (Qubits (firstBits params + params.ell))))
      (NormalizedVector.tensor_ket
        (0 : Fin (2 ^ firstBits params))
        (0 : Fin (2 ^ params.ell)))
  rw [hexponentZero, exponentPreparation_apply_zero]

/-- Applying the sealed group-operation leaf to the prepared state produces
the explicit graph state of `(a,b) ↦ g^a * (x^b)⁻¹`. -/
theorem oracle_apply_preparation {N : Nat}
    {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    (oracleCircuit encoding g x).applyVec
        ((preparationCircuit params).applyVec
          (NormalizedVector.ket
            (R := Qubits (totalQubits params))
            (0 : Fin (2 ^ totalQubits params)) :
            HilbertVector (Qubits (totalQubits params)))) =
      postOracleVec encoding g x := by
  rw [preparation_apply_input]
  apply WithLp.ofLp_injective
  funext basis
  change (oracleOperator encoding g x).applyVec
      (HilbertVector.tensor
        (HilbertVector.tensor
          (WalshHadamard.uniformState (firstBits params) :
            HilbertVector (Qubits (firstBits params)))
          (WalshHadamard.uniformState params.ell :
            HilbertVector (Qubits params.ell)))
        (NormalizedVector.ket
          (R := Qubits params.workspaceBits)
          (0 : Fin (2 ^ params.workspaceBits)) :
          HilbertVector (Qubits params.workspaceBits))) basis =
    (if ((tripleEquiv params).symm basis).2 =
        encodeUnit encoding
          (oracleValue g x
            ((tripleEquiv params).symm basis).1.1.val
            ((tripleEquiv params).symm basis).1.2.val) then
      WalshHadamard.invSqrtCard (firstBits params) *
        WalshHadamard.invSqrtCard params.ell
    else
      0)
  rw [oracleOperator, UnitaryOperator.ofPerm_applyVec]
  simp only [Equiv.permCongr_apply]
  let triple := (tripleEquiv params).symm basis
  change HilbertVector.tensor
      (HilbertVector.tensor
        (WalshHadamard.uniformState (firstBits params) :
          HilbertVector (Qubits (firstBits params)))
        (WalshHadamard.uniformState params.ell :
          HilbertVector (Qubits params.ell)))
      (NormalizedVector.ket
        (R := Qubits params.workspaceBits)
        (0 : Fin (2 ^ params.workspaceBits)) :
        HilbertVector (Qubits params.workspaceBits))
      (tripleEquiv params (oraclePerm encoding g x triple)) = _
  change HilbertVector.tensor
      (HilbertVector.tensor
        (WalshHadamard.uniformState (firstBits params) :
          HilbertVector (Qubits (firstBits params)))
        (WalshHadamard.uniformState params.ell :
          HilbertVector (Qubits params.ell)))
      (NormalizedVector.ket
        (R := Qubits params.workspaceBits)
        (0 : Fin (2 ^ params.workspaceBits)) :
        HilbertVector (Qubits params.workspaceBits))
      (tripleEquiv params
        ((triple.1.1, triple.1.2),
          oracleTarget encoding g x triple.1.1 triple.1.2 triple.2)) = _
  rw [tensor3_apply_tripleEquiv]
  rw [NormalizedVector.ket_apply]
  change _ =
    if triple.2 = encodeUnit encoding
          (oracleValue g x triple.1.1.val triple.1.2.val) then
        WalshHadamard.invSqrtCard (firstBits params) *
          WalshHadamard.invSqrtCard params.ell
      else
        0
  rw [WalshHadamard.uniformState_apply,
    WalshHadamard.uniformState_apply]
  rw [if_congr
    (oracleTarget_eq_zero_iff encoding g x triple.1.1 triple.1.2 triple.2)
    rfl rfl]
  by_cases htarget :
      triple.2 = encodeUnit encoding
        (oracleValue g x triple.1.1.val triple.1.2.val)
  · rw [if_pos htarget, if_pos htarget, mul_one]
  · rw [if_neg htarget, if_neg htarget, mul_zero]

@[simp]
theorem shortDLPUnitaryOne_entry (bits : Nat)
    (left right : Fin (2 ^ bits)) :
    (((1 : UnitaryOperator (Qubits bits)) : HilbertOperator (Qubits bits))
        left right) =
      if left = right then 1 else 0 := by
  exact Matrix.one_apply

/-- Every terminal basis amplitude is computed by the stored prepare-query-
readout circuit and equals the explicit double inverse-QFT sum. -/
theorem shortDLPCircuit_amplitude {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (y : Fin (2 ^ params.workspaceBits)) :
    (evolvedState encoding g x).normalized
        (tripleEquiv params ((j, k), y)) =
      circuitAmplitude encoding g x j k y := by
  change UnitaryCircuit.applyVec (circuit encoding g x)
      (NormalizedVector.ket
        (R := Qubits (totalQubits params))
        (0 : Fin (2 ^ totalQubits params)) :
        HilbertVector (Qubits (totalQubits params)))
      (tripleEquiv params ((j, k), y)) = _
  rw [circuit, UnitaryCircuit.applyVec_seq, UnitaryCircuit.applyVec_seq,
    oracle_apply_preparation]
  change HilbertOperator.applyVec
      ((readoutCircuit params).matrix :
        HilbertOperator (Qubits (totalQubits params)))
      (postOracleVec encoding g x)
      (tripleEquiv params ((j, k), y)) = _
  rw [HilbertOperator.applyVec_apply,
    ← Equiv.sum_comp (tripleEquiv params),
    Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [readoutCircuit_matrix, exponentReadout_matrix,
    UnitaryOperator.tensor_apply,
    UnitaryCircuit.dagger_matrix, QFTCircuit_matrix, Matrix.conjTranspose_apply,
    QFTOperator_entry, shortDLPUnitaryOne_entry]
  rw [circuitAmplitude]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  rw [Finset.sum_eq_single y]
  · simp [postOracleVec, mul_assoc]
  · intro sourceWorkspace _hsource hne
    simp [postOracleVec, Ne.symm hne]
  · simp

/-! ## Terminal-measurement fibers -/

/-- Big-endian terminal outcome for the combined pair of exponent registers. -/
def shortDLPMeasurementOutcome (params : RegisterParameters)
    (value : Fin (2 ^ (firstBits params + params.ell))) : Outcome params :=
  fun outputIndex =>
    value.val.testBit
      (firstBits params + params.ell - 1 - outputIndex.val)

@[simp]
theorem fullRegisterIndex_shortDLPMeasurementOutcome
    (params : RegisterParameters)
    (value : Fin (2 ^ (firstBits params + params.ell))) :
    TerminalZMeasure.fullRegisterIndex
        (shortDLPMeasurementOutcome params value) = value := by
  apply Fin.val_injective
  change Nat.ofBits
      ((shortDLPMeasurementOutcome params value) ∘ Fin.rev) = value.val
  have hbits :
      (shortDLPMeasurementOutcome params value) ∘ Fin.rev =
        fun bit : Fin (firstBits params + params.ell) =>
          value.val.testBit bit.val := by
    funext bit
    simp only [Function.comp_apply, shortDLPMeasurementOutcome]
    apply congrArg value.val.testBit
    calc
      firstBits params + params.ell - 1 - (Fin.rev bit).val =
          firstBits params + params.ell - ((Fin.rev bit).val + 1) := by
        omega
      _ = (Fin.rev (Fin.rev bit)).val := rfl
      _ = bit.val := congrArg Fin.val (Fin.rev_rev bit)
  rw [hbits, Nat.ofBits_testBit, Nat.mod_eq_of_lt value.isLt]

theorem shortDLPMeasurementOutcome_injective (params : RegisterParameters) :
    Function.Injective (shortDLPMeasurementOutcome params) := by
  intro left right h
  have hindex := congrArg TerminalZMeasure.fullRegisterIndex h
  simpa using hindex

private theorem shortDLPMeasurementOutcome_bijective
    (params : RegisterParameters) :
    Function.Bijective (shortDLPMeasurementOutcome params) := by
  apply (Fintype.bijective_iff_injective_and_card
    (shortDLPMeasurementOutcome params)).2
  refine ⟨shortDLPMeasurementOutcome_injective params, ?_⟩
  simp [Outcome]

@[simp]
theorem decodeOutcome_shortDLPMeasurementOutcome
    (params : RegisterParameters)
    (leftRight : Fin (2 ^ (firstBits params + params.ell))) :
    decodeOutcome params (shortDLPMeasurementOutcome params leftRight) =
      prodEquiv.symm leftRight := by
  simp [decodeOutcome]

@[simp]
theorem shortDLPMeasurement_readout_triple (params : RegisterParameters)
    (leftRight : Fin (2 ^ (firstBits params + params.ell)))
    (workspace : Fin (2 ^ params.workspaceBits)) :
    (measurement params).readout (prodEquiv (leftRight, workspace)) =
      shortDLPMeasurementOutcome params leftRight := by
  funext outputIndex
  change (prodEquiv (leftRight, workspace)).val.testBit
      (totalQubits params - 1 - outputIndex.val) =
    leftRight.val.testBit
      (firstBits params + params.ell - 1 - outputIndex.val)
  have hindex :
      totalQubits params - 1 - outputIndex.val =
        params.workspaceBits +
          (firstBits params + params.ell - 1 - outputIndex.val) := by
    unfold totalQubits
    omega
  rw [hindex]
  exact prodEquiv_testBit_left leftRight workspace
    ⟨firstBits params + params.ell - 1 - outputIndex.val, by omega⟩

theorem shortDLPMeasurement_readout_eq_outcome_iff
    (params : RegisterParameters)
    (basis : Fin (2 ^ totalQubits params))
    (leftRight : Fin (2 ^ (firstBits params + params.ell))) :
    (measurement params).readout basis =
        shortDLPMeasurementOutcome params leftRight ↔
      (prodEquiv.symm basis).1 = leftRight := by
  have hself :
      (measurement params).readout basis =
        shortDLPMeasurementOutcome params (prodEquiv.symm basis).1 := by
    simpa using shortDLPMeasurement_readout_triple params
      (prodEquiv.symm basis).1 (prodEquiv.symm basis).2
  constructor
  · intro h
    exact shortDLPMeasurementOutcome_injective params (hself.symm.trans h)
  · intro h
    exact hself.trans (congrArg (shortDLPMeasurementOutcome params) h)

/-- Embed the unmeasured group-workspace basis into one exponent-readout
fiber. -/
def shortDLPMeasurementFiberEmbedding {params : RegisterParameters}
    (leftRight : Fin (2 ^ (firstBits params + params.ell))) :
    Fin (2 ^ params.workspaceBits) ↪ Fin (2 ^ totalQubits params) where
  toFun := fun workspace => prodEquiv (leftRight, workspace)
  inj' := by
    intro left right h
    cases prodEquiv.injective h
    rfl

@[simp]
theorem shortDLPMeasurementFiberEmbedding_apply
    {params : RegisterParameters}
    (leftRight : Fin (2 ^ (firstBits params + params.ell)))
    (workspace : Fin (2 ^ params.workspaceBits)) :
    shortDLPMeasurementFiberEmbedding leftRight workspace =
      prodEquiv (leftRight, workspace) := rfl

theorem shortDLPMeasurement_fiber (params : RegisterParameters)
    (leftRight : Fin (2 ^ (firstBits params + params.ell))) :
    Finset.univ.filter
        (fun basis : Fin (2 ^ totalQubits params) =>
          (measurement params).readout basis =
            shortDLPMeasurementOutcome params leftRight) =
      Finset.univ.map (shortDLPMeasurementFiberEmbedding leftRight) := by
  ext basis
  rw [Finset.mem_filter,
    shortDLPMeasurement_readout_eq_outcome_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hleft
    apply Finset.mem_map.mpr
    refine ⟨(prodEquiv.symm basis).2, Finset.mem_univ _, ?_⟩
    rw [shortDLPMeasurementFiberEmbedding_apply, ← hleft]
    exact (Equiv.apply_symm_apply
      (prodEquiv
        (m := firstBits params + params.ell)
        (n := params.workspaceBits)) basis)
  · intro hmem
    obtain ⟨workspace, _, hworkspace⟩ := Finset.mem_map.mp hmem
    change prodEquiv (leftRight, workspace) = basis at hworkspace
    rw [← hworkspace, Equiv.symm_apply_apply]

/-- The actual terminal Born probability is the marginal over the unmeasured
group workspace of the same stored circuit amplitude. -/
theorem shortDLPBornOutcomeProbability_eq_workspaceMarginal
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) :
    (measurement params).outcomePMF (evolvedState encoding g x)
        (shortDLPMeasurementOutcome params (prodEquiv (j, k))) =
      ∑ workspace : Fin (2 ^ params.workspaceBits),
        ENNReal.ofReal
          (‖circuitAmplitude encoding g x j k workspace‖ ^ 2) := by
  classical
  rw [TerminalZMeasure.outcomePMF_apply,
    shortDLPMeasurement_fiber, Finset.sum_map]
  simp_rw [shortDLPMeasurementFiberEmbedding_apply]
  change (∑ workspace : Fin (2 ^ params.workspaceBits),
      ENNReal.ofReal
        (‖(evolvedState encoding g x).normalized
          (tripleEquiv params ((j, k), workspace))‖ ^ 2)) = _
  simp_rw [shortDLPCircuit_amplitude]

/-! ## Centered-frequency events -/

/-- E23's centered `tau`-good predicate on one measured exponent pair.  The
distance is computed modulo `2^(m+ell)` and the accepted window is
`2^(m+tau)` [E23, arxiv-v5.tex:332-337]. -/
def TauGoodPair (params : RegisterParameters) (secret τ : Nat)
    (sample : Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) : Prop :=
  NumberTheory.centeredModDistance (2 ^ (params.m + params.ell))
      (secret * sample.1.val + 2 ^ params.m * sample.2.val) ≤
    2 ^ (params.m + τ)

/-- The source-facing centered-distance predicate is exactly the absolute
centered Fourier-frequency window used by the analytic tail bound. -/
theorem tauGoodPair_iff_centeredPhaseFrequency
    (params : RegisterParameters) (secret τ : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) :
    TauGoodPair params secret τ (j, k) ↔
      (centeredPhaseFrequency secret j k).natAbs ≤
        2 ^ (params.m + τ) := by
  unfold TauGoodPair centeredPhaseFrequency phaseFrequencyNat firstBits
  rw [NumberTheory.natAbs_centeredResidue (by positivity)]
  simp [Nat.add_comm]

/-- Second-register outcomes outside the centered `tau` window for one fixed
first-register outcome. -/
def tauBadKSet (params : RegisterParameters) (secret τ : Nat)
    (j : Fin (2 ^ firstBits params)) : Finset (Fin (2 ^ params.ell)) := by
  classical
  exact Finset.univ.filter fun k =>
    ¬ TauGoodPair params secret τ (j, k)

/-- The distinct integral lattice points occupied by the bad second-register
outcomes for one fixed first-register outcome. -/
def tauBadFrequencySet (params : RegisterParameters) (secret τ : Nat)
    (j : Fin (2 ^ firstBits params)) : Finset Int :=
  (tauBadKSet params secret τ j).image
    (scaledFrequencyIndex secret j)

/-- A bad second-register outcome lies strictly beyond distance `2^tau` from
the real center of the scaled integer frequency lattice. -/
theorem tauBadK_distance_gt
    (params : RegisterParameters) (secret τ : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (hk : k ∈ tauBadKSet params secret τ j) :
    (2 : Real) ^ τ <
      |scaledFrequencyCenter secret j -
        (scaledFrequencyIndex secret j k : Real)| := by
  classical
  have hbad : ¬ TauGoodPair params secret τ (j, k) :=
    (Finset.mem_filter.mp hk).2
  have hfrequencyNat :
      2 ^ (params.m + τ) <
        (centeredPhaseFrequency secret j k).natAbs := by
    exact Nat.lt_of_not_ge
      (fun h => hbad ((tauGoodPair_iff_centeredPhaseFrequency
        params secret τ j k).2 h))
  have habsFrequency :
      |(centeredPhaseFrequency secret j k : Real)| =
        ((centeredPhaseFrequency secret j k).natAbs : Real) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  have hfrequencyReal :
      (2 : Real) ^ (params.m + τ) <
        |(centeredPhaseFrequency secret j k : Real)| := by
    rw [habsFrequency]
    exact_mod_cast hfrequencyNat
  rw [abs_centeredPhaseFrequency_eq_spacing_mul_distance
    secret j k, pow_add] at hfrequencyReal
  have hspacingPos : 0 < (2 : Real) ^ params.m := by positivity
  nlinarith

/-- The bad scaled-frequency lattice has a two-sided reciprocal-square tail
bounded solely by the accepted centered window. -/
theorem tauBadFrequency_reciprocalSquareSum_le
    (params : RegisterParameters) (secret τ : Nat)
    (j : Fin (2 ^ firstBits params)) :
    (∑ k ∈ tauBadKSet params secret τ j,
        1 / |scaledFrequencyCenter secret j -
          (scaledFrequencyIndex secret j k : Real)| ^ 2) ≤
      2 / (2 : Real) ^ τ + 2 / ((2 : Real) ^ τ) ^ 2 := by
  classical
  have hinjective : Set.InjOn (scaledFrequencyIndex secret j)
      (tauBadKSet params secret τ j) := by
    intro left _hleft right _hright heq
    exact scaledFrequencyIndex_injective secret j heq
  calc
    (∑ k ∈ tauBadKSet params secret τ j,
        1 / |scaledFrequencyCenter secret j -
          (scaledFrequencyIndex secret j k : Real)| ^ 2) =
      ∑ z ∈ tauBadFrequencySet params secret τ j,
        1 / |scaledFrequencyCenter secret j - (z : Real)| ^ 2 := by
          unfold tauBadFrequencySet
          rw [Finset.sum_image hinjective]
    _ ≤ 2 / (2 : Real) ^ τ + 2 / ((2 : Real) ^ τ) ^ 2 := by
      apply integerReciprocalSquareTail_le
      · positivity
      · intro z hz
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
        exact (tauBadK_distance_gt params secret τ j k hk).le

/-- Actual Born probability of one decoded exponent pair, obtained by
marginalizing the unmeasured group workspace. -/
def pairBornProbability {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (sample : Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) : ENNReal :=
  ∑ workspace : Fin (2 ^ params.workspaceBits),
    ENNReal.ofReal
      (‖circuitAmplitude encoding g x sample.1 sample.2 workspace‖ ^ 2)

/-- Real source weight corresponding to Eq. (3), before embedding the
nonnegative result into `ENNReal`. -/
def pairSourceWeight {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) : Real :=
  ∑ index : Fin (oracleFiberSpan params secret),
    (((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
      ‖exponentFiberIntervalSum secret
        (oracleExponentAtIndex params secret index) j k‖ ^ 2

/-- Every source Eq. (3) pair weight is nonnegative. -/
theorem pairSourceWeight_nonneg {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) :
    0 ≤ pairSourceWeight secret j k := by
  unfold pairSourceWeight
  positivity

/-- The first-register marginal of the source Eq. (3) distribution is exactly
uniform.  This is derived from the inverse-QFT Parseval identity on every
integer-exponent fiber and the exact partition of all exponent inputs; no
uniformity assumption is attached to the probability model. -/
theorem sum_pairSourceWeight_fixedFirst_eq
    {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) :
    (∑ k : Fin (2 ^ params.ell), pairSourceWeight secret j k) =
      ((2 : Real) ^ firstBits params)⁻¹ := by
  classical
  let normalization : Real :=
    ((2 : Real) ^ (2 * (params.m + 2 * params.ell)))⁻¹
  have hsumReal :
      (∑ index : Fin (oracleFiberSpan params secret),
        ((exponentFiberBSet (params := params) secret
          (oracleExponentAtIndex params secret index)).card : Real)) =
        (2 : Real) ^ firstBits params * (2 : Real) ^ params.ell := by
    exact_mod_cast sum_card_exponentFiberBSet params secret
  have hpower :
      (2 : Real) ^ (2 * (params.m + 2 * params.ell)) =
        ((2 : Real) ^ firstBits params) ^ 2 *
          ((2 : Real) ^ params.ell) ^ 2 := by
    rw [show 2 * (params.m + 2 * params.ell) =
        2 * (params.m + params.ell) + 2 * params.ell by omega,
      pow_add,
      show 2 * (params.m + params.ell) =
        (params.m + params.ell) * 2 by omega,
      show 2 * params.ell = params.ell * 2 by omega,
      pow_mul, pow_mul]
    simp only [firstBits, Nat.add_comm]
  unfold pairSourceWeight
  rw [Finset.sum_comm]
  calc
    (∑ index : Fin (oracleFiberSpan params secret),
        ∑ k : Fin (2 ^ params.ell),
          (((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
            ‖exponentFiberIntervalSum secret
              (oracleExponentAtIndex params secret index) j k‖ ^ 2) =
      normalization *
        ∑ index : Fin (oracleFiberSpan params secret),
          ∑ k : Fin (2 ^ params.ell),
            ‖exponentFiberIntervalSum secret
              (oracleExponentAtIndex params secret index) j k‖ ^ 2 := by
        dsimp [normalization]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro index _hindex
        rw [Finset.mul_sum]
    _ = normalization *
        ∑ index : Fin (oracleFiberSpan params secret),
          ((2 : Real) ^ params.ell *
            (exponentFiberBSet (params := params) secret
              (oracleExponentAtIndex params secret index)).card) := by
        congr 1
        apply Finset.sum_congr rfl
        intro index _hindex
        exact sum_normSq_exponentFiberIntervalSum secret
          (oracleExponentAtIndex params secret index) j
    _ = normalization * ((2 : Real) ^ params.ell *
        ∑ index : Fin (oracleFiberSpan params secret),
          ((exponentFiberBSet (params := params) secret
            (oracleExponentAtIndex params secret index)).card : Real)) := by
      congr 1
      calc
        (∑ index : Fin (oracleFiberSpan params secret),
            (2 : Real) ^ params.ell *
              (exponentFiberBSet (params := params) secret
                (oracleExponentAtIndex params secret index)).card) =
          ∑ index : Fin (oracleFiberSpan params secret),
            ((exponentFiberBSet (params := params) secret
              (oracleExponentAtIndex params secret index)).card : Real) *
                (2 : Real) ^ params.ell := by
            apply Finset.sum_congr rfl
            intro index _hindex
            ring
        _ = (∑ index : Fin (oracleFiberSpan params secret),
              ((exponentFiberBSet (params := params) secret
                (oracleExponentAtIndex params secret index)).card : Real)) *
              (2 : Real) ^ params.ell := by
            rw [Finset.sum_mul]
        _ = (2 : Real) ^ params.ell *
            ∑ index : Fin (oracleFiberSpan params secret),
              ((exponentFiberBSet (params := params) secret
                (oracleExponentAtIndex params secret index)).card : Real) := by
          ring
    _ = normalization * ((2 : Real) ^ params.ell *
        ((2 : Real) ^ firstBits params * (2 : Real) ^ params.ell)) := by
      rw [hsumReal]
    _ = ((2 : Real) ^ firstBits params)⁻¹ := by
      dsimp [normalization]
      rw [hpower]
      field_simp

/-- Every Ekerå–Håstad narrow-good measured pair has source probability at
least `2^(-m-ℓ-2)`.  This is derived from the actual contiguous Fourier
fibers: the quarter-circle estimate supplies one half of each squared fiber
cardinality, while Cauchy–Schwarz supplies the global fiber-square mass
[EH17, source.tex:645-745]. -/
theorem narrowGoodPairSourceWeight_ge
    {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (hm : 2 ≤ params.m) (hsecret : secret < 2 ^ params.m)
    (hgood : (centeredPhaseFrequency secret j k).natAbs ≤
      2 ^ (params.m - 2)) :
    ((2 : Real) ^ (params.m + params.ell + 2))⁻¹ ≤
      pairSourceWeight secret j k := by
  let normalization : Real :=
    ((2 : Real) ^ (2 * (params.m + 2 * params.ell)))⁻¹
  let fiberCard : Fin (oracleFiberSpan params secret) → Real :=
    fun index =>
      ((exponentFiberBSet (params := params) secret
        (oracleExponentAtIndex params secret index)).card : Real)
  have hcauchy :=
    sq_sum_card_exponentFiberBSet_div_le params secret hsecret
  have hperFiber (index : Fin (oracleFiberSpan params secret)) :
      normalization * (fiberCard index ^ 2 / 2) ≤
        normalization *
          ‖exponentFiberIntervalSum secret
            (oracleExponentAtIndex params secret index) j k‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact norm_exponentFiberIntervalSum_sq_ge_half_card
      secret (oracleExponentAtIndex params secret index) j k hm hgood
  have hsumLower :
      normalization *
          ((∑ index : Fin (oracleFiberSpan params secret),
            fiberCard index ^ 2) / 2) ≤
        pairSourceWeight secret j k := by
    calc
      normalization *
          ((∑ index : Fin (oracleFiberSpan params secret),
            fiberCard index ^ 2) / 2) =
        (normalization / 2) *
          ∑ index : Fin (oracleFiberSpan params secret),
            fiberCard index ^ 2 := by ring
      _ = ∑ index : Fin (oracleFiberSpan params secret),
          (normalization / 2) * fiberCard index ^ 2 := by
            rw [Finset.mul_sum]
      _ = ∑ index : Fin (oracleFiberSpan params secret),
          normalization * (fiberCard index ^ 2 / 2) := by
        apply Finset.sum_congr rfl
        intro index _hindex
        ring
      _ ≤ ∑ index : Fin (oracleFiberSpan params secret),
          normalization *
            ‖exponentFiberIntervalSum secret
              (oracleExponentAtIndex params secret index) j k‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro index _hindex
        exact hperFiber index
      _ = pairSourceWeight secret j k := by
        rfl
  have hscaledCauchy :
      normalization *
          (((((2 : Real) ^ firstBits params) *
              (2 : Real) ^ params.ell) ^ 2) /
            (2 * (2 : Real) ^ firstBits params) / 2) ≤
        normalization *
          ((∑ index : Fin (oracleFiberSpan params secret),
            fiberCard index ^ 2) / 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_right hcauchy
    norm_num
  have hlower := hscaledCauchy.trans hsumLower
  have hinputPow :
      (2 : Real) ^ firstBits params * (2 : Real) ^ params.ell =
        (2 : Real) ^ (params.m + 2 * params.ell) := by
    rw [← pow_add]
    unfold firstBits
    congr 1
    omega
  have hnormalizationPow :
      (2 : Real) ^ (2 * (params.m + 2 * params.ell)) =
        ((2 : Real) ^ (params.m + 2 * params.ell)) ^ 2 := by
    rw [Nat.mul_comm 2, pow_mul]
  have houtputPow :
      (2 : Real) ^ (params.m + params.ell + 2) =
        4 * (2 : Real) ^ firstBits params := by
    rw [show params.m + params.ell + 2 =
        2 + firstBits params by unfold firstBits; omega, pow_add]
    norm_num
  dsimp only [normalization, fiberCard] at hlower
  rw [hinputPow, hnormalizationPow] at hlower
  calc
    ((2 : Real) ^ (params.m + params.ell + 2))⁻¹ =
        (((2 : Real) ^ (params.m + 2 * params.ell)) ^ 2)⁻¹ *
          ((((2 : Real) ^ (params.m + 2 * params.ell)) ^ 2) /
            (2 * (2 : Real) ^ firstBits params) / 2) := by
      rw [houtputPow]
      field_simp
      norm_num
    _ ≤ pairSourceWeight secret j k := hlower

/-- Every selected core atom has the source's uniform pointwise Fourier
minorization floor. -/
theorem exactNarrowGoodCore_pairSourceWeight_ge
    {params : RegisterParameters} (secret : Nat)
    (hm : 2 ≤ params.m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ params.m)
    {pair : Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)}
    (hpair : pair ∈ exactNarrowGoodCore secret hm hsecretPos hsecretLt) :
    ((2 : Real) ^ (params.m + params.ell + 2))⁻¹ ≤
      pairSourceWeight secret pair.1 pair.2 := by
  classical
  apply narrowGoodPairSourceWeight_ge secret pair.1 pair.2 hm hsecretLt
  exact (Finset.mem_filter.mp
    (exactNarrowGoodCore_mem_narrowGoodPairs secret hm hsecretPos hsecretLt
      hpair)).2

/-- Total source-formula mass of the narrow Ekerå–Håstad event. -/
def narrowGoodSourceWeight {params : RegisterParameters} (secret : Nat) : Real :=
  ∑ pair ∈ narrowGoodPairs params secret,
    pairSourceWeight secret pair.1 pair.2

/-- The source Eq. (3) assigns at least one eighth of its total mass to the
narrow good-pair event.  This is the exact product of at least
`2^(m+ℓ-1)` good pairs and the per-pair floor `2^(-m-ℓ-2)`
[EH17, source.tex:540-745]. -/
theorem narrowGoodSourceWeight_ge_oneEighth
    {params : RegisterParameters} (secret : Nat)
    (hm : 2 ≤ params.m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ params.m) :
    (1 / 8 : Real) ≤ narrowGoodSourceWeight (params := params) secret := by
  classical
  let goodPairs := narrowGoodPairs params secret
  let pointFloor : Real :=
    ((2 : Real) ^ (params.m + params.ell + 2))⁻¹
  have hcardNat : 2 ^ (firstBits params - 1) ≤ goodPairs.card := by
    exact narrowGoodPair_card_ge secret hm hsecretPos hsecretLt
  have hcardReal :
      ((2 ^ (firstBits params - 1) : Nat) : Real) ≤
        (goodPairs.card : Real) := by
    exact_mod_cast hcardNat
  have hpointFloorNonneg : 0 ≤ pointFloor := by
    dsimp [pointFloor]
    positivity
  have hfloorProduct :
      (1 / 8 : Real) =
        ((2 ^ (firstBits params - 1) : Nat) : Real) * pointFloor := by
    dsimp [pointFloor]
    rw [show params.m + params.ell + 2 =
        (firstBits params - 1) + 3 by unfold firstBits; omega, pow_add]
    norm_num [Nat.cast_pow]
    field_simp
  calc
    (1 / 8 : Real) =
        ((2 ^ (firstBits params - 1) : Nat) : Real) * pointFloor :=
      hfloorProduct
    _ ≤ (goodPairs.card : Real) * pointFloor :=
      mul_le_mul_of_nonneg_right hcardReal hpointFloorNonneg
    _ = ∑ _pair ∈ goodPairs, pointFloor := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ pair ∈ goodPairs,
        pairSourceWeight secret pair.1 pair.2 := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact narrowGoodPairSourceWeight_ge secret pair.1 pair.2 hm hsecretLt
        (by simpa [goodPairs, narrowGoodPairs, NarrowGoodPair] using
          (Finset.mem_filter.mp hpair).2)
    _ = narrowGoodSourceWeight (params := params) secret := rfl

/-- Source Eq. (3) for the actual production circuit: the probability of one
measured pair is the common `2⁻²⁽ᵐ⁺²ˡ⁾` normalization times the sum of squared
contiguous Fourier fibers over the complete canonical exponent interval.
Nothing in this formula is supplied as detached probability metadata. -/
theorem pairBornProbability_eq_sourceFormula
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    pairBornProbability encoding g x (j, k) =
      ∑ index : Fin (oracleFiberSpan params secret),
        ENNReal.ofReal
          ((((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
            ‖exponentFiberIntervalSum secret
              (oracleExponentAtIndex params secret index) j k‖ ^ 2) := by
  rw [pairBornProbability,
    workspaceMarginal_eq_exponentIndexSum
      encoding g x secret j k htarget horder]
  apply Finset.sum_congr rfl
  intro index _hindex
  change ENNReal.ofReal
      (‖circuitAmplitude encoding g x j k
        (encodeUnit encoding
          (g ^ oracleExponentAtIndex params secret index))‖ ^ 2) = _
  rw [normSq_circuitAmplitude_at_exponentIndex_eq_sourceFormula
    encoding g x secret index j k htarget horder]

/-- The actual pair probability is the nonnegative-real embedding of the same
source Eq. (3) weight. -/
theorem pairBornProbability_eq_ofReal_pairSourceWeight
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    pairBornProbability encoding g x (j, k) =
      ENNReal.ofReal (pairSourceWeight secret j k) := by
  rw [pairBornProbability_eq_sourceFormula
    encoding g x secret j k htarget horder]
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro index _hindex
  positivity

/-- The actual circuit's first-register marginal is uniform.  The equality is
the `ENNReal` image of `sum_pairSourceWeight_fixedFirst_eq`, hence is derived
from the circuit amplitudes and inverse-QFT unitarity rather than imposed on a
detached measurement model. -/
theorem sum_pairBornProbability_fixedFirst_eq
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (j : Fin (2 ^ firstBits params))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    (∑ k : Fin (2 ^ params.ell),
        pairBornProbability encoding g x (j, k)) =
      ENNReal.ofReal (((2 : Real) ^ firstBits params)⁻¹) := by
  simp_rw [pairBornProbability_eq_ofReal_pairSourceWeight
    encoding g x secret _ _ htarget horder]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [sum_pairSourceWeight_fixedFirst_eq]
  · intro k _hk
    exact pairSourceWeight_nonneg secret j k

/-- Eq. (3) together with the contiguous-fiber estimate bounds one pair by
the number of integer exponent fibers times one reciprocal-frequency term. -/
theorem pairSourceWeight_le_fiberSpan_mul
    {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (hfrequency : centeredPhaseFrequency secret j k ≠ 0) :
    pairSourceWeight secret j k ≤
      (oracleFiberSpan params secret : Real) *
        ((((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
          (((2 ^ firstBits params : Nat) : Real) /
            (2 * ((centeredPhaseFrequency secret j k).natAbs : Real))) ^ 2) := by
  unfold pairSourceWeight
  calc
    (∑ index : Fin (oracleFiberSpan params secret),
        (((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
          ‖exponentFiberIntervalSum secret
            (oracleExponentAtIndex params secret index) j k‖ ^ 2) ≤
      ∑ _index : Fin (oracleFiberSpan params secret),
        (((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
          (((2 ^ firstBits params : Nat) : Real) /
            (2 * ((centeredPhaseFrequency secret j k).natAbs : Real))) ^ 2 := by
      apply Finset.sum_le_sum
      intro index _hindex
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2
          (norm_exponentFiberIntervalSum_le secret
            (oracleExponentAtIndex params secret index) j k hfrequency)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_fin]

/-- Under the short-logarithm range hypothesis, one measured pair has the
explicit inverse-square centered-frequency envelope. -/
theorem pairSourceWeight_le_centeredFrequency
    {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (hsecret : secret < 2 ^ params.m)
    (hfrequency : centeredPhaseFrequency secret j k ≠ 0) :
    pairSourceWeight secret j k ≤
      ((2 ^ firstBits params : Nat) : Real) /
        (2 * ((2 ^ params.ell : Nat) : Real) ^ 2 *
          ((centeredPhaseFrequency secret j k).natAbs : Real) ^ 2) := by
  have hspanNat :=
    oracleFiberSpan_le_two_mul_firstRegister params secret hsecret
  have hspanReal :
      (oracleFiberSpan params secret : Real) ≤
        2 * ((2 ^ firstBits params : Nat) : Real) := by
    exact_mod_cast hspanNat
  have hfrequencyPos :
      0 < ((centeredPhaseFrequency secret j k).natAbs : Real) := by
    exact_mod_cast (Int.natAbs_pos.mpr hfrequency)
  have hpower :
      (2 : Real) ^ (2 * (params.m + 2 * params.ell)) =
        ((2 : Real) ^ firstBits params) ^ 2 *
          ((2 : Real) ^ params.ell) ^ 2 := by
    rw [show 2 * (params.m + 2 * params.ell) =
        2 * (params.m + params.ell) + 2 * params.ell by omega,
      pow_add,
      show 2 * (params.m + params.ell) =
        (params.m + params.ell) * 2 by omega,
      show 2 * params.ell = params.ell * 2 by omega,
      pow_mul, pow_mul]
    simp only [firstBits, Nat.add_comm]
  calc
    pairSourceWeight secret j k ≤
      (oracleFiberSpan params secret : Real) *
        ((((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
          (((2 ^ firstBits params : Nat) : Real) /
            (2 * ((centeredPhaseFrequency secret j k).natAbs : Real))) ^ 2) :=
        pairSourceWeight_le_fiberSpan_mul secret j k hfrequency
    _ ≤ (2 * ((2 ^ firstBits params : Nat) : Real)) *
        ((((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
          (((2 ^ firstBits params : Nat) : Real) /
            (2 * ((centeredPhaseFrequency secret j k).natAbs : Real))) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hspanReal (by positivity)
    _ = ((2 ^ firstBits params : Nat) : Real) /
        (2 * ((2 ^ params.ell : Nat) : Real) ^ 2 *
          ((centeredPhaseFrequency secret j k).natAbs : Real) ^ 2) := by
      rw [hpower]
      norm_num
      field_simp [ne_of_gt hfrequencyPos]
      simp only [sq_abs]

/-- After scaling the centered frequency by the `2^m` lattice spacing, one
bad pair has a universal reciprocal-square envelope. -/
theorem pairSourceWeight_le_scaledDistance
    {params : RegisterParameters} (secret τ : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (hsecret : secret < 2 ^ params.m)
    (hk : k ∈ tauBadKSet params secret τ j) :
    pairSourceWeight secret j k ≤
      (1 / (2 * ((2 ^ firstBits params : Nat) : Real))) *
        (1 / |scaledFrequencyCenter secret j -
          (scaledFrequencyIndex secret j k : Real)| ^ 2) := by
  have hdistancePos : 0 <
      |scaledFrequencyCenter secret j -
        (scaledFrequencyIndex secret j k : Real)| :=
    (pow_pos (by norm_num : (0 : Real) < 2) τ).trans
      (tauBadK_distance_gt params secret τ j k hk)
  have hfrequencyAbsPos :
      0 < |(centeredPhaseFrequency secret j k : Real)| := by
    rw [abs_centeredPhaseFrequency_eq_spacing_mul_distance secret j k]
    positivity
  have hfrequency : centeredPhaseFrequency secret j k ≠ 0 := by
    intro hzero
    rw [hzero] at hfrequencyAbsPos
    norm_num at hfrequencyAbsPos
  have habsFrequency :
      |(centeredPhaseFrequency secret j k : Real)| =
        ((centeredPhaseFrequency secret j k).natAbs : Real) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  have hnatAbsEq :
      ((centeredPhaseFrequency secret j k).natAbs : Real) =
        (2 : Real) ^ params.m *
          |scaledFrequencyCenter secret j -
            (scaledFrequencyIndex secret j k : Real)| := by
    rw [← habsFrequency]
    exact abs_centeredPhaseFrequency_eq_spacing_mul_distance secret j k
  have hfirstBitsCast :
      ((2 ^ firstBits params : Nat) : Real) =
        (2 : Real) ^ params.m * (2 : Real) ^ params.ell := by
    norm_num [firstBits, pow_add]
    ring
  have hellCast :
      ((2 ^ params.ell : Nat) : Real) = (2 : Real) ^ params.ell := by
    norm_num
  calc
    pairSourceWeight secret j k ≤
        ((2 ^ firstBits params : Nat) : Real) /
          (2 * ((2 ^ params.ell : Nat) : Real) ^ 2 *
            ((centeredPhaseFrequency secret j k).natAbs : Real) ^ 2) :=
      pairSourceWeight_le_centeredFrequency secret j k hsecret hfrequency
    _ = (1 / (2 * ((2 ^ firstBits params : Nat) : Real))) *
        (1 / |scaledFrequencyCenter secret j -
          (scaledFrequencyIndex secret j k : Real)| ^ 2) := by
      rw [hnatAbsEq, hfirstBitsCast, hellCast]
      field_simp [ne_of_gt hdistancePos]

/-- For one fixed first-register result, the total source weight of all bad
second-register results is controlled by the two-sided integer tail. -/
theorem tauBadPairSourceWeight_fixedFirst_le
    {params : RegisterParameters} (secret τ : Nat)
    (j : Fin (2 ^ firstBits params))
    (hsecret : secret < 2 ^ params.m) :
    (∑ k ∈ tauBadKSet params secret τ j,
        pairSourceWeight secret j k) ≤
      (1 / (2 * ((2 ^ firstBits params : Nat) : Real))) *
        (2 / (2 : Real) ^ τ + 2 / ((2 : Real) ^ τ) ^ 2) := by
  calc
    (∑ k ∈ tauBadKSet params secret τ j,
        pairSourceWeight secret j k) ≤
      ∑ k ∈ tauBadKSet params secret τ j,
        (1 / (2 * ((2 ^ firstBits params : Nat) : Real))) *
          (1 / |scaledFrequencyCenter secret j -
            (scaledFrequencyIndex secret j k : Real)| ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      exact pairSourceWeight_le_scaledDistance secret τ j k hsecret hk
    _ = (1 / (2 * ((2 ^ firstBits params : Nat) : Real))) *
        (∑ k ∈ tauBadKSet params secret τ j,
          1 / |scaledFrequencyCenter secret j -
            (scaledFrequencyIndex secret j k : Real)| ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (2 * ((2 ^ firstBits params : Nat) : Real))) *
        (2 / (2 : Real) ^ τ + 2 / ((2 : Real) ^ τ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
        (tauBadFrequency_reciprocalSquareSum_le params secret τ j)
      positivity

/-- Total source-formula weight of all centered-window failures. -/
def tauBadSourceWeight {params : RegisterParameters} (secret τ : Nat) : Real :=
  ∑ j : Fin (2 ^ firstBits params),
    ∑ k ∈ tauBadKSet params secret τ j,
      pairSourceWeight secret j k

/-- Summing the fixed-first-register tail over the complete first register
cancels the Fourier normalization and leaves the universal failure envelope
`2^-tau + 2^-2tau`. -/
theorem tauBadSourceWeight_le
    {params : RegisterParameters} (secret τ : Nat)
    (hsecret : secret < 2 ^ params.m) :
    tauBadSourceWeight (params := params) secret τ ≤
      1 / (2 : Real) ^ τ + 1 / ((2 : Real) ^ τ) ^ 2 := by
  have hfirstBitsPos :
      0 < ((2 ^ firstBits params : Nat) : Real) := by positivity
  have hrhoPos : 0 < (2 : Real) ^ τ := by positivity
  unfold tauBadSourceWeight
  calc
    (∑ j : Fin (2 ^ firstBits params),
        ∑ k ∈ tauBadKSet params secret τ j,
          pairSourceWeight secret j k) ≤
      ∑ _j : Fin (2 ^ firstBits params),
        (1 / (2 * ((2 ^ firstBits params : Nat) : Real))) *
          (2 / (2 : Real) ^ τ + 2 / ((2 : Real) ^ τ) ^ 2) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact tauBadPairSourceWeight_fixedFirst_le secret τ j hsecret
    _ = 1 / (2 : Real) ^ τ +
        1 / ((2 : Real) ^ τ) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_fin]
      field_simp [ne_of_gt hfirstBitsPos, ne_of_gt hrhoPos]

/-- The actual terminal PMF at the canonical encoding of `(j,k)` is exactly
the same circuit's workspace-marginal probability. -/
theorem shortDLPBornOutcomeProbability_eq_pairBornProbability
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (sample : Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) :
    (measurement params).outcomePMF (evolvedState encoding g x)
        (shortDLPMeasurementOutcome params (prodEquiv sample)) =
      pairBornProbability encoding g x sample := by
  exact shortDLPBornOutcomeProbability_eq_workspaceMarginal
    encoding g x sample.1 sample.2

/-- First-register marginal of the actual terminal Born distribution.  This
is a projection of the measured circuit output, not a detached sampler. -/
def firstRegisterBornPMF {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) : PMF (Fin (2 ^ firstBits params)) :=
  ((measurement params).outcomePMF (evolvedState encoding g x)).map
    fun outcome => (decodeOutcome params outcome).1

/-- The first-register marginal of the actual short-DLP circuit is exactly
uniform.  The proof reindexes terminal bit strings by the measured register
pair and then uses inverse-QFT Parseval on every fixed first-register value. -/
theorem firstRegisterBornPMF_eq_uniform
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    firstRegisterBornPMF encoding g x =
      PMF.uniformOfFintype (Fin (2 ^ firstBits params)) := by
  classical
  apply PMF.ext
  intro j
  have hmarginal :
      firstRegisterBornPMF encoding g x j =
        ∑ k : Fin (2 ^ params.ell),
          pairBornProbability encoding g x (j, k) := by
    rw [← PMF.toOuterMeasure_apply_singleton]
    rw [firstRegisterBornPMF, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_apply_fintype]
    let e : Fin (2 ^ (firstBits params + params.ell)) ≃ Outcome params :=
      Equiv.ofBijective (shortDLPMeasurementOutcome params)
        (shortDLPMeasurementOutcome_bijective params)
    rw [← Equiv.sum_comp e,
      ← Equiv.sum_comp
        (prodEquiv (m := firstBits params) (n := params.ell)),
      Fintype.sum_prod_type]
    simp only [e, Equiv.ofBijective_apply, Set.indicator_apply,
      Set.mem_preimage, Set.mem_singleton_iff,
      decodeOutcome_shortDLPMeasurementOutcome, Equiv.symm_apply_apply]
    simp_rw [shortDLPBornOutcomeProbability_eq_pairBornProbability]
    simp
  rw [hmarginal,
    sum_pairBornProbability_fixedFirst_eq
      encoding g x secret j htarget horder]
  simp [PMF.uniformOfFintype_apply, ENNReal.ofReal_inv_of_pos]

/-! ## Actual narrow-good and tau-good event masses -/

/-- Mass of the narrow Ekerå–Håstad good-pair event in the actual terminal
distribution of the production short-DLP circuit. -/
def narrowGoodBornMass {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat) : ENNReal :=
  ((measurement params).outcomePMF (evolvedState encoding g x)).toOuterMeasure
    {outcome | NarrowGoodPair params secret (decodeOutcome params outcome)}

/-- Reindex the actual terminal narrow-good event by the canonical measured
pair.  This identifies the PMF event with the same finite set used by the
source Eq. (3) count. -/
theorem narrowGoodBornMass_eq_pairSum
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat) :
    narrowGoodBornMass encoding g x secret =
      ∑ pair ∈ narrowGoodPairs params secret,
        pairBornProbability encoding g x pair := by
  classical
  let e : Fin (2 ^ (firstBits params + params.ell)) ≃ Outcome params :=
    Equiv.ofBijective (shortDLPMeasurementOutcome params)
      (shortDLPMeasurementOutcome_bijective params)
  rw [narrowGoodBornMass, PMF.toOuterMeasure_apply_fintype,
    ← Equiv.sum_comp e,
    ← Equiv.sum_comp
      (prodEquiv (m := firstBits params) (n := params.ell))]
  simp only [e, Equiv.ofBijective_apply, Set.indicator_apply,
    Set.mem_ofPred_eq, decodeOutcome_shortDLPMeasurementOutcome,
    Equiv.symm_apply_apply]
  simp_rw [shortDLPBornOutcomeProbability_eq_pairBornProbability]
  unfold narrowGoodPairs
  rw [Finset.sum_filter]

/-- The actual narrow-good Born mass is the nonnegative-real embedding of the
source Eq. (3) narrow-good weight; no detached probability model is used. -/
theorem narrowGoodBornMass_eq_ofReal_sourceWeight
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    narrowGoodBornMass encoding g x secret =
      ENNReal.ofReal
        (narrowGoodSourceWeight (params := params) secret) := by
  rw [narrowGoodBornMass_eq_pairSum]
  simp_rw [pairBornProbability_eq_ofReal_pairSourceWeight
    encoding g x secret _ _ htarget horder]
  unfold narrowGoodSourceWeight
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro pair _hpair
  exact pairSourceWeight_nonneg secret pair.1 pair.2

/-- One execution of the actual production short-DLP circuit lands in the
narrow Ekerå–Håstad good-pair event with probability at least `1/8`
[EH17, source.tex:540-745]. -/
theorem narrowGoodBornMass_ge_oneEighth
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (hm : 2 ≤ params.m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ params.m)
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    ENNReal.ofReal (1 / 8 : Real) ≤
      narrowGoodBornMass encoding g x secret := by
  rw [narrowGoodBornMass_eq_ofReal_sourceWeight
    encoding g x secret htarget horder]
  exact ENNReal.ofReal_le_ofReal
    (narrowGoodSourceWeight_ge_oneEighth secret hm hsecretPos hsecretLt)

/-- Mass of the `tau`-good event in the actual terminal distribution of the
production short-DLP circuit.  No detached probability model or lower bound is
an input. -/
def tauGoodBornMass {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret τ : Nat) : ENNReal :=
  ((measurement params).outcomePMF (evolvedState encoding g x)).toOuterMeasure
    {outcome | TauGoodPair params secret τ (decodeOutcome params outcome)}

/-- Mass of the complementary centered-window failure event in the same actual
terminal distribution. -/
def tauBadBornMass {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret τ : Nat) : ENNReal :=
  ((measurement params).outcomePMF (evolvedState encoding g x)).toOuterMeasure
    {outcome | ¬ TauGoodPair params secret τ (decodeOutcome params outcome)}

/-- Reindex the actual terminal event mass by the canonical `(j,k)` basis.
This is the source-facing finite sum used by the Fourier-tail argument
[E23, arxiv-v5.tex:233-266,382-393]. -/
theorem tauGoodBornMass_eq_pairSum
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret τ : Nat) :
    tauGoodBornMass encoding g x secret τ =
      ∑ leftRight : Fin (2 ^ (firstBits params + params.ell)),
        Set.indicator
          {leftRight |
            TauGoodPair params secret τ (prodEquiv.symm leftRight)}
          (fun leftRight =>
            pairBornProbability encoding g x (prodEquiv.symm leftRight))
          leftRight := by
  classical
  let e : Fin (2 ^ (firstBits params + params.ell)) ≃ Outcome params :=
    Equiv.ofBijective (shortDLPMeasurementOutcome params)
      (shortDLPMeasurementOutcome_bijective params)
  rw [tauGoodBornMass, PMF.toOuterMeasure_apply_fintype,
    ← Equiv.sum_comp e]
  simp only [e, Equiv.ofBijective_apply, Set.indicator_apply,
    Set.mem_ofPred_eq, decodeOutcome_shortDLPMeasurementOutcome]
  apply Finset.sum_congr rfl
  intro leftRight _hleftRight
  by_cases hgood :
      TauGoodPair params secret τ (prodEquiv.symm leftRight)
  · rw [if_pos hgood, if_pos hgood]
    simpa only [Equiv.apply_symm_apply] using
      shortDLPBornOutcomeProbability_eq_pairBornProbability encoding g x
        (prodEquiv.symm leftRight)
  · rw [if_neg hgood, if_neg hgood]

/-- Reindex the actual bad-event mass as the nested sum over the bad
second-register outcomes for every first-register outcome. -/
theorem tauBadBornMass_eq_pairSum
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret τ : Nat) :
    tauBadBornMass encoding g x secret τ =
      ∑ j : Fin (2 ^ firstBits params),
        ∑ k ∈ tauBadKSet params secret τ j,
          pairBornProbability encoding g x (j, k) := by
  classical
  let e : Fin (2 ^ (firstBits params + params.ell)) ≃ Outcome params :=
    Equiv.ofBijective (shortDLPMeasurementOutcome params)
      (shortDLPMeasurementOutcome_bijective params)
  rw [tauBadBornMass, PMF.toOuterMeasure_apply_fintype,
    ← Equiv.sum_comp e,
    ← Equiv.sum_comp
      (prodEquiv (m := firstBits params) (n := params.ell)),
    Fintype.sum_prod_type]
  simp only [e, Equiv.ofBijective_apply, Set.indicator_apply,
    Set.mem_ofPred_eq, decodeOutcome_shortDLPMeasurementOutcome,
    Equiv.symm_apply_apply]
  simp_rw [shortDLPBornOutcomeProbability_eq_pairBornProbability]
  apply Finset.sum_congr rfl
  intro j _hj
  unfold tauBadKSet
  rw [Finset.sum_filter]

/-- The actual bad-event probability is exactly the nonnegative-real embedding
of the source Eq. (3) bad weight. -/
theorem tauBadBornMass_eq_ofReal_sourceWeight
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret τ : Nat)
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    tauBadBornMass encoding g x secret τ =
      ENNReal.ofReal (tauBadSourceWeight (params := params) secret τ) := by
  rw [tauBadBornMass_eq_pairSum]
  simp_rw [pairBornProbability_eq_ofReal_pairSourceWeight
    encoding g x secret _ _ htarget horder]
  unfold tauBadSourceWeight
  have hinner (j : Fin (2 ^ firstBits params)) :
      (∑ k ∈ tauBadKSet params secret τ j,
          ENNReal.ofReal (pairSourceWeight secret j k)) =
        ENNReal.ofReal
          (∑ k ∈ tauBadKSet params secret τ j,
            pairSourceWeight secret j k) := by
    symm
    apply ENNReal.ofReal_sum_of_nonneg
    intro k _hk
    exact pairSourceWeight_nonneg secret j k
  simp_rw [hinner]
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro j _hj
  exact Finset.sum_nonneg fun k _hk => pairSourceWeight_nonneg secret j k

/-- The actual terminal failure probability obeys the universal centered-tail
envelope derived from the same circuit's Eq. (3) amplitudes. -/
theorem tauBadBornMass_le
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret τ : Nat)
    (hsecret : secret < 2 ^ params.m)
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    tauBadBornMass encoding g x secret τ ≤
      ENNReal.ofReal
        (1 / (2 : Real) ^ τ + 1 / ((2 : Real) ^ τ) ^ 2) := by
  rw [tauBadBornMass_eq_ofReal_sourceWeight
    encoding g x secret τ htarget horder]
  exact ENNReal.ofReal_le_ofReal
    (tauBadSourceWeight_le secret τ hsecret)

/-- The good and bad centered-window events are exact complements in the
actual terminal PMF. -/
theorem tauGoodBornMass_eq_one_sub_tauBadBornMass
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret τ : Nat) :
    tauGoodBornMass encoding g x secret τ =
      1 - tauBadBornMass encoding g x secret τ := by
  exact PMF.eventProbability_eq_one_sub_complement
    ((measurement params).outcomePMF (evolvedState encoding g x))
    (fun outcome =>
      TauGoodPair params secret τ (decodeOutcome params outcome))

/-- At the production choice `tau = 4`, the actual centered-window failure
mass is at most `17/256`. -/
theorem tauFourBadBornMass_le_seventeen_over_twoFiftySix
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (hsecret : secret < 2 ^ params.m)
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    tauBadBornMass encoding g x secret 4 ≤
      ENNReal.ofReal (17 / 256 : Real) := by
  convert tauBadBornMass_le encoding g x secret 4
    hsecret htarget horder using 1
  norm_num

/-- The actual production circuit has centered `tau = 4` good mass at least
`239/256`, with no detached measurement model or assumed probability floor. -/
theorem tauFourGoodBornMass_ge_twoThirtyNine_over_twoFiftySix
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (hsecret : secret < 2 ^ params.m)
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    ENNReal.ofReal (239 / 256 : Real) ≤
      tauGoodBornMass encoding g x secret 4 := by
  have hbad := tauFourBadBornMass_le_seventeen_over_twoFiftySix
    encoding g x secret hsecret htarget horder
  calc
    ENNReal.ofReal (239 / 256 : Real) =
        ENNReal.ofReal (1 - 17 / 256 : Real) := by norm_num
    _ = ENNReal.ofReal (1 : Real) -
        ENNReal.ofReal (17 / 256 : Real) := by
      rw [ENNReal.ofReal_sub]
      norm_num
    _ = 1 - ENNReal.ofReal (17 / 256 : Real) := by
      rw [ENNReal.ofReal_one]
    _ ≤ 1 - tauBadBornMass encoding g x secret 4 :=
      tsub_le_tsub_left hbad 1
    _ = tauGoodBornMass encoding g x secret 4 :=
      (tauGoodBornMass_eq_one_sub_tauBadBornMass
        encoding g x secret 4).symm

/-- Coarse one-eighth corollary proved here for `tau = 4` using the wider
centered-window analysis [E23, arxiv-v5.tex:334-337,382-393].  The narrow
good-pair event used by the two-sample lattice-recovery analysis above has a
different window [EH17, source.tex:525-532]. -/
theorem tauFourGoodBornMass_ge_oneEighth
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (hsecret : secret < 2 ^ params.m)
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    ENNReal.ofReal (1 / 8 : Real) ≤
      tauGoodBornMass encoding g x secret 4 := by
  calc
    ENNReal.ofReal (1 / 8 : Real) ≤
        ENNReal.ofReal (239 / 256 : Real) :=
      ENNReal.ofReal_le_ofReal (by norm_num)
    _ ≤ tauGoodBornMass encoding g x secret 4 :=
      tauFourGoodBornMass_ge_twoThirtyNine_over_twoFiftySix
        encoding g x secret hsecret htarget horder

end BornProbability
end ShortDLP

end

end QuantumAlg

end
