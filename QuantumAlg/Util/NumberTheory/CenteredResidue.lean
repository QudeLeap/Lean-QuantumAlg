/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

/-!
# Centered modular distance

This module contains the quantum-free arithmetic shared by Fourier-sampling
probability arguments.  It deliberately does not name an algorithm or attach a
probability lower bound.
-/

section

namespace QuantumAlg
namespace NumberTheory

/-- Distance from `value` to zero in the centered residue system modulo
`modulus`.  For a positive modulus this is the smaller of the ordinary residue
and its distance from the next multiple of the modulus. -/
def centeredModDistance (modulus value : Nat) : Nat :=
  let residue := value % modulus
  min residue (modulus - residue)

/-- Canonical signed representative of a natural residue, chosen in the
centered interval about zero.  Ties at half the modulus use the nonnegative
representative. -/
def centeredResidue (modulus value : Nat) : Int :=
  let residue := value % modulus
  if 2 * residue ≤ modulus then
    residue
  else
    (residue : Int) - modulus

/-- Additive inverse of a natural number in the canonical residue interval. -/
def modularNegation (modulus value : Nat) : Nat :=
  (modulus - value % modulus) % modulus

theorem modularNegation_lt {modulus value : Nat} (hmodulus : 0 < modulus) :
    modularNegation modulus value < modulus := by
  exact Nat.mod_lt _ hmodulus

/-- Adding the canonical modular negation gives residue zero. -/
theorem add_modularNegation_mod_eq_zero {modulus value : Nat}
    (hmodulus : 0 < modulus) :
    (value + modularNegation modulus value) % modulus = 0 := by
  let residue := value % modulus
  have hresidueLt : residue < modulus := Nat.mod_lt value hmodulus
  have hvalue : value ≡ residue [MOD modulus] :=
    (Nat.mod_modEq value modulus).symm
  change value + modularNegation modulus value ≡ 0 [MOD modulus]
  by_cases hzero : residue = 0
  · simpa [modularNegation, residue, hzero] using hvalue
  · have hresiduePos : 0 < residue := Nat.pos_of_ne_zero hzero
    have hnegMod : (modulus - residue) % modulus =
        modulus - residue :=
      Nat.mod_eq_of_lt (by omega)
    have hnegEq : modularNegation modulus value =
        modulus - residue := by
      unfold modularNegation
      change (modulus - residue) % modulus = modulus - residue
      exact hnegMod
    calc
      value + modularNegation modulus value ≡
          residue + (modulus - residue) [MOD modulus] := by
        rw [hnegEq]
        exact hvalue.add Nat.ModEq.rfl
      _ = modulus := by omega
      _ ≡ 0 [MOD modulus] := by simp [Nat.ModEq]

/-- The canonical natural modular negation represents the additive inverse in
the corresponding integer residue class. -/
theorem modularNegation_modEq_neg {modulus value : Nat}
    (hmodulus : 0 < modulus) :
    Int.ModEq modulus (modularNegation modulus value) (-(value : Int)) := by
  have hzero := add_modularNegation_mod_eq_zero
    (modulus := modulus) (value := value) hmodulus
  have hdvdNat : modulus ∣ value + modularNegation modulus value := by
    exact Nat.dvd_of_mod_eq_zero hzero
  rw [Int.modEq_iff_dvd]
  rcases hdvdNat with ⟨multiple, hmultiple⟩
  refine ⟨-(multiple : Int), ?_⟩
  have hmultipleInt :
      (value : Int) + modularNegation modulus value =
        (modulus : Int) * multiple := by
    exact_mod_cast hmultiple
  calc
    -(value : Int) - modularNegation modulus value =
        -((value : Int) + modularNegation modulus value) := by omega
    _ = -((modulus : Int) * multiple) :=
      congrArg Neg.neg hmultipleInt
    _ = (modulus : Int) * -(multiple : Int) := by simp

@[simp]
theorem centeredModDistance_zero (modulus : Nat) :
    centeredModDistance modulus 0 = 0 := by
  simp [centeredModDistance]

theorem centeredModDistance_le_residue (modulus value : Nat) :
    centeredModDistance modulus value ≤ value % modulus := by
  exact Nat.min_le_left _ _

theorem centeredModDistance_le_complement (modulus value : Nat) :
    centeredModDistance modulus value ≤ modulus - value % modulus := by
  exact Nat.min_le_right _ _

/-- Centered distance depends only on the residue class of the value. -/
theorem centeredModDistance_eq_of_modEq {modulus left right : Nat}
    (h : left ≡ right [MOD modulus]) :
    centeredModDistance modulus left =
      centeredModDistance modulus right := by
  unfold centeredModDistance Nat.ModEq at *
  rw [h]

/-- Scaling both a residue and its modulus scales centered distance by the
same natural factor. -/
theorem centeredModDistance_mul_left (scale modulus value : Nat) :
    centeredModDistance (scale * modulus) (scale * value) =
      scale * centeredModDistance modulus value := by
  unfold centeredModDistance
  rw [Nat.mul_mod_mul_left]
  change min (scale * (value % modulus))
      (scale * modulus - scale * (value % modulus)) =
    scale * min (value % modulus) (modulus - value % modulus)
  rw [← Nat.mul_sub_left_distrib]
  exact Nat.mul_min_mul_left scale (value % modulus)
    (modulus - value % modulus)

/-- Encode the open centered window of radius `radius` as two ordinary
half-intervals.  Values on the lower side keep their residue; values on the
upper side are encoded after `radius` by their distance from the modulus. -/
def centeredWindowCode (modulus radius value : Nat) : Nat :=
  if value % modulus < radius then value % modulus
  else radius + (modulus - value % modulus)

/-- A residue in the open centered window has code below `2 * radius`. -/
theorem centeredWindowCode_lt {modulus radius value : Nat}
    (hmodulus : 0 < modulus)
    (hwindow : centeredModDistance modulus value < radius) :
    centeredWindowCode modulus radius value < 2 * radius := by
  have hresidue := Nat.mod_lt value hmodulus
  have hsides : value % modulus < radius ∨
      modulus - value % modulus < radius := by
    simpa [centeredModDistance, min_lt_iff] using hwindow
  unfold centeredWindowCode
  by_cases hlower : value % modulus < radius
  · rw [if_pos hlower]
    omega
  · rw [if_neg hlower]
    omega

/-- The two-half encoding is injective on the open centered window. -/
theorem centeredWindowCode_injectiveOn {modulus radius : Nat} :
    Set.InjOn (centeredWindowCode modulus radius)
      {value | value < modulus ∧
        centeredModDistance modulus value < radius} := by
  intro left hleft right hright heq
  have hleftMod : left % modulus = left := Nat.mod_eq_of_lt hleft.1
  have hrightMod : right % modulus = right := Nat.mod_eq_of_lt hright.1
  have hleftSides : left < radius ∨ modulus - left < radius := by
    simpa [centeredModDistance, hleftMod, min_lt_iff] using hleft.2
  have hrightSides : right < radius ∨ modulus - right < radius := by
    simpa [centeredModDistance, hrightMod, min_lt_iff] using hright.2
  unfold centeredWindowCode at heq
  rw [hleftMod, hrightMod] at heq
  by_cases hleftLower : left < radius
  · rw [if_pos hleftLower] at heq
    by_cases hrightLower : right < radius
    · simpa [if_pos hrightLower] using heq
    · rw [if_neg hrightLower] at heq
      have hrightComplementPos : 0 < modulus - right :=
        Nat.sub_pos_of_lt hright.1
      omega
  · rw [if_neg hleftLower] at heq
    by_cases hrightLower : right < radius
    · rw [if_pos hrightLower] at heq
      have hleftComplementPos : 0 < modulus - left :=
        Nat.sub_pos_of_lt hleft.1
      omega
    · rw [if_neg hrightLower] at heq
      have hleftCancel : modulus - left + left = modulus :=
        Nat.sub_add_cancel (Nat.le_of_lt hleft.1)
      have hrightCancel : modulus - right + right = modulus :=
        Nat.sub_add_cancel (Nat.le_of_lt hright.1)
      omega

/-- At most `2 * radius` residues modulo a positive modulus lie in the open
centered window. -/
theorem card_centeredWindow_lt_le (modulus radius : Nat)
    (hmodulus : 0 < modulus) :
    (Finset.univ.filter fun value : Fin modulus =>
      centeredModDistance modulus value.val < radius).card ≤ 2 * radius := by
  classical
  let source := Finset.univ.filter fun value : Fin modulus =>
    centeredModDistance modulus value.val < radius
  have hmaps : Set.MapsTo (fun value : Fin modulus =>
      centeredWindowCode modulus radius value.val)
      (↑source : Set (Fin modulus)) (↑(Finset.range (2 * radius))) := by
    intro value hvalue
    rw [Finset.mem_coe, Finset.mem_range]
    exact centeredWindowCode_lt hmodulus (Finset.mem_filter.mp hvalue).2
  have hinjective : Set.InjOn (fun value : Fin modulus =>
      centeredWindowCode modulus radius value.val)
      (↑source : Set (Fin modulus)) := by
    intro left hleft right hright heq
    apply Fin.ext
    apply centeredWindowCode_injectiveOn
    · exact ⟨left.isLt, (Finset.mem_filter.mp hleft).2⟩
    · exact ⟨right.isLt, (Finset.mem_filter.mp hright).2⟩
    · exact heq
  have hcard := Finset.card_le_card_of_injOn
    (fun value : Fin modulus => centeredWindowCode modulus radius value.val)
    hmaps hinjective
  simpa [source] using hcard

/-- Multiplication modulo `2^bits` sends at most `2^(window+1)` indices into
the open centered window of radius `2^window`, provided the nonzero
multiplier itself is shorter than that radius.  The proof factors the
multiplier into its two-adic scale and odd part; the odd part permutes the
reduced residue ring, while the scale is exactly the fiber multiplicity. -/
theorem card_centered_mul_pow_two_window_lt_le
    {bits window multiplier : Nat} (hwindow : window ≤ bits)
    (hmultiplierPos : 0 < multiplier)
    (hmultiplierLt : multiplier < 2 ^ window) :
    (Finset.univ.filter fun index : Fin (2 ^ bits) =>
      centeredModDistance (2 ^ bits) (multiplier * index.val) <
        2 ^ window).card ≤ 2 ^ (window + 1) := by
  classical
  obtain ⟨valuation, oddPart, hodd, hfactor⟩ :=
    Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt hmultiplierPos)
  have hoddPos : 0 < oddPart := hodd.pos
  have hscaleLe : 2 ^ valuation ≤ multiplier := by
    rw [hfactor]
    exact Nat.le_mul_of_pos_right _ hoddPos
  have hvaluationLt : valuation < window :=
    (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp
      (hscaleLe.trans_lt hmultiplierLt)
  have hvaluationLeBits : valuation ≤ bits :=
    hvaluationLt.le.trans hwindow
  let scale := 2 ^ valuation
  let reducedModulus := 2 ^ (bits - valuation)
  let reducedRadius := 2 ^ (window - valuation)
  have hscalePos : 0 < scale := by
    dsimp [scale]
    exact Nat.two_pow_pos _
  have hreducedModulusPos : 0 < reducedModulus := by
    dsimp [reducedModulus]
    exact Nat.two_pow_pos _
  have hmodulusEq : 2 ^ bits = scale * reducedModulus := by
    dsimp [scale, reducedModulus]
    rw [← pow_add]
    congr 1
    omega
  have hradiusEq : 2 ^ window = scale * reducedRadius := by
    dsimp [scale, reducedRadius]
    rw [← pow_add]
    congr 1
    omega
  let source := Finset.univ.filter fun index : Fin (2 ^ bits) =>
    centeredModDistance (2 ^ bits) (multiplier * index.val) <
      2 ^ window
  let reducedResidue (index : Fin (2 ^ bits)) : Nat :=
    (oddPart * (index.val % reducedModulus)) % reducedModulus
  let encode (index : Fin (2 ^ bits)) : Nat × Nat :=
    (index.val / reducedModulus,
      centeredWindowCode reducedModulus reducedRadius
        (reducedResidue index))
  let target := (Finset.range scale).product (Finset.range (2 * reducedRadius))
  have hreducedWindow (index : Fin (2 ^ bits)) (hindex : index ∈ source) :
      centeredModDistance reducedModulus (reducedResidue index) <
        reducedRadius := by
    have hjmod : index.val % reducedModulus ≡ index.val
        [MOD reducedModulus] := Nat.mod_modEq _ _
    have hscaled := (hjmod.mul_left oddPart).mul_left' scale
    have hmod : multiplier * index.val ≡
        scale * (oddPart * (index.val % reducedModulus)) [MOD 2 ^ bits] := by
      unfold Nat.ModEq at hscaled ⊢
      rw [hfactor]
      simpa [hmodulusEq, mul_assoc] using hscaled.symm
    have hdistance :
        centeredModDistance (2 ^ bits) (multiplier * index.val) =
          scale * centeredModDistance reducedModulus
            (reducedResidue index) := by
      rw [centeredModDistance_eq_of_modEq hmod]
      have hchangeModulus :
          centeredModDistance (2 ^ bits)
              (scale * (oddPart * (index.val % reducedModulus))) =
            centeredModDistance (scale * reducedModulus)
              (scale * (oddPart * (index.val % reducedModulus))) :=
        congrArg (fun modulus => centeredModDistance modulus
          (scale * (oddPart * (index.val % reducedModulus)))) hmodulusEq
      rw [hchangeModulus, centeredModDistance_mul_left]
      congr 1
      unfold reducedResidue
      exact centeredModDistance_eq_of_modEq (Nat.mod_modEq _ _).symm
    have hsourceWindow := (Finset.mem_filter.mp hindex).2
    rw [hdistance, hradiusEq] at hsourceWindow
    exact (Nat.mul_lt_mul_left hscalePos).mp hsourceWindow
  have hmaps : Set.MapsTo encode (↑source : Set (Fin (2 ^ bits)))
      (↑target : Set (Nat × Nat)) := by
    intro index hindex
    change encode index ∈ target
    dsimp only [encode, target]
    apply Finset.mk_mem_product
    · rw [Finset.mem_range, Nat.div_lt_iff_lt_mul hreducedModulusPos,
        ← hmodulusEq]
      exact index.isLt
    · rw [Finset.mem_range]
      exact centeredWindowCode_lt hreducedModulusPos
        (hreducedWindow index hindex)
  have hinjective : Set.InjOn encode (↑source : Set (Fin (2 ^ bits))) := by
    intro left hleft right hright heq
    have hhigh : left.val / reducedModulus =
        right.val / reducedModulus := congrArg Prod.fst heq
    have hcode : centeredWindowCode reducedModulus reducedRadius
        (reducedResidue left) =
      centeredWindowCode reducedModulus reducedRadius
        (reducedResidue right) := congrArg Prod.snd heq
    have hreducedEq : reducedResidue left = reducedResidue right := by
      apply centeredWindowCode_injectiveOn
      · exact ⟨Nat.mod_lt _ hreducedModulusPos,
          hreducedWindow left hleft⟩
      · exact ⟨Nat.mod_lt _ hreducedModulusPos,
          hreducedWindow right hright⟩
      · exact hcode
    have hmulMod : oddPart * (left.val % reducedModulus) ≡
        oddPart * (right.val % reducedModulus) [MOD reducedModulus] := by
      unfold Nat.ModEq
      simpa [reducedResidue] using hreducedEq
    have hcoprime : Nat.Coprime oddPart reducedModulus := by
      dsimp [reducedModulus]
      exact hodd.coprime_two_right.pow_right _
    have hlowMod : left.val % reducedModulus ≡
        right.val % reducedModulus [MOD reducedModulus] :=
      Nat.ModEq.cancel_left_of_coprime hcoprime.symm hmulMod
    have hlow : left.val % reducedModulus =
        right.val % reducedModulus :=
      hlowMod.eq_of_lt_of_lt
        (Nat.mod_lt _ hreducedModulusPos)
        (Nat.mod_lt _ hreducedModulusPos)
    apply Fin.ext
    calc
      left.val = left.val % reducedModulus +
          reducedModulus * (left.val / reducedModulus) := by
        simpa [Nat.mul_comm] using
          (Nat.mod_add_div left.val reducedModulus).symm
      _ = right.val % reducedModulus +
          reducedModulus * (right.val / reducedModulus) := by
        rw [hlow, hhigh]
      _ = right.val := by
        simpa [Nat.mul_comm] using Nat.mod_add_div right.val reducedModulus
  have hcard := Finset.card_le_card_of_injOn encode hmaps hinjective
  have htargetCard : target.card = 2 ^ (window + 1) := by
    change ((Finset.range scale).product
      (Finset.range (2 * reducedRadius))).card = 2 ^ (window + 1)
    have hproductCard :
        ((Finset.range scale).product
          (Finset.range (2 * reducedRadius))).card =
        scale * (2 * reducedRadius) := by
      simpa only [Finset.product_eq_sprod, Finset.card_range] using
        Finset.card_product (Finset.range scale)
          (Finset.range (2 * reducedRadius))
    rw [hproductCard]
    calc
      scale * (2 * reducedRadius) = (scale * reducedRadius) * 2 := by
        rw [Nat.mul_comm 2 reducedRadius, Nat.mul_assoc]
      _ = 2 ^ window * 2 := by rw [← hradiusEq]
      _ = 2 ^ (window + 1) := by rw [pow_succ]
  rw [htargetCard] at hcard
  simpa only [source] using hcard

/-- A residue in the nonnegative half of the canonical interval is the
centered representative of every congruent natural value. -/
theorem centeredResidue_eq_natCast_of_modEq {modulus value residue : Nat}
    (hresidueLt : residue < modulus)
    (hhalf : 2 * residue ≤ modulus)
    (hmod : value ≡ residue [MOD modulus]) :
    centeredResidue modulus value = residue := by
  unfold centeredResidue
  rw [Nat.mod_eq_of_modEq hmod hresidueLt, if_pos hhalf]

/-- A residue in the upper half of the canonical interval is represented by
subtracting the modulus. -/
theorem centeredResidue_eq_sub_of_modEq {modulus value residue : Nat}
    (hresidueLt : residue < modulus)
    (hhalf : modulus < 2 * residue)
    (hmod : value ≡ residue [MOD modulus]) :
    centeredResidue modulus value = (residue : Int) - modulus := by
  unfold centeredResidue
  rw [Nat.mod_eq_of_modEq hmod hresidueLt, if_neg (Nat.not_le_of_gt hhalf)]

/-- Outside the central quarter of a circle of size `4 * width`, translation
by the half-period lands inside that quarter.  Endpoints are included in the
central window, so this is the implication needed for the source's
conservative Fourier-sampling count. -/
theorem centeredModDistance_add_half_le_of_lt {width value : Nat}
    (hwidth : 0 < width)
    (houtside : width < centeredModDistance (4 * width) value) :
    centeredModDistance (4 * width) (value + 2 * width) ≤ width := by
  let residue := value % (4 * width)
  have hmodulus : 0 < 4 * width := by omega
  have hresidueLt : residue < 4 * width :=
    Nat.mod_lt value hmodulus
  have hwidthLtResidue : width < residue :=
    houtside.trans_le (centeredModDistance_le_residue _ _)
  have hwidthLtComplement : width < 4 * width - residue :=
    houtside.trans_le (centeredModDistance_le_complement _ _)
  have hresidueLtThree : residue < 3 * width := by omega
  by_cases hleft : residue < 2 * width
  · have hshift : (value + 2 * width) % (4 * width) =
        residue + 2 * width := by
      rw [Nat.add_mod]
      change (residue + 2 * width % (4 * width)) % (4 * width) = _
      rw [Nat.mod_eq_of_lt (by omega : 2 * width < 4 * width),
        Nat.mod_eq_of_lt (by omega : residue + 2 * width < 4 * width)]
    unfold centeredModDistance
    rw [hshift]
    exact (Nat.min_le_right _ _).trans (by omega)
  · have htwoLe : 2 * width ≤ residue := Nat.le_of_not_gt hleft
    have hshift : (value + 2 * width) % (4 * width) =
        residue - 2 * width := by
      rw [Nat.add_mod]
      change (residue + 2 * width % (4 * width)) % (4 * width) = _
      rw [Nat.mod_eq_of_lt (by omega : 2 * width < 4 * width)]
      have heq : residue + 2 * width =
          4 * width + (residue - 2 * width) := by omega
      rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
      rw [Nat.mod_mod]
      exact Nat.mod_eq_of_lt (by omega)
    unfold centeredModDistance
    rw [hshift]
    exact (Nat.min_le_left _ _).trans (by omega)

/-- At least half of the residues modulo `2^bits` send a nonzero multiplier
into the centered quarter-window.  The proof factors the multiplier into its
two-adic and odd parts.  Translation by `2^(bits-v₂(multiplier)-1)` is
injective and changes the multiplied residue by exactly one half-period, so it
maps every bad residue to a good one. -/
theorem pow_two_half_le_card_centered_mul_quarter
    {bits multiplier : Nat} (hbits : 2 ≤ bits)
    (hmultiplierPos : 0 < multiplier)
    (hmultiplierLt : multiplier < 2 ^ bits) :
    2 ^ (bits - 1) ≤
      (Finset.univ.filter fun index : Fin (2 ^ bits) =>
        centeredModDistance (2 ^ bits) (multiplier * index.val) ≤
          2 ^ (bits - 2)).card := by
  classical
  obtain ⟨valuation, oddPart, hodd, hfactor⟩ :=
    Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt hmultiplierPos)
  have hoddPos : 0 < oddPart := hodd.pos
  have hpowLe : 2 ^ valuation ≤ multiplier := by
    rw [hfactor]
    exact Nat.le_mul_of_pos_right _ hoddPos
  have hvaluationLt : valuation < bits :=
    (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp
      (hpowLe.trans_lt hmultiplierLt)
  let modulus := 2 ^ bits
  let quarter := 2 ^ (bits - 2)
  let half := 2 ^ (bits - 1)
  let shift := 2 ^ (bits - valuation - 1)
  have hquarterPos : 0 < quarter := by
    unfold quarter
    exact Nat.two_pow_pos _
  have hmodulusEq : modulus = 4 * quarter := by
    unfold modulus quarter
    calc
      2 ^ bits = 2 ^ ((bits - 2) + 2) := by
        congr 1
        omega
      _ = 4 * 2 ^ (bits - 2) := by
        rw [pow_add]
        change 2 ^ (bits - 2) * 4 = 4 * 2 ^ (bits - 2)
        exact Nat.mul_comm _ _
  have hhalfEq : half = 2 * quarter := by
    unfold half quarter
    calc
      2 ^ (bits - 1) = 2 ^ ((bits - 2) + 1) := by
        congr 1
        omega
      _ = 2 * 2 ^ (bits - 2) := by
        rw [pow_add]
        change 2 ^ (bits - 2) * 2 = 2 * 2 ^ (bits - 2)
        exact Nat.mul_comm _ _
  have hpowShift : 2 ^ valuation * shift = half := by
    unfold shift half
    rw [← pow_add]
    congr 1
    omega
  obtain ⟨oddWitness, hoddEq⟩ := hodd
  have hmultiplierShift :
      multiplier * shift ≡ half [MOD modulus] := by
    have htwiceHalf : 2 * half = modulus := by omega
    calc
      multiplier * shift = oddPart * (2 ^ valuation * shift) := by
        rw [hfactor]
        ac_rfl
      _ = oddPart * half := by rw [hpowShift]
      _ = (2 * oddWitness + 1) * half := by rw [hoddEq]
      _ = 2 * oddWitness * half + half := by
        rw [Nat.add_mul, Nat.one_mul]
      _ = (2 * half) * oddWitness + half := by ac_rfl
      _ = modulus * oddWitness + half := by rw [htwiceHalf]
      _ ≡ half [MOD modulus] := Nat.ModEq.modulus_mul_add
  let good : Fin modulus → Prop := fun index =>
    centeredModDistance modulus (multiplier * index.val) ≤ quarter
  let translate : Fin modulus → Fin modulus := fun index =>
    ⟨(index.val + shift) % modulus,
      Nat.mod_lt _ (by rw [hmodulusEq]; omega)⟩
  have htranslateInjective : Function.Injective translate := by
    intro left right heq
    apply Fin.ext
    have hmod : left.val + shift ≡ right.val + shift [MOD modulus] := by
      unfold translate at heq
      exact congrArg Fin.val heq
    have hcancel : left.val ≡ right.val [MOD modulus] :=
      Nat.ModEq.add_right_cancel' shift hmod
    unfold Nat.ModEq at hcancel
    rw [Nat.mod_eq_of_lt left.isLt, Nat.mod_eq_of_lt right.isLt] at hcancel
    exact hcancel
  have htranslateBadToGood : Set.MapsTo translate
      (↑(Finset.univ.filter fun index : Fin modulus => ¬ good index) :
        Set (Fin modulus))
      (↑(Finset.univ.filter good) : Set (Fin modulus)) := by
    intro index hindex
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] at hindex ⊢
    have houtside : quarter <
        centeredModDistance modulus (multiplier * index.val) :=
      Nat.lt_of_not_ge hindex
    have htranslatedMod :
        multiplier * (translate index).val ≡
          multiplier * index.val + half [MOD modulus] := by
      have hvalue : (translate index).val ≡
          index.val + shift [MOD modulus] := by
        unfold translate
        exact Nat.mod_modEq _ _
      calc
        multiplier * (translate index).val ≡
            multiplier * (index.val + shift) [MOD modulus] :=
          hvalue.mul_left multiplier
        _ = multiplier * index.val + multiplier * shift := by
          rw [Nat.mul_add]
        _ ≡ multiplier * index.val + half [MOD modulus] :=
          Nat.ModEq.rfl.add hmultiplierShift
    change centeredModDistance modulus
      (multiplier * (translate index).val) ≤ quarter
    rw [centeredModDistance_eq_of_modEq htranslatedMod]
    have houtside' : quarter < centeredModDistance (4 * quarter)
        (multiplier * index.val) := by
      rw [← hmodulusEq]
      exact houtside
    have hinside := centeredModDistance_add_half_le_of_lt
      hquarterPos houtside'
    simpa only [← hmodulusEq, ← hhalfEq] using hinside
  have hbadLeGood :
      (Finset.univ.filter fun index : Fin modulus => ¬ good index).card ≤
        (Finset.univ.filter good).card :=
    Finset.card_le_card_of_injOn translate htranslateBadToGood
      htranslateInjective.injOn
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin modulus))) good
  have hcard : (Finset.univ : Finset (Fin modulus)).card = modulus := by
    simp
  rw [hcard] at hpartition
  have hmodulusHalf : modulus = 2 * half := by omega
  have hhalfLe : half ≤ (Finset.univ.filter good).card := by omega
  simpa [modulus, quarter, half, good] using hhalfLe

/-- The centered distance never exceeds half the modulus. -/
theorem two_mul_centeredModDistance_le {modulus value : Nat}
    (hmodulus : 0 < modulus) :
    2 * centeredModDistance modulus value ≤ modulus := by
  let residue := value % modulus
  have hresidue : residue < modulus := Nat.mod_lt value hmodulus
  unfold centeredModDistance
  change 2 * min residue (modulus - residue) ≤ modulus
  by_cases hleft : residue ≤ modulus - residue
  · rw [Nat.min_eq_left hleft]
    omega
  · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hleft))]
    omega

/-- The absolute value of the signed centered representative is exactly the
unsigned centered modular distance. -/
theorem natAbs_centeredResidue {modulus value : Nat}
    (hmodulus : 0 < modulus) :
    (centeredResidue modulus value).natAbs =
      centeredModDistance modulus value := by
  let residue := value % modulus
  have hresidue : residue < modulus := Nat.mod_lt value hmodulus
  have hresidueLe : residue ≤ modulus := Nat.le_of_lt hresidue
  unfold centeredResidue centeredModDistance
  change (if 2 * residue ≤ modulus then (residue : Int)
      else (residue : Int) - modulus).natAbs =
    min residue (modulus - residue)
  by_cases hhalf : 2 * residue ≤ modulus
  · rw [if_pos hhalf, Int.natAbs_natCast, Nat.min_eq_left]
    omega
  · rw [if_neg hhalf, Nat.min_eq_right]
    · exact Int.natAbs_natCast_sub_natCast_of_le hresidueLe
    · omega

/-- The signed centered representative lies in the principal half-modulus
interval, expressed without division. -/
theorem two_mul_natAbs_centeredResidue_le {modulus value : Nat}
    (hmodulus : 0 < modulus) :
    2 * (centeredResidue modulus value).natAbs ≤ modulus := by
  rw [natAbs_centeredResidue hmodulus]
  exact two_mul_centeredModDistance_le hmodulus

/-- The signed centered representative is congruent to the original value
modulo the positive modulus. -/
theorem centeredResidue_modEq (modulus value : Nat) :
    Int.ModEq modulus (centeredResidue modulus value) value := by
  let residue := value % modulus
  have hresidue : Int.ModEq modulus residue value := by
    rw [Int.natCast_modEq_iff]
    exact Nat.mod_modEq value modulus
  have hmodulusZero : Int.ModEq modulus modulus 0 := by
    rw [Int.modEq_zero_iff_dvd]
  unfold centeredResidue
  change Int.ModEq modulus
    (if 2 * residue ≤ modulus then (residue : Int)
      else (residue : Int) - modulus) value
  by_cases hhalf : 2 * residue ≤ modulus
  · rw [if_pos hhalf]
    exact hresidue
  · rw [if_neg hhalf]
    simpa using hresidue.sub hmodulusZero

/-- The signed centered residue has least absolute value among all integer
representatives of the same residue class. -/
theorem centeredModDistance_le_natAbs_of_intModEq
    {modulus value : Nat} {representative : Int}
    (hmodulus : 0 < modulus)
    (hrepresentative : Int.ModEq modulus representative value) :
    centeredModDistance modulus value ≤ representative.natAbs := by
  let centered := centeredResidue modulus value
  have hcenteredBound : 2 * centered.natAbs ≤ modulus := by
    exact two_mul_natAbs_centeredResidue_le hmodulus
  have hcenteredMod : Int.ModEq modulus centered representative :=
    (centeredResidue_modEq modulus value).trans hrepresentative.symm
  rcases Int.modEq_iff_add_fac.mp hcenteredMod with
    ⟨multiple, hrepresentativeEq⟩
  rw [← natAbs_centeredResidue hmodulus]
  change centered.natAbs ≤ representative.natAbs
  have hcenteredBoundInt :
      2 * |centered| ≤ (modulus : Int) := by
    have hcast :
        (2 : Int) * (centered.natAbs : Int) ≤ (modulus : Int) := by
      exact_mod_cast hcenteredBound
    simpa only [Int.natCast_natAbs] using hcast
  have hcenteredUpper : 2 * centered ≤ (modulus : Int) := by
    have hle := le_abs_self centered
    nlinarith
  have hcenteredLower : -(modulus : Int) ≤ 2 * centered := by
    have hle := neg_abs_le centered
    nlinarith
  rw [hrepresentativeEq, Int.natAbs_le_iff_sq_le]
  rcases lt_trichotomy multiple 0 with hmultipleNeg | hmultipleZero |
      hmultiplePos
  · have hmultipleLe : multiple ≤ -1 := by omega
    have hproductLe :
        (modulus : Int) * multiple ≤ -(modulus : Int) := by
      have hmul := mul_le_mul_of_nonneg_left hmultipleLe
        (show (0 : Int) ≤ (modulus : Int) by
          exact_mod_cast hmodulus.le)
      nlinarith
    nlinarith [sq_nonneg ((modulus : Int) * multiple)]
  · subst multiple
    simp
  · have hmultipleOne : 1 ≤ multiple := by omega
    have hmodulusLeProduct :
        (modulus : Int) ≤ (modulus : Int) * multiple := by
      have hmul := mul_le_mul_of_nonneg_left hmultipleOne
        (show (0 : Int) ≤ (modulus : Int) by
          exact_mod_cast hmodulus.le)
      nlinarith
    nlinarith [sq_nonneg ((modulus : Int) * multiple)]

end NumberTheory
end QuantumAlg

end
