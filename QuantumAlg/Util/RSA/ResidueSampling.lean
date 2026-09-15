/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.Combinatorics
import all QuantumAlg.Util.NumberTheory.ExactArithmetic
import all QuantumAlg.Util.ResidueEncoding
import Batteries.Data.Fin.Coding
import Batteries.Data.Fin.Lemmas

/-!
# Fixed-width RSA residue sampling

This module contains the quantum-free semantics of decoding one fixed random
bit string into a fixed number of equal-width residue proposals, selecting the
first proposal in the public interval `[1, N)`, and preparing either a unit or
an early nontrivial gcd factor. Resource accounting belongs to the closed
algorithm syntax; this module owns only the deterministic mathematics.
-/

section

namespace QuantumAlg
namespace RSA

/-- Decode word `index` from a packed little-endian sequence of equal-width
words. The outer `Fin` bound makes every decoded word canonical. -/
def decodeFixedWidthWord (wordWidth wordCount : Nat)
    (bits : Fin (2 ^ (wordCount * wordWidth))) (index : Fin wordCount) :
    Fin (2 ^ wordWidth) :=
  ⟨bits.val / 2 ^ (index.val * wordWidth) % 2 ^ wordWidth,
    Nat.mod_lt _ (pow_pos (by decide) wordWidth)⟩

/-- Cardinality identity behind fixed-width word packing. -/
theorem fixedWidthWords_card (wordWidth wordCount : Nat) :
    2 ^ (wordCount * wordWidth) = (2 ^ wordWidth) ^ wordCount := by
  rw [Nat.mul_comm, pow_mul]

/-- Packing equivalence between one fixed random bit string and a vector of
equal-width random words.  This is the executable bridge used later to turn
bit sampling into an exact finite counting argument. -/
def fixedWidthWordsEquiv (wordWidth wordCount : Nat) :
    Fin (2 ^ (wordCount * wordWidth)) ≃
      (Fin wordCount → Fin (2 ^ wordWidth)) where
  toFun bits :=
    Fin.decodeFun (Fin.cast (fixedWidthWords_card wordWidth wordCount) bits)
  invFun words :=
    Fin.cast (fixedWidthWords_card wordWidth wordCount).symm
      (Fin.encodeFun words)
  left_inv bits := by
    simp
  right_inv words := by
    simp

/-- Decode all fixed-width proposals from one packed random bit string. -/
def decodeFixedWidthWords (wordWidth wordCount : Nat)
    (bits : Fin (2 ^ (wordCount * wordWidth))) :
    Fin wordCount → Fin (2 ^ wordWidth) :=
  fixedWidthWordsEquiv wordWidth wordCount bits

private theorem decodeFun_val_eq_div_pow_mod {base count : Nat}
    (basePos : 0 < base) (value : Fin (base ^ count))
    (index : Fin count) :
    (Fin.decodeFun value index).val =
      value.val / base ^ index.val % base := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count inductionHypothesis =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · change value.val % base = value.val / base ^ 0 % base
        simp
      · change
          (Fin.decodeFun
            (⟨value.val / base, by
              rw [Nat.div_lt_iff_lt_mul basePos]
              simpa [pow_succ] using value.isLt⟩ : Fin (base ^ count)) tail).val = _
        rw [inductionHypothesis]
        simp only [Fin.val_succ, pow_succ]
        rw [Nat.div_div_eq_div_mul]
        rw [Nat.mul_comm base (base ^ tail.val)]

/-- The vector decoder used by the sampler is the ordinary consecutive
little-endian word slicing formula.  This bridge lets the typed bit-reference
machine decode the same public packed sample without a host callback. -/
theorem decodeFixedWidthWords_eq_decodeFixedWidthWord
    (wordWidth wordCount : Nat)
    (bits : Fin (2 ^ (wordCount * wordWidth)))
    (index : Fin wordCount) :
    decodeFixedWidthWords wordWidth wordCount bits index =
      decodeFixedWidthWord wordWidth wordCount bits index := by
  apply Fin.ext
  change
    (Fin.decodeFun
      (Fin.cast (fixedWidthWords_card wordWidth wordCount) bits) index).val =
      bits.val / 2 ^ (index.val * wordWidth) % 2 ^ wordWidth
  rw [decodeFun_val_eq_div_pow_mod (pow_pos (by decide) wordWidth)]
  change bits.val / (2 ^ wordWidth) ^ index.val % 2 ^ wordWidth = _
  rw [← pow_mul]
  rw [Nat.mul_comm wordWidth index.val]

/-- Packing preserves the exact count of word vectors whose coordinates all
lie in a fixed finite set. -/
theorem card_filter_decodeFixedWidthWords_forall_mem
    (wordWidth wordCount : Nat) (s : Finset (Fin (2 ^ wordWidth))) :
    ((Finset.univ : Finset (Fin (2 ^ (wordCount * wordWidth)))).filter
      fun bits => ∀ index, decodeFixedWidthWords wordWidth wordCount bits index ∈ s).card =
        s.card ^ wordCount := by
  classical
  let packed : Finset (Fin (2 ^ (wordCount * wordWidth))) :=
    Finset.univ.filter fun bits =>
      ∀ index, decodeFixedWidthWords wordWidth wordCount bits index ∈ s
  let words : Finset (Fin wordCount → Fin (2 ^ wordWidth)) :=
    Finset.univ.filter fun vector => ∀ index, vector index ∈ s
  let packing : ↑packed ≃ ↑words :=
    (fixedWidthWordsEquiv wordWidth wordCount).subtypeEquiv fun bits => by
      simp only [packed, words, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
  calc
    ((Finset.univ : Finset (Fin (2 ^ (wordCount * wordWidth)))).filter
        fun bits => ∀ index,
          decodeFixedWidthWords wordWidth wordCount bits index ∈ s).card =
        Fintype.card ↑packed := by
      rw [Fintype.card_coe]
    _ = Fintype.card ↑words := Fintype.card_congr packing
    _ = words.card := Fintype.card_coe words
    _ = s.card ^ wordCount := by
      exact Finset.card_filter_pi_forall_mem s wordCount

/-- Exact count of nonempty packed word vectors whose first coordinate lies
in a fixed finite set.  Every admissible first word has an arbitrary
`wordCount`-word tail. -/
theorem card_filter_decodeFixedWidthWords_first_mem
    (wordWidth wordCount : Nat) (s : Finset (Fin (2 ^ wordWidth))) :
    ((Finset.univ :
        Finset (Fin (2 ^ ((wordCount + 1) * wordWidth)))).filter
      fun bits =>
        decodeFixedWidthWords wordWidth (wordCount + 1) bits 0 ∈ s).card =
      s.card * (2 ^ wordWidth) ^ wordCount := by
  classical
  let packed : Finset (Fin (2 ^ ((wordCount + 1) * wordWidth))) :=
    Finset.univ.filter fun bits =>
      decodeFixedWidthWords wordWidth (wordCount + 1) bits 0 ∈ s
  let words : Finset (Fin (wordCount + 1) → Fin (2 ^ wordWidth)) :=
    Finset.univ.filter fun vector => vector 0 ∈ s
  let packing : ↑packed ≃ ↑words :=
    (fixedWidthWordsEquiv wordWidth (wordCount + 1)).subtypeEquiv
      fun bits => by
        simp only [packed, words, Finset.mem_filter, Finset.mem_univ, true_and]
        rfl
  have hwords :
      words.card = s.card * (2 ^ wordWidth) ^ wordCount := by
    dsimp only [words]
    rw [← Fintype.piFinset_univ]
    rw [← Fintype.piFinset_update_eq_filter_piFinset_mem
      (fun _ : Fin (wordCount + 1) =>
        (Finset.univ : Finset (Fin (2 ^ wordWidth))))
      (0 : Fin (wordCount + 1)) (t := s) (by simp)]
    rw [Fintype.card_piFinset]
    calc
      (∏ index : Fin (wordCount + 1),
          (Function.update
            (fun _ : Fin (wordCount + 1) =>
              (Finset.univ : Finset (Fin (2 ^ wordWidth))))
            0 s index).card) =
          ∏ index : Fin (wordCount + 1),
            Function.update
              (fun _ : Fin (wordCount + 1) => 2 ^ wordWidth)
              0 s.card index := by
        apply Fintype.prod_congr
        intro index
        obtain rfl | hindex := eq_or_ne index 0
        · simp
        · simp [hindex]
      _ = s.card * (2 ^ wordWidth) ^ wordCount := by
        have htailCard :
            ((Finset.univ : Finset (Fin (wordCount + 1))) \ {0}).card =
              wordCount := by
          rw [Finset.card_sdiff_of_subset (by simp)]
          simp
        rw [Finset.prod_update_of_mem
          (Finset.mem_univ (0 : Fin (wordCount + 1)))]
        simp [htailCard]
  calc
    ((Finset.univ :
        Finset (Fin (2 ^ ((wordCount + 1) * wordWidth)))).filter
      fun bits =>
        decodeFixedWidthWords wordWidth (wordCount + 1) bits 0 ∈ s).card =
        Fintype.card ↑packed := by
      rw [Fintype.card_coe]
    _ = Fintype.card ↑words := Fintype.card_congr packing
    _ = words.card := Fintype.card_coe words
    _ = s.card * (2 ^ wordWidth) ^ wordCount := hwords

/-- Packing also transports the union bound for a word vector with at least
one exceptional coordinate. -/
theorem card_filter_decodeFixedWidthWords_exists_mem_le
    (wordWidth wordCount : Nat) (s : Finset (Fin (2 ^ wordWidth))) :
    ((Finset.univ : Finset (Fin (2 ^ (wordCount * wordWidth)))).filter
      fun bits => ∃ index, decodeFixedWidthWords wordWidth wordCount bits index ∈ s).card ≤
        wordCount * s.card * (2 ^ wordWidth) ^ (wordCount - 1) := by
  classical
  let packed : Finset (Fin (2 ^ (wordCount * wordWidth))) :=
    Finset.univ.filter fun bits =>
      ∃ index, decodeFixedWidthWords wordWidth wordCount bits index ∈ s
  let words : Finset (Fin wordCount → Fin (2 ^ wordWidth)) :=
    Finset.univ.filter fun vector => ∃ index, vector index ∈ s
  let packing : ↑packed ≃ ↑words :=
    (fixedWidthWordsEquiv wordWidth wordCount).subtypeEquiv fun bits => by
      simp only [packed, words, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
  calc
    ((Finset.univ : Finset (Fin (2 ^ (wordCount * wordWidth)))).filter
        fun bits => ∃ index,
          decodeFixedWidthWords wordWidth wordCount bits index ∈ s).card =
        Fintype.card ↑packed := by
      rw [Fintype.card_coe]
    _ = Fintype.card ↑words := Fintype.card_congr packing
    _ = words.card := Fintype.card_coe words
    _ ≤ wordCount * s.card * (2 ^ wordWidth) ^ (wordCount - 1) := by
      simpa using Finset.card_filter_pi_exists_mem_le s wordCount

/-- A proposal is eligible exactly when it is the canonical representative of
one public nonzero residue modulo `modulus`. -/
def ResidueEligible (modulus candidate : Nat) : Prop :=
  0 < candidate ∧ candidate < modulus

instance residueEligibleDecidable (modulus candidate : Nat) :
    Decidable (ResidueEligible modulus candidate) := by
  unfold ResidueEligible
  infer_instance

/-- Fixed-width words accepted as public nonzero residues modulo `modulus`. -/
def eligibleResidueCandidates (modulus wordWidth : Nat) :
    Finset (Fin (2 ^ wordWidth)) :=
  Finset.univ.filter fun candidate => ResidueEligible modulus candidate.val

/-- Fixed-width words rejected before the gcd/unit preparation step. -/
def rejectedResidueCandidates (modulus wordWidth : Nat) :
    Finset (Fin (2 ^ wordWidth)) :=
  Finset.univ.filter fun candidate => ¬ ResidueEligible modulus candidate.val

/-- If the public modulus fits in one proposal word, there are exactly
`modulus - 1` accepted nonzero representatives. -/
theorem eligibleResidueCandidates_card {modulus wordWidth : Nat}
    (hmodulus : modulus ≤ 2 ^ wordWidth) :
    (eligibleResidueCandidates modulus wordWidth).card = modulus - 1 := by
  classical
  let accepted := eligibleResidueCandidates modulus wordWidth
  let enumerate : ↑accepted ≃ Fin (modulus - 1) := {
    toFun candidate := by
      have heligible :
          ResidueEligible modulus candidate.val.val := by
        exact (Finset.mem_filter.mp candidate.property).2
      exact ⟨candidate.val.val - 1,
        (Nat.sub_lt_sub_iff_right heligible.1).2 heligible.2⟩
    invFun index := by
      have hvalue : index.val + 1 < modulus := by
        simpa [Nat.add_comm] using
          (Nat.lt_sub_iff_add_lt').1 index.isLt
      have hword : index.val + 1 < 2 ^ wordWidth :=
        hvalue.trans_le hmodulus
      exact ⟨⟨index.val + 1, hword⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          exact ⟨Nat.zero_lt_succ index.val, hvalue⟩⟩⟩
    left_inv candidate := by
      apply Subtype.ext
      apply Fin.ext
      have heligible :
          ResidueEligible modulus candidate.val.val :=
        (Finset.mem_filter.mp candidate.property).2
      change candidate.val.val - 1 + 1 = candidate.val.val
      exact Nat.sub_add_cancel heligible.1
    right_inv index := by
      apply Fin.ext
      change (index.val + 1) - 1 = index.val
      omega }
  calc
    accepted.card = Fintype.card ↑accepted :=
      (Fintype.card_coe accepted).symm
    _ = Fintype.card (Fin (modulus - 1)) :=
      Fintype.card_congr enumerate
    _ = modulus - 1 := Fintype.card_fin _

/-- Rejected words are the complement of the exact accepted interval. -/
theorem rejectedResidueCandidates_card {modulus wordWidth : Nat}
    (hmodulus : modulus ≤ 2 ^ wordWidth) :
    (rejectedResidueCandidates modulus wordWidth).card =
      2 ^ wordWidth - (modulus - 1) := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2 ^ wordWidth))))
    (fun candidate => ResidueEligible modulus candidate.val)
  have haccepted := eligibleResidueCandidates_card hmodulus
  simp only [Finset.card_univ, Fintype.card_fin] at hpartition
  change
    (eligibleResidueCandidates modulus wordWidth).card +
        (rejectedResidueCandidates modulus wordWidth).card =
      2 ^ wordWidth at hpartition
  rw [haccepted] at hpartition
  omega

/-- Retain eligible proposals and reject zero or out-of-range words. -/
def classifyResidueProposals {wordWidth wordCount : Nat} (modulus : Nat)
    (proposals : Fin wordCount → Fin (2 ^ wordWidth)) :
    Fin wordCount → Option Nat :=
  fun index =>
    if _h : ResidueEligible modulus (proposals index).val then
      some (proposals index).val
    else
      none

/-- Select the first successful value from a fixed-length proposal vector. -/
def firstValidResidue {wordCount : Nat}
    (proposals : Fin wordCount → Option Nat) : Option Nat :=
  Fin.findSome? proposals

/-- Pack one word as the first word of a nonempty fixed-width proposal batch;
all later words are zero. -/
def firstWordBits (wordWidth wordCount : Nat)
    (candidate : Fin (2 ^ wordWidth)) :
    Fin (2 ^ ((wordCount + 1) * wordWidth)) :=
  ⟨candidate.val, lt_of_lt_of_le candidate.isLt <|
    Nat.pow_le_pow_right (by decide) <| by
      rw [Nat.add_mul]
      omega⟩

@[simp] theorem decodeFixedWidthWord_firstWordBits_zero
    (wordWidth wordCount : Nat) (candidate : Fin (2 ^ wordWidth)) :
    decodeFixedWidthWord wordWidth (wordCount + 1)
        (firstWordBits wordWidth wordCount candidate) 0 = candidate := by
  apply Fin.ext
  simp [decodeFixedWidthWord, firstWordBits, Nat.mod_eq_of_lt candidate.isLt]

@[simp] theorem decodeFixedWidthWords_firstWordBits_zero
    (wordWidth wordCount : Nat) (candidate : Fin (2 ^ wordWidth)) :
    decodeFixedWidthWords wordWidth (wordCount + 1)
        (firstWordBits wordWidth wordCount candidate) 0 = candidate := by
  apply Fin.ext
  change candidate.val % 2 ^ wordWidth = candidate.val
  exact Nat.mod_eq_of_lt candidate.isLt

/-- A successful first entry determines the fixed-vector selector. -/
theorem firstValidResidue_eq_first {wordCount candidate : Nat}
    (proposals : Fin (wordCount + 1) → Option Nat)
    (hfirst : proposals 0 = some candidate) :
    firstValidResidue proposals = some candidate := by
  exact Fin.findSome?_succ_of_some hfirst

/-- If the first fixed-width proposal is eligible, classification and
first-success selection return that proposal independently of the tail. -/
theorem firstValidResidue_classify_eq_first
    {wordWidth wordCount modulus : Nat}
    (proposals : Fin (wordCount + 1) → Fin (2 ^ wordWidth))
    (heligible : ResidueEligible modulus (proposals 0).val) :
    firstValidResidue (classifyResidueProposals modulus proposals) =
      some (proposals 0).val := by
  apply firstValidResidue_eq_first
  simp [classifyResidueProposals, heligible]

/-- The fixed-vector selector rejects exactly when every proposal rejects. -/
@[simp] theorem firstValidResidue_eq_none_iff {wordCount : Nat}
    (proposals : Fin wordCount → Option Nat) :
    firstValidResidue proposals = none ↔ ∀ index, proposals index = none := by
  exact Fin.findSome?_eq_none_iff

/-- Every value returned by the fixed-vector selector is one of its entries. -/
theorem exists_eq_some_of_firstValidResidue_eq_some
    {wordCount candidate : Nat} {proposals : Fin wordCount → Option Nat}
    (hselected : firstValidResidue proposals = some candidate) :
    ∃ index, proposals index = some candidate :=
  Fin.exists_eq_some_of_findSome?_eq_some hselected

/-- The classified selector rejects exactly when every decoded word lies
outside the public residue interval. -/
theorem firstValidResidue_classify_eq_none_iff
    {wordWidth wordCount : Nat} (modulus : Nat)
    (proposals : Fin wordCount → Fin (2 ^ wordWidth)) :
    firstValidResidue (classifyResidueProposals modulus proposals) = none ↔
      ∀ index, ¬ ResidueEligible modulus (proposals index).val := by
  rw [firstValidResidue_eq_none_iff]
  constructor
  · intro hall index heligible
    have := hall index
    simp [classifyResidueProposals, heligible] at this
  · intro hall index
    simp [classifyResidueProposals, hall index]

/-- A selected classified residue is the value of one eligible decoded word. -/
theorem exists_eligible_of_firstValidResidue_classify_eq_some
    {wordWidth wordCount modulus candidate : Nat}
    {proposals : Fin wordCount → Fin (2 ^ wordWidth)}
    (hselected :
      firstValidResidue (classifyResidueProposals modulus proposals) =
        some candidate) :
    ∃ index, (proposals index).val = candidate ∧
      ResidueEligible modulus candidate := by
  obtain ⟨index, hindex⟩ :=
    exists_eq_some_of_firstValidResidue_eq_some hselected
  simp only [classifyResidueProposals] at hindex
  split at hindex
  next heligible =>
    have hvalue := Option.some.inj hindex
    exact ⟨index, hvalue, hvalue ▸ heligible⟩
  next => simp at hindex

/-- A selected RSA residue together with the unit used by the fixed-cost
quantum circuit and an optional factor learned before that circuit. The
constructor is private: callers can only obtain this object from the closed
preparation semantics below. -/
structure PreparedResidue (modulus : Nat) where private mk ::
  /-- Selected public residue, or `1` when every proposal was rejected. -/
  candidate : Nat
  /-- Unit fed to the fixed-cost circuit; it is `1` on rejection/nonunit paths. -/
  unit : (ZMod modulus)ˣ
  /-- Nontrivial gcd discovered from a selected nonunit residue. -/
  earlyFactor : Option Nat
  /-- Every stored early factor is a genuine nontrivial divisor. -/
  earlyFactor_sound : ∀ factor, earlyFactor = some factor →
    factor ∣ modulus ∧ 1 < factor ∧ factor < modulus

/-- One sealed sampler-preparation execution.  Its result and Euclidean
arithmetic are constructed together from the selected residue. -/
structure PreparedResidueExecution (modulus : Nat) where
  private mk ::
  /-- Circuit unit and optional early factor produced by this execution. -/
  output : PreparedResidue modulus
  /-- Complete operand-derived option, gcd, and validation schedule. -/
  arithmetic : List NumberTheory.ArithmeticEvent

/-- Prepare the circuit unit and optional early factor from the selected public
residue.  A selected candidate is classified by one sealed Euclidean trace,
which supplies both the branch value and the dynamic arithmetic schedule. -/
def prepareResidueExecution (modulus : Nat) :
    Option Nat → PreparedResidueExecution modulus
  | none =>
      .mk
        { candidate := 1
          unit := 1
          earlyFactor := none
          earlyFactor_sound := by simp }
        [.natEq 0 1]
  | some candidate =>
      let gcdTrace := NumberTheory.euclideanGCDTrace candidate modulus
      let commonArithmetic :=
        [.natEq 1 1] ++ gcdTrace.arithmetic ++
          [ .natEq gcdTrace.value 1
          , .natLt 1 gcdTrace.value
          , .natLt gcdTrace.value modulus ]
      if hcoprime : gcdTrace.value = 1 then
        let coprime : Nat.Coprime candidate modulus := by
          change Nat.gcd candidate modulus = 1
          rw [← NumberTheory.euclideanGCDTrace_value]
          exact hcoprime
        .mk
          { candidate := candidate
            unit := ZMod.unitOfCoprime candidate coprime
            earlyFactor := none
            earlyFactor_sound := by simp }
          commonArithmetic
      else
        let factor := gcdTrace.value
        let result :=
          if 1 < factor ∧ factor < modulus then some factor else none
        .mk
          { candidate := candidate
            unit := 1
            earlyFactor := result
            earlyFactor_sound := by
              intro returned hreturned
              dsimp only [result] at hreturned
              split at hreturned
              next hnontrivial =>
                injection hreturned with heq
                subst returned
                have hfactor :
                    factor = Nat.gcd candidate modulus :=
                  NumberTheory.euclideanGCDTrace_value candidate modulus
                exact ⟨by
                    rw [hfactor]
                    exact Nat.gcd_dvd_right candidate modulus,
                  hnontrivial.1, hnontrivial.2⟩
              next _ => simp at hreturned }
          commonArithmetic

/-- Value projection of the unique sampler-preparation execution. -/
def prepareResidue (modulus : Nat) (selected : Option Nat) :
    PreparedResidue modulus :=
  (prepareResidueExecution modulus selected).output

/-- Dynamic arithmetic projection of the same sampler-preparation execution. -/
def prepareResidueArithmetic (modulus : Nat) (selected : Option Nat) :
    List NumberTheory.ArithmeticEvent :=
  (prepareResidueExecution modulus selected).arithmetic

/-- A rejected sampler slot performs one option-tag comparison. -/
theorem prepareResidueExecution_none_schoolbookCharge (modulus : Nat) :
    NumberTheory.arithmeticEventListCharge
        (prepareResidueExecution modulus none).arithmetic = 2 := by
  simp [prepareResidueExecution, NumberTheory.arithmeticEventListCharge,
    NumberTheory.ArithmeticEvent.schoolbookCharge,
    NumberTheory.ArithmeticEvent.operandWidth]

/-- A selected sampler residue has a cubic operand-derived preparation bound.
The envelope contains only the actual candidate and public-modulus widths. -/
theorem prepareResidueExecution_some_schoolbookCharge_le
    (modulus candidate : Nat) :
    NumberTheory.arithmeticEventListCharge
        (prepareResidueExecution modulus (some candidate)).arithmetic ≤
      2 ^ 8 * (Nat.size candidate + Nat.size modulus + 1) ^ 3 := by
  let gcdTrace := NumberTheory.euclideanGCDTrace candidate modulus
  let width := Nat.size candidate + Nat.size modulus + 1
  have hwidthPos : 1 ≤ width := by
    dsimp only [width]
    omega
  have hmaxWidth :
      max (Nat.size candidate) (Nat.size modulus) + 1 ≤ width := by
    dsimp only [width]
    omega
  have hgcd :
      gcdTrace.schoolbookCharge ≤ 16 * width ^ 3 := by
    exact
      (NumberTheory.euclideanGCDTrace_schoolbookCharge_cubic
        candidate modulus).trans
        (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hmaxWidth 3))
  have hgcdValueLe : Nat.gcd candidate modulus ≤ candidate + modulus := by
    cases candidate with
    | zero => simp
    | succ candidate =>
        exact
          (Nat.gcd_le_left modulus (Nat.succ_pos candidate)).trans
            (Nat.le_add_right _ _)
  have hgcdValueSize : Nat.size gcdTrace.value ≤ width := by
    rw [NumberTheory.euclideanGCDTrace_value]
    exact
      (Nat.size_le_size hgcdValueLe).trans
        ((NumberTheory.natSize_add_le_max_add_one candidate modulus).trans
          (by
            dsimp only [width]
            omega))
  have hcomparison :
      NumberTheory.arithmeticEventListCharge
          [ .natEq 1 1
          , .natEq gcdTrace.value 1
          , .natLt 1 gcdTrace.value
          , .natLt gcdTrace.value modulus ] ≤
        16 * width := by
    simp only [NumberTheory.arithmeticEventListCharge, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil,
      NumberTheory.ArithmeticEvent.schoolbookCharge,
      NumberTheory.ArithmeticEvent.operandWidth]
    have hone : Nat.size 1 ≤ width := by simp [width]
    omega
  have hwidthCube : width ≤ width ^ 3 := by
    simpa only [pow_one] using
      (pow_le_pow_right' hwidthPos (show 1 ≤ 3 by norm_num))
  have hcomparisonCubic :
      NumberTheory.arithmeticEventListCharge
          [ .natEq 1 1
          , .natEq gcdTrace.value 1
          , .natLt 1 gcdTrace.value
          , .natLt gcdTrace.value modulus ] ≤
        16 * width ^ 3 :=
    hcomparison.trans (Nat.mul_le_mul_left 16 hwidthCube)
  simp only [prepareResidueExecution]
  split <;>
    change
      NumberTheory.arithmeticEventListCharge
          ([.natEq 1 1] ++ gcdTrace.arithmetic ++
            [ .natEq gcdTrace.value 1
            , .natLt 1 gcdTrace.value
            , .natLt gcdTrace.value modulus ]) ≤
        2 ^ 8 * width ^ 3
  all_goals
    rw [NumberTheory.arithmeticEventListCharge_append,
      NumberTheory.arithmeticEventListCharge_append]
    have hprefix :
        NumberTheory.arithmeticEventListCharge [.natEq 1 1] = 2 := by
      norm_num [NumberTheory.arithmeticEventListCharge,
        NumberTheory.ArithmeticEvent.schoolbookCharge,
        NumberTheory.ArithmeticEvent.operandWidth]
    rw [hprefix]
    change 2 + gcdTrace.schoolbookCharge +
      NumberTheory.arithmeticEventListCharge
        [ .natEq gcdTrace.value 1
        , .natLt 1 gcdTrace.value
        , .natLt gcdTrace.value modulus ] ≤ _
    have hcombined :
        2 +
          NumberTheory.arithmeticEventListCharge
            [ .natEq gcdTrace.value 1
            , .natLt 1 gcdTrace.value
            , .natLt gcdTrace.value modulus ] ≤
          16 * width ^ 3 := by
      simpa [NumberTheory.arithmeticEventListCharge,
        NumberTheory.ArithmeticEvent.schoolbookCharge,
        NumberTheory.ArithmeticEvent.operandWidth] using hcomparisonCubic
    calc
      2 + gcdTrace.schoolbookCharge +
          NumberTheory.arithmeticEventListCharge
            [ .natEq gcdTrace.value 1
            , .natLt 1 gcdTrace.value
            , .natLt gcdTrace.value modulus ] ≤
        16 * width ^ 3 + 16 * width ^ 3 := by omega
      _ = 32 * width ^ 3 := by ring
      _ ≤ 2 ^ 8 * width ^ 3 :=
        Nat.mul_le_mul_right (width ^ 3) (by decide)

/-- Complete deterministic interpretation of one packed fixed-width random
bit string. -/
def prepareResidueFromBits (modulus wordWidth wordCount : Nat)
    (bits : Fin (2 ^ (wordCount * wordWidth))) : PreparedResidue modulus :=
  prepareResidue modulus <|
    firstValidResidue <|
      classifyResidueProposals modulus <|
        decodeFixedWidthWords wordWidth wordCount bits

/-- A legal residue packed into the first word is recovered by the complete
fixed-width preparation semantics. -/
theorem prepareResidueFromBits_firstWord
    (modulus wordWidth wordCount : Nat)
    (candidate : Fin (2 ^ wordWidth))
    (heligible : ResidueEligible modulus candidate.val) :
    prepareResidueFromBits modulus wordWidth (wordCount + 1)
        (firstWordBits wordWidth wordCount candidate) =
      prepareResidue modulus (some candidate.val) := by
  unfold prepareResidueFromBits
  congr 1
  apply firstValidResidue_eq_first
  have hdecode :
      decodeFixedWidthWords wordWidth (wordCount + 1)
          (firstWordBits wordWidth wordCount candidate) 0 = candidate :=
    decodeFixedWidthWords_firstWordBits_zero wordWidth wordCount candidate
  simp only [classifyResidueProposals]
  rw [hdecode]
  simp [heligible]

@[simp] theorem prepareResidue_none_candidate (modulus : Nat) :
    (prepareResidue modulus none).candidate = 1 := rfl

@[simp] theorem prepareResidue_none_unit (modulus : Nat) :
    (prepareResidue modulus none).unit = 1 := rfl

@[simp] theorem prepareResidue_none_earlyFactor (modulus : Nat) :
    (prepareResidue modulus none).earlyFactor = none := rfl

@[simp] theorem prepareResidue_some_candidate (modulus candidate : Nat) :
    (prepareResidue modulus (some candidate)).candidate = candidate := by
  simp only [prepareResidue, prepareResidueExecution]
  split <;> rfl

theorem prepareResidue_some_unit_of_coprime
    (modulus candidate : Nat) (hcoprime : Nat.Coprime candidate modulus) :
    (prepareResidue modulus (some candidate)).unit =
      ZMod.unitOfCoprime candidate hcoprime := by
  have htrace :
      (NumberTheory.euclideanGCDTrace candidate modulus).value = 1 := by
    rw [NumberTheory.euclideanGCDTrace_value]
    exact hcoprime
  simp only [prepareResidue, prepareResidueExecution]
  rw [dif_pos htrace]

theorem prepareResidue_some_earlyFactor_of_coprime
    (modulus candidate : Nat) (hcoprime : Nat.Coprime candidate modulus) :
    (prepareResidue modulus (some candidate)).earlyFactor = none := by
  have htrace :
      (NumberTheory.euclideanGCDTrace candidate modulus).value = 1 := by
    rw [NumberTheory.euclideanGCDTrace_value]
    exact hcoprime
  simp only [prepareResidue, prepareResidueExecution]
  rw [dif_pos htrace]

/-- Every selected eligible nonunit residue immediately exposes its nontrivial
gcd factor.  Thus the sampler's `unit = 1` fallback can only represent total
proposal rejection, not a silently discarded nonunit candidate. -/
theorem prepareResidue_some_earlyFactor_of_not_coprime
    (modulus candidate : Nat)
    (hpositive : 0 < candidate) (hbelow : candidate < modulus)
    (hnotCoprime : ¬ Nat.Coprime candidate modulus) :
    (prepareResidue modulus (some candidate)).earlyFactor =
      some (Nat.gcd candidate modulus) := by
  have hgcdPos : 0 < Nat.gcd candidate modulus :=
    Nat.gcd_pos_of_pos_left modulus hpositive
  have hgcdNeOne : Nat.gcd candidate modulus ≠ 1 := by
    intro hgcd
    exact hnotCoprime hgcd
  have hgcdGtOne : 1 < Nat.gcd candidate modulus := by omega
  have hgcdLt : Nat.gcd candidate modulus < modulus :=
    (Nat.gcd_le_left modulus hpositive).trans_lt hbelow
  have htrace :
      (NumberTheory.euclideanGCDTrace candidate modulus).value ≠ 1 := by
    rw [NumberTheory.euclideanGCDTrace_value]
    exact hgcdNeOne
  simp only [prepareResidue, prepareResidueExecution]
  rw [dif_neg htrace]
  simp [NumberTheory.euclideanGCDTrace_value, hgcdGtOne, hgcdLt]

/-- Every early result emitted by the closed sampler preparation is a genuine
nontrivial divisor of the public modulus. -/
theorem prepareResidue_earlyFactor_some_sound
    (modulus factor : Nat) (selected : Option Nat)
    (hfactor : (prepareResidue modulus selected).earlyFactor = some factor) :
    factor ∣ modulus ∧ 1 < factor ∧ factor < modulus :=
  (prepareResidue modulus selected).earlyFactor_sound factor hfactor

/-- Every early result emitted from a packed fixed-width sample is a genuine
nontrivial divisor of the public modulus. -/
theorem prepareResidueFromBits_earlyFactor_some_sound
    (modulus wordWidth wordCount : Nat)
    (bits : Fin (2 ^ (wordCount * wordWidth))) (factor : Nat)
    (hfactor :
      (prepareResidueFromBits modulus wordWidth wordCount bits).earlyFactor =
        some factor) :
    factor ∣ modulus ∧ 1 < factor ∧ factor < modulus :=
  prepareResidue_earlyFactor_some_sound modulus factor _ (by
    simpa [prepareResidueFromBits] using hfactor)

end RSA
end QuantumAlg

end
