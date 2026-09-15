/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Candidate.Power.Source

/-!
# Original source candidate options decoded from actual execution stores
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

/-- Decode the original persistent first-success latches from the actual store. -/
def selectedOption {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : ClassicalRoutines.FirstAccepted.Direct.Refs ctx width)
    (store : Store ctx) : Option Nat :=
  if (store.read (writeInput refs.accepted)).toBool then
    some (store.read (writeInput refs.selected)).toNat else none

/-- Decode the current actual eligibility bit and candidate word. -/
def checkedOption {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (eligible : CInputRef ctx .bit) (candidate : CInputRef ctx (.unsignedWord width))
    (store : Store ctx) : Option Nat :=
  if (store.read eligible).toBool then some (store.read candidate).toNat else none

/-- The three original caller-visible checks decoded as the current slot result. -/
def slotCheckedOption {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeCandidateSelector.Refs ctx width) (store : Store ctx) : Option Nat :=
  if ((store.read refs.nearTarget).toBool && (store.read refs.exponentInRange).toBool) &&
      (store.read refs.powerMatches).toBool then some (store.read refs.candidate).toNat else none

/-- An actual first-success outcome is exactly the original pure retain-first update. -/
theorem selectedOption_of_outcome {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (eligible : CInputRef ctx .bit) (candidate : CInputRef ctx (.unsignedWord width))
    (refs : ClassicalRoutines.FirstAccepted.Direct.Refs ctx width) (before after : Store ctx)
    (holds : ClassicalRoutines.FirstAccepted.Direct.Outcome eligible candidate refs before after) :
    selectedOption refs after = RSA.retainFirstShortLogCandidate (selectedOption refs before)
      (checkedOption eligible candidate before) := by
  unfold selectedOption checkedOption
  rw [holds.accepted, holds.selected]
  cases (before.read (writeInput refs.accepted)).toBool <;>
    cases (before.read eligible).toBool <;>
      simp [RSA.retainFirstShortLogCandidate]

/-- An actual conjunction-selector outcome feeds the original three-check candidate option. -/
theorem candidateSelectorOutcome_selectedOption {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (refs : LatticeCandidateSelector.Refs ctx width)
    (before after : Store ctx) (holds : LatticeCandidateSelector.Outcome refs before after) :
    selectedOption refs.selection after =
      RSA.retainFirstShortLogCandidate (selectedOption refs.selection before)
        (slotCheckedOption refs before) := by
  unfold selectedOption slotCheckedOption
  rw [holds.accepted, holds.selected]
  change (if ((before.read (writeInput refs.selection.accepted)).toBool ||
      LatticeCandidateSelector.eligibility refs before) then _ else none) = _
  change (if _ then _ else none) = RSA.retainFirstShortLogCandidate
    (if (before.read (writeInput refs.selection.accepted)).toBool then _ else none)
    (if LatticeCandidateSelector.eligibility refs before then _ else none)
  cases (before.read (writeInput refs.selection.accepted)).toBool <;>
    cases LatticeCandidateSelector.eligibility refs before <;>
      simp [RSA.retainFirstShortLogCandidate]

/-- The actual executed selector retains exactly the first source-checked candidate. -/
theorem candidateSelectorInto_selectedOption {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (refs : LatticeCandidateSelector.Refs ctx width)
    (separation : LatticeCandidateSelector.Separation refs) (store : Store ctx) :
    selectedOption refs.selection (LatticeCandidateSelector.selectorStep refs store).1 =
      RSA.retainFirstShortLogCandidate (selectedOption refs.selection store)
        (slotCheckedOption refs store) :=
  candidateSelectorOutcome_selectedOption refs store _
    (LatticeCandidateSelector.candidateSelectorInto_correct refs separation store)

/-- Three exact machine checks decode to the source candidate option. -/
theorem slotCheckedOption_eq_shortLogCandidateAtOffset {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (offset : NumberTheory.IntegerPoint3) {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeCandidateSelector.Refs ctx width)
    (store : Store ctx)
    (nearTargetEq : (store.read refs.nearTarget).toBool =
      decide (RSA.ShortLogNearTarget m ell samples
        (RSA.shortLogPointAtOffset m ell samples offset)))
    (exponentInRangeEq : (store.read refs.exponentInRange).toBool =
      decide (LatticeCandidateExponent.ExponentInRange m
        (RSA.shortLogPointAtOffset m ell samples offset).2.2))
    (powerMatchesEq : (store.read refs.powerMatches).toBool =
      decide (generator ^
        (RSA.shortLogPointAtOffset m ell samples offset).2.2.toNat =
          RSA.targetUnit generator))
    (candidateEq : LatticeCandidateExponent.ExponentInRange m
      (RSA.shortLogPointAtOffset m ell samples offset).2.2 →
        (store.read refs.candidate).toNat =
          (RSA.shortLogPointAtOffset m ell samples offset).2.2.toNat) :
    slotCheckedOption refs store =
      RSA.shortLogCandidateAtOffset m ell generator samples offset := by
  rw [RSA.shortLogCandidateAtOffset_eq]
  unfold LatticeCandidateExponent.ExponentInRange at exponentInRangeEq candidateEq
  by_cases nearTarget : RSA.ShortLogNearTarget m ell samples
      (RSA.shortLogPointAtOffset m ell samples offset) <;>
    by_cases positive : 0 < (RSA.shortLogPointAtOffset m ell samples offset).2.2 <;>
      by_cases below :
          (RSA.shortLogPointAtOffset m ell samples offset).2.2 < (2 ^ m : Nat) <;>
        by_cases powerMatches : generator ^
            (RSA.shortLogPointAtOffset m ell samples offset).2.2.toNat =
              RSA.targetUnit generator <;>
          simp_all [slotCheckedOption]

/-- A range-accepted actual exponent outcome exposes the source integer's natural value. -/
theorem candidateExponentOutcome_toNat_of_inRange {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeCandidateExponent.Refs ctx width) (exponentBits : Nat)
    (before after : Store ctx)
    (candidate : Int)
    (initial : LatticeCandidateExponent.InitialConditions before refs exponentBits candidate)
    (holds : LatticeCandidateExponent.Outcome refs exponentBits candidate before after)
    (inRange : LatticeCandidateExponent.ExponentInRange exponentBits candidate) :
    (after.read (writeInput refs.exponent)).toNat = candidate.toNat := by
  have outputRepresents := holds.exponent
  have nonnegative : 0 ≤ candidate := inRange.1.le
  have magnitudeCast : (candidate.natAbs : Int) = candidate :=
    Int.natAbs_of_nonneg nonnegative
  have magnitudeBelow : candidate.natAbs < 2 ^ exponentBits := by
    have bound : (candidate.natAbs : Int) < ((2 ^ exponentBits : Nat) : Int) := by
      rw [magnitudeCast]
      exact inRange.2
    exact_mod_cast bound
  have outputValue := rawSignedRepresents_toNat_eq_of_lt _ outputRepresents
    (magnitudeBelow.trans initial.upperBoundFits)
  have magnitudeEq : candidate.natAbs = candidate.toNat := by
    exact Int.ofNat_inj.mp (magnitudeCast.trans (Int.toNat_of_nonneg nonnegative).symm)
  exact outputValue.trans magnitudeEq

/-- Three exact machine checks decode to the source candidate option when the
power machine receives the exponent classifier's natural magnitude.  Outside
the strict exponent interval the selector rejects before that distinction can
matter. -/
theorem slotCheckedOption_eq_shortLogCandidateAtOffset_of_natAbsPower
    {N : Nat} (m ell : Nat) (generator : (ZMod N)ˣ)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (offset : NumberTheory.IntegerPoint3) {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeCandidateSelector.Refs ctx width)
    (store : Store ctx)
    (nearTargetEq : (store.read refs.nearTarget).toBool =
      decide (RSA.ShortLogNearTarget m ell samples
        (RSA.shortLogPointAtOffset m ell samples offset)))
    (exponentInRangeEq : (store.read refs.exponentInRange).toBool =
      decide (LatticeCandidateExponent.ExponentInRange m
        (RSA.shortLogPointAtOffset m ell samples offset).2.2))
    (powerMatchesEq : (store.read refs.powerMatches).toBool =
      decide (generator ^
        (RSA.shortLogPointAtOffset m ell samples offset).2.2.natAbs =
          RSA.targetUnit generator))
    (candidateEq : (store.read refs.candidate).toNat =
      (RSA.shortLogPointAtOffset m ell samples offset).2.2.natAbs) :
    slotCheckedOption refs store =
      RSA.shortLogCandidateAtOffset m ell generator samples offset := by
  rw [RSA.shortLogCandidateAtOffset_eq]
  by_cases inRange : LatticeCandidateExponent.ExponentInRange m
      (RSA.shortLogPointAtOffset m ell samples offset).2.2
  · have exponentInRangeTrue : (store.read refs.exponentInRange).toBool = true := by
      rw [exponentInRangeEq]
      simp [inRange]
    rcases inRange with ⟨positive, below⟩
    have nonnegative : 0 ≤ (RSA.shortLogPointAtOffset m ell samples offset).2.2 :=
      le_of_lt positive
    have magnitudeCast :
        ((RSA.shortLogPointAtOffset m ell samples offset).2.2.natAbs : Int) =
          (RSA.shortLogPointAtOffset m ell samples offset).2.2 :=
      Int.natAbs_of_nonneg nonnegative
    have natAbs_eq_toNat :
        (RSA.shortLogPointAtOffset m ell samples offset).2.2.natAbs =
          (RSA.shortLogPointAtOffset m ell samples offset).2.2.toNat := by
      exact Int.ofNat_inj.mp
        (magnitudeCast.trans (Int.toNat_of_nonneg nonnegative).symm)
    have powerMatchesEq' : (store.read refs.powerMatches).toBool =
        decide (generator ^
          (RSA.shortLogPointAtOffset m ell samples offset).2.2.toNat =
            RSA.targetUnit generator) := by
      simpa only [natAbs_eq_toNat] using powerMatchesEq
    have candidateEq' : (store.read refs.candidate).toNat =
        (RSA.shortLogPointAtOffset m ell samples offset).2.2.toNat := by
      simpa only [natAbs_eq_toNat] using candidateEq
    by_cases nearTarget : RSA.ShortLogNearTarget m ell samples
        (RSA.shortLogPointAtOffset m ell samples offset) <;>
      by_cases powerMatches : generator ^
          (RSA.shortLogPointAtOffset m ell samples offset).2.2.toNat =
            RSA.targetUnit generator <;>
        simp_all [slotCheckedOption]
  · have exponentInRangeFalse : (store.read refs.exponentInRange).toBool = false := by
      rw [exponentInRangeEq]
      simp [inRange]
    by_cases nearTarget : RSA.ShortLogNearTarget m ell samples
        (RSA.shortLogPointAtOffset m ell samples offset) <;>
      by_cases positive : 0 <
          (RSA.shortLogPointAtOffset m ell samples offset).2.2 <;>
        by_cases below :
            (RSA.shortLogPointAtOffset m ell samples offset).2.2 < (2 ^ m : Nat) <;>
          by_cases powerMatches : generator ^
              (RSA.shortLogPointAtOffset m ell samples offset).2.2.toNat =
                RSA.targetUnit generator <;>
            simp_all [slotCheckedOption, LatticeCandidateExponent.ExponentInRange];
              omega

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotMachine
