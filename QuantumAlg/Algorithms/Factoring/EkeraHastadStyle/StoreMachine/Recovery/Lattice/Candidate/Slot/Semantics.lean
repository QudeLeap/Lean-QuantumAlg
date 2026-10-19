/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Semantics.Prefix
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Setup.Layout

/-!
# Original short-log candidate correctness from the actual five-stage execution
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotSemantics

open Execution
open ClassicalRoutines
open ClassicalRoutines.NumberTheory.SignedWord hiding writeInput
open LatticeCandidateSlotFrames
open LatticeCandidateSlotMachine (writeInput)
open LatticeCandidateSlotOutcome (initialConditions_transport)

noncomputable section

private lemma natAbs_lt_wordModulus_of_signedRepresentable {width : Nat} {value : Int}
    (widthPositive : 0 < width)
    (fits : ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width value) :
    value.natAbs < CShape.wordModulus width := by
  unfold ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable at fits
  change value.natAbs < 2 ^ width
  have halfBelowFull : 2 ^ (width - 1) < 2 ^ width := by
    apply Nat.pow_lt_pow_right (by norm_num)
    omega
  have capacityCast :
      ((2 ^ (width - 1) : Nat) : Int) = (2 ^ (width - 1) : Int) := by
    norm_num
  rw [← capacityCast] at fits
  by_cases nonnegative : 0 ≤ value
  · have magnitudeAtMostHalf : (value.natAbs : Int) <
        ((2 ^ (width - 1) : Nat) : Int) := by
      rw [Int.natAbs_of_nonneg nonnegative]
      exact fits.2
    have magnitudeBelowHalf : value.natAbs < 2 ^ (width - 1) :=
      Int.ofNat_lt.mp magnitudeAtMostHalf
    exact magnitudeBelowHalf.trans halfBelowFull
  · have nonpositive : value ≤ 0 := Int.le_of_not_le nonnegative
    have magnitudeAtMostHalf : (value.natAbs : Int) ≤
        ((2 ^ (width - 1) : Nat) : Int) := by
      rw [Int.ofNat_natAbs_of_nonpos nonpositive]
      omega
    have magnitudeAtMostHalfNat : value.natAbs ≤ 2 ^ (width - 1) := by
      exact_mod_cast magnitudeAtMostHalf
    exact magnitudeAtMostHalfNat.trans_lt halfBelowFull

private lemma word_eq_of_toNat_eq {width : Nat} (left right : CShape.Word width)
    (equal : left.toNat = right.toNat) : left = right := by
  cases left with
  | unsignedWord left =>
      cases right with
      | unsignedWord right =>
          congr
          exact Fin.ext equal

/-- Every actual slot execution preserves its original entry data and retains exactly the first
source-accepted candidate, with the complete actual caller frame. -/
lemma candidateSlotInto_correct {N m ell : Nat} {model : ExecutionModel}
    [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
    (input : Input N) (generator : (ZMod N)ˣ)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (offset : NumberTheory.IntegerPoint3)
    (hoffset : offset ∈ NumberTheory.coefficientOffsetList3
      NumberTheory.nearestPlaneCoefficientBounds3)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (separation : LatticeCandidateSlotMachine.Separation refs)
    (frameSeparation : FrameSeparation refs) (store : Store ctx)
    (initial : LatticeCandidateSlotOutcome.InitialConditions input generator samples refs store) :
    LatticeCandidateSlotOutcome.Outcome input generator samples offset refs store
      (LatticeCandidateSlotMachine.candidateSlotStep (model := model)
        (LatticeCandidateModularSetup.modulusSpec input) offset refs store).1 := by
  let _ : NeZero N := input.neZero
  let spec := LatticeCandidateModularSetup.modulusSpec input
  let point := RSA.shortLogPointAtOffset m ell samples offset
  let afterScale := distanceScaleStore (model := model) offset refs store
  let afterExponent :=
    (LatticeCandidateExponent.exponentStep (model := model) refs.exponent afterScale).1
  let afterPower :=
    (LatticeCandidatePowerMachine.candidateStep (model := model)
      spec refs.power afterExponent).1
  let finalStore :=
    (LatticeCandidateSlotMachine.candidateSlotStep (model := model)
      spec offset refs store).1
  have prefixFacts := distanceScaleStore_correct (model := model)
    input generator samples offset hoffset refs
    separation frameSeparation store initial
  have exponentFacts := LatticeCandidateExponent.candidateExponentInto_correct refs.exponent
    separation.exponent afterScale m point.2.2 prefixFacts.exponentInitial
  have exponentFrame {shape : CShape} (other : CInputRef ctx shape)
      (avoids : AvoidsStageWrites refs other .exponent) :
      afterExponent.read other = afterScale.read other :=
    candidateExponentInto_callerFrame refs afterScale other avoids
  have powerFrame {shape : CShape} (other : CInputRef ctx shape)
      (avoids : AvoidsStageWrites refs other .power) :
      afterPower.read other = afterExponent.read other :=
    candidatePowerInto_callerFrame spec refs afterExponent other avoids
  have initialAtExponent :
      LatticeCandidateSlotOutcome.InitialConditions input generator samples refs afterExponent :=
    initialConditions_transport input generator samples refs afterScale afterExponent
      prefixFacts.initial fun source => exponentFrame (externalSourceInput refs source)
        (frameSeparation.externalAvoidsStage source .exponent)
  have exponentMagnitudeFits :
      point.2.2.natAbs < CShape.wordModulus (RSA.ShortLogWidths.coordinateWidth N m ell) :=
    natAbs_lt_wordModulus_of_signedRepresentable prefixFacts.exponentInitial.widthPositive
      prefixFacts.exponentInitial.candidateSignedFits
  have exponentValue :
      (afterExponent.read (writeInput refs.exponent.exponent)).toNat = point.2.2.natAbs :=
    rawSignedRepresents_toNat_eq_of_lt _ exponentFacts.exponent exponentMagnitudeFits
  let powerInput : ClassicalAlgorithms.Modular.Pow.Input spec
      (RSA.ShortLogWidths.coordinateWidth N m ell) :=
    { base := ⟨(generator : ZMod N).val, by exact ZMod.val_lt _⟩
      exponent := ⟨point.2.2.natAbs, exponentMagnitudeFits⟩ }
  let targetResidue : ClassicalAlgorithms.Modular.Residue spec :=
    ⟨(RSA.targetUnit generator : ZMod N).val, by exact ZMod.val_lt _⟩
  have powerInitial : LatticeCandidatePowerMachine.InitialConditions spec afterExponent refs.power
      powerInput targetResidue := by
    refine ⟨initialAtExponent.powerModulus, initialAtExponent.powerGenerator, ?_,
      initialAtExponent.powerTarget⟩
    rw [refs.powerExponent]
    apply word_eq_of_toNat_eq
    exact exponentValue
  have powerFacts := LatticeCandidatePowerMachine.candidatePowerInto_correct spec refs.power
    separation.power afterExponent powerInput targetResidue powerInitial
  have nearTargetAtPower : (afterPower.read refs.selector.nearTarget).toBool =
      decide (RSA.ShortLogNearTarget m ell samples point) := by
    rw [refs.selectorNearTarget]
    change (afterPower.read (writeInput refs.nearTarget.accepted)).toBool = _
    rw [powerFrame _ (mutableWrite_avoids_stage refs frameSeparation refs.nearTarget.accepted
      (.nearTarget .accepted) .power rfl (by intro impossible; exact impossible))]
    rw [exponentFrame _ (mutableWrite_avoids_stage refs frameSeparation refs.nearTarget.accepted
      (.nearTarget .accepted) .exponent rfl (by intro impossible; exact impossible))]
    exact prefixFacts.nearTarget
  have exponentAtPower : (afterPower.read refs.selector.exponentInRange).toBool =
      decide (LatticeCandidateExponent.ExponentInRange m point.2.2) := by
    rw [refs.selectorExponentInRange]
    change (afterPower.read (writeInput refs.exponent.accepted)).toBool = _
    rw [powerFrame _ (mutableWrite_avoids_stage refs frameSeparation refs.exponent.accepted
      (.exponent .accepted) .power rfl (by intro impossible; exact impossible))]
    exact exponentFacts.accepted
  have candidateAtPower : (afterPower.read refs.selector.candidate).toNat = point.2.2.natAbs := by
    rw [refs.selectorCandidate]
    rw [powerFrame _ (mutableWrite_avoids_stage refs frameSeparation refs.exponent.exponent
      (.exponent .exponent) .power rfl (by intro impossible; exact impossible))]
    exact exponentValue
  have powerMatchesAtPower : (afterPower.read refs.selector.powerMatches).toBool =
      decide (generator ^ point.2.2.natAbs = RSA.targetUnit generator) := by
    rw [refs.selectorPowerMatches]
    refine powerFacts.accepted.trans ?_
    change decide ((generator : ZMod N).val ^ point.2.2.natAbs % N =
      (RSA.targetUnit generator : ZMod N).val) = _
    simp only [LatticeCandidatePowerBridge.candidatePowerMatches_targetUnit_iff
      input generator point.2.2.natAbs]
  have acceptedFrame : afterPower.read (writeInput refs.selector.selection.accepted) =
      afterScale.read (writeInput refs.selector.selection.accepted) :=
    (powerFrame _ (mutableWrite_avoids_stage refs frameSeparation refs.selector.selection.accepted
      (.selection .accepted) .power rfl (by intro impossible; exact impossible))).trans
      (exponentFrame _
        (mutableWrite_avoids_stage refs frameSeparation refs.selector.selection.accepted
          (.selection .accepted) .exponent rfl (by intro impossible; exact impossible)))
  have selectedFrame : afterPower.read (writeInput refs.selector.selection.selected) =
      afterScale.read (writeInput refs.selector.selection.selected) :=
    (powerFrame _ (mutableWrite_avoids_stage refs frameSeparation refs.selector.selection.selected
      (.selection .selected) .power rfl (by intro impossible; exact impossible))).trans
      (exponentFrame _
        (mutableWrite_avoids_stage refs frameSeparation refs.selector.selection.selected
          (.selection .selected) .exponent rfl (by intro impossible; exact impossible)))
  have selectedAtPower : LatticeCandidateSlotMachine.selectedOption refs.selector.selection
      afterPower = LatticeCandidateSlotMachine.selectedOption refs.selector.selection store := by
    refine Eq.trans ?_ prefixFacts.selectedFrame
    unfold LatticeCandidateSlotMachine.selectedOption
    rw [acceptedFrame, selectedFrame]
  have slotCheckedAtPower : LatticeCandidateSlotMachine.slotCheckedOption refs.selector afterPower =
      RSA.shortLogCandidateAtOffset m ell generator samples offset :=
    LatticeCandidateSlotMachine.slotCheckedOption_eq_shortLogCandidateAtOffset_of_natAbsPower
      m ell generator samples offset refs.selector afterPower nearTargetAtPower exponentAtPower
      powerMatchesAtPower candidateAtPower
  refine ⟨?_, ?_, candidateSlotInto_callerFrame spec offset refs store⟩
  · exact initialConditions_transport input generator samples refs store finalStore initial
      (candidateSlotInto_external_frame spec offset refs frameSeparation store)
  · change LatticeCandidateSlotMachine.selectedOption refs.selector.selection
      (LatticeCandidateSelector.selectorStep refs.selector afterPower).1 = _
    rw [LatticeCandidateSlotMachine.candidateSelectorInto_selectedOption refs.selector
      separation.selector afterPower, selectedAtPower, slotCheckedAtPower]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotSemantics
