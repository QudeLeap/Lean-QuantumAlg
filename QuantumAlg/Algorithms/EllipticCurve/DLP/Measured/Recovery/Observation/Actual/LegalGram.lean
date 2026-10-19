/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.Good.Kernel
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.Selected.Effect

/-!
# Actual legal Gram entries on the original good source columns

The actual Fourier coefficients retain their complex relative phase. Each
complete legal outcome contributes its original group-equality Gram kernel,
beside every residual Reference coordinate. The selected event is still a
sum over all complete legal outcomes. Neither a frequency reindexing nor a
point-outcome normalization is assumed here.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ActualLegalGram

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg.Execution (Store)
open _root_.QuantumAlg.QuantumFourierTransform.Semiclassical (Bits)
open _root_.QuantumAlg.FiniteCyclicDLP (KnownOrderProblem orderWidth)
open Recovery.Stage.PointCoordinates (Bank ResidualReference)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity (Branch)
open GenericPointAddition.InPlace.Semantics (radixUnit)
open Recovery.Conversion.FreeSourceFamily
  (freeSourceColumns pathFourierCoefficient LegalOutcome legalColumns)
open Recovery.Conversion.CoherentBankFamily (sourceWord)
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}

/-- The two source Fourier factors multiply the full actual bank Gram without phase loss. -/
lemma freeSourceColumns_gram (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (path : Fin (2 * m) → Branch p.size m)
    (left right : Bits m × Bits m) (bankLeft bankRight : Bank p.size m Reference) :
    ((freeSourceColumns (environment := environment) E points coefficient Reference
      path).conjTranspose *
      freeSourceColumns (environment := environment) E points coefficient Reference path)
      (left, bankLeft) (right, bankRight) =
      (star (pathFourierCoefficient p.size m path left) *
        pathFourierCoefficient p.size m path right) *
      ((sourceWord (environment := environment) E points coefficient Reference path
        left).conjTranspose *
        sourceWord (environment := environment) E points coefficient Reference path right)
        bankLeft bankRight := by
  change (∑ row : Bank p.size m Reference,
    star (pathFourierCoefficient p.size m path left *
      sourceWord (environment := environment) E points coefficient Reference path left row
        bankLeft) *
      (pathFourierCoefficient p.size m path right *
        sourceWord (environment := environment) E points coefficient Reference path right row
          bankRight)) =
    (star (pathFourierCoefficient p.size m path left) *
      pathFourierCoefficient p.size m path right) *
      ∑ row : Bank p.size m Reference,
        star (sourceWord (environment := environment) E points coefficient Reference path left row
          bankLeft) *
          sourceWord (environment := environment) E points coefficient Reference path right row
            bankRight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [star_mul]
  ring

section OriginalSchedule

variable (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (addends : (fun index => (points index).toGroupPoint) =
    ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
      problem.generator problem.target)
  (fieldTail : Nat) (odd : Odd p) (Reference : Register)
  (original : Store (Recovery.Layout.terminal p.size (orderWidth problem)))
  (left right : Bits (orderWidth problem) × Bits (orderWidth problem))
  (refLeft refRight : (ResidualReference p.size (orderWidth problem) Reference).Index)
  (leftGood : ExceptionalOffsetAveraging.Admissible (2 * orderWidth problem)
    (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem))
    (fun index => (points index).toGroupPoint) seed.toGroupPoint
    (SourceControls.sourceValues (orderWidth problem) left))
  (rightGood : ExceptionalOffsetAveraging.Admissible (2 * orderWidth problem)
    (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem))
    (fun index => (points index).toGroupPoint) seed.toGroupPoint
    (SourceControls.sourceValues (orderWidth problem) right))

include addends leftGood rightGood

/-- A legal outcome keeps both Fourier phases and the unchanged full-group kernel. -/
lemma legalColumns_reset_gram
    (outcome : LegalOutcome p (orderWidth problem) original) :
    ((legalColumns (environment := environment) E points (radixUnit p fieldTail.succ odd)
        Reference original outcome).conjTranspose *
      legalColumns (environment := environment) E points (radixUnit p fieldTail.succ odd)
        Reference original outcome)
      (left, (Recovery.Initialization.resetArithmeticLabel E fieldTail seed, (0, refLeft)))
      (right, (Recovery.Initialization.resetArithmeticLabel E fieldTail seed, (0, refRight))) =
      (star (pathFourierCoefficient p.size (orderWidth problem)
          outcome.2.val left) *
        pathFourierCoefficient p.size (orderWidth problem)
          outcome.2.val right) *
      ((star ((WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) ^
          (2 * orderWidth problem)) *
          (WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) ^
            (2 * orderWidth problem)) *
        (if ECDLP.Measured.idealGroupOutput problem seed
              (SourceControls.sourceValues (orderWidth problem) left) =
            ECDLP.Measured.idealGroupOutput problem seed
              (SourceControls.sourceValues (orderWidth problem) right) ∧ refLeft = refRight
          then 1 else 0)) := by
  unfold legalColumns
  rw [freeSourceColumns_gram]
  rw [ActualGoodKernel.sourceWord_reset_gram_idealGroup E problem points seed addends
    fieldTail odd Reference outcome.2.val original outcome.1 outcome.2.property
    left right refLeft refRight leftGood rightGood]

/-- The actual Store event retains every legal summand and all off-diagonal source phases. -/
lemma eventEffect_reset_gram
    (event : Store (Recovery.Layout.terminal p.size (orderWidth problem)) → Prop) :
    (ActualSelectedEffect.eventEffect (environment := environment) E points (radixUnit p
      fieldTail.succ odd)
      Reference original event).matrix
      (left, (Recovery.Initialization.resetArithmeticLabel E fieldTail seed, (0, refLeft)))
      (right, (Recovery.Initialization.resetArithmeticLabel E fieldTail seed, (0, refRight))) =
      ∑ outcome : LegalOutcome p (orderWidth problem) original,
        if event outcome.1 then
          (star (pathFourierCoefficient p.size (orderWidth problem)
              outcome.2.val left) *
            pathFourierCoefficient p.size (orderWidth problem)
              outcome.2.val right) *
          ((star ((WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) ^
              (2 * orderWidth problem)) *
              (WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) ^
                (2 * orderWidth problem)) *
            (if ECDLP.Measured.idealGroupOutput problem seed
                  (SourceControls.sourceValues (orderWidth problem) left) =
                ECDLP.Measured.idealGroupOutput problem seed
                  (SourceControls.sourceValues (orderWidth problem) right) ∧ refLeft = refRight
              then 1 else 0))
        else 0 := by
  rw [ActualSelectedEffect.eventEffect_matrix]
  erw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases selected : event outcome.1
  · simp only [if_pos selected]
    exact legalColumns_reset_gram E problem points seed addends fieldTail odd Reference
      original left right refLeft refRight leftGood rightGood outcome
  · simp only [if_neg selected]
    rfl

end OriginalSchedule

end

end ActualLegalGram
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
