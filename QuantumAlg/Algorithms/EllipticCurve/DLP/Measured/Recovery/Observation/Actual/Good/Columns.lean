/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.SourceControls
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.RadixWords

/-!
# Actual converted arithmetic columns on the unchanged original good set

Both physical block words use the complete original outcome tuple. Their length
casts agree with the first and second halves of that tuple, and the second block
acts after the first. The resulting literal converted word therefore has the
prepared column of the original affine trajectory. Specializing the unchanged
coefficient to the original radix gives the actual reset arithmetic label.

No reference coordinate, zero outcome, or physical readout choice is discarded.
The original good predicate is used only to identify the prepared columns; the
complete legal family and its effect are defined independently of that predicate.
These identities do not assert a success bound or normalize a good component.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ActualGoodColumns

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open _root_.QuantumAlg.QuantumFourierTransform.Semiclassical.Partner (chronologicalProduct)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity.ActualFeedback
  (position position_val)

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private lemma chronologicalProduct_append {Bank : Type} [Fintype Bank]
    (first second : List (Matrix Bank Bank ℂ)) :
    chronologicalProduct (first ++ second) =
      chronologicalProduct second * chronologicalProduct first := by
  induction first with
  | nil => simp only [List.nil_append, chronologicalProduct, Matrix.mul_one]
  | cons head tail ih =>
      simp only [List.cons_append, chronologicalProduct, ih, Matrix.mul_assoc]

private lemma chronologicalProduct_ofFn_blocks {Bank : Type} [Fintype Bank]
    [DecidableEq Bank]
    (m : Nat) (entry : Fin (2 * m) → Matrix Bank Bank ℂ)
    (first second : Matrix Bank Bank ℂ)
    (firstLaw : chronologicalProduct
      (List.ofFn (fun current : Fin m => entry (position false current))) = first)
    (secondLaw : chronologicalProduct
      (List.ofFn (fun current : Fin m => entry (position true current))) = second) :
    chronologicalProduct (List.ofFn entry) = second * first := by
  have appendLaw (left right : List (Matrix Bank Bank ℂ)) :
      chronologicalProduct (left ++ right) =
        chronologicalProduct right * chronologicalProduct left := by
    induction left with
    | nil => simp only [List.nil_append, chronologicalProduct, Matrix.mul_one]
    | cons head tail ih =>
        simp only [List.cons_append, chronologicalProduct, ih, Matrix.mul_assoc]
  exact (congrArg chronologicalProduct
    (SourceControls.ofFn_split_positions m entry)).trans
    ((appendLaw _ _).trans
      (congrArg₂ (fun second first : Matrix Bank Bank ℂ => second * first)
        secondLaw firstLaw))

/-- The complete outcome tuple splits into exactly its two chronological block paths. -/
lemma pointOutcomes_append {m : Nat} {Outcome : Type}
    (outcomes : Fin (2 * m) → Outcome) :
    Fin.append (fun current : Fin m => outcomes (position false current))
        (fun current : Fin m => outcomes (position true current)) =
      fun index : Fin (m + m) => outcomes (Fin.cast (Nat.two_mul m).symm index) := by
  calc
    _ = Fin.append
        (fun current : Fin m => outcomes
          (Fin.cast (Nat.two_mul m).symm (Fin.castAdd m current)))
        (fun current : Fin m => outcomes
          (Fin.cast (Nat.two_mul m).symm (Fin.natAdd m current))) := by
      congr 1
      · funext current
        apply congrArg outcomes
        apply Fin.ext
        simpa only [Bool.false_eq_true, ↓reduceIte, Fin.val_cast, Fin.val_castAdd]
          using position_val false current
      · funext current
        apply congrArg outcomes
        apply Fin.ext
        simpa only [↓reduceIte, Fin.val_cast, Fin.val_natAdd] using position_val true current
    _ = _ := Fin.append_castAdd_natAdd (m := m) (n := m)
      (f := fun index : Fin (m + m) => outcomes (Fin.cast (Nat.two_mul m).symm index))

open QuantumAlg QuantumAlg.Execution
open _root_.QuantumAlg.QuantumFourierTransform.Semiclassical (Bits)
open GenericPointAddition.InPlace.Semantics (radixUnit)
open Recovery.Stage.PointCoordinates (Bank ResidualReference)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity (Branch traceValid)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}

omit [Fact p.Prime] in
/-- The full prescribed stage list has one stage for every original position. -/
lemma affineStages_length (points : Fin (2 * m) → AffinePoint E) :
    (PointBankAffineTrajectory.affineStages E points (SourceControls.controls m)
      (List.finRange (2 * m))).length = 2 * m := by
  simp only [PointBankAffineTrajectory.affineStages, List.length_map, List.length_finRange]

omit [Fact p.Prime] in
/-- Reindex the same complete outcome tuple by the length of the original affine list. -/
def affineOutcomePath (points : Fin (2 * m) → AffinePoint E)
    (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size) :
    Fin (PointBankAffineTrajectory.affineStages E points (SourceControls.controls m)
      (List.finRange (2 * m))).length → ControlledPointWords.Outcome p.size :=
  fun index => outcomes (Fin.cast (affineStages_length E points) index)

private lemma bankWord_ofFn_cast {Source : Type} {count : Nat}
    (Reference : Register) (stages : List (ControlledPointWords.Stage E Source))
    (entries : Fin count → ControlledPointWords.Stage E Source)
    (same : stages = List.ofFn entries) (length : stages.length = count)
    (outcomes : Fin count → ControlledPointWords.Outcome p.size) (source : Source) :
    ControlledPointWords.bankWord (environment := environment) E Reference stages
        (fun index => outcomes (Fin.cast length index)) source =
      chronologicalProduct (List.ofFn (fun index : Fin count =>
        Recovery.Point.Instrument.pointBankBlock (environment := environment) E (entries index).1
          Reference
          (outcomes index).2 (outcomes index).1 ((entries index).2 source))) := by
  subst stages
  rw [ControlledPointWords.bankWord_chronologicalProduct]
  apply congrArg chronologicalProduct
  exact ActualPointWords.ofFn_get_cast entries outcomes
    (fun stage outcome => Recovery.Point.Instrument.pointBankBlock (environment := environment) E
      stage.1 Reference
      outcome.2 outcome.1 (stage.2 source))

/-- All original point outcomes enter the same complete affine word, with no extra labels. -/
lemma affineWord_chronologicalProduct (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
    (source : Bits m × Bits m) :
    ControlledPointWords.bankWord (environment := environment) E (ResidualReference p.size m
      Reference)
        (PointBankAffineTrajectory.affineStages E points (SourceControls.controls m)
          (List.finRange (2 * m))) (affineOutcomePath E points outcomes) source =
      chronologicalProduct (List.ofFn (fun index : Fin (2 * m) =>
        Recovery.Point.Instrument.pointBankBlock (environment := environment) E (points index)
          (ResidualReference p.size m
          Reference)
          (outcomes index).2 (outcomes index).1
          (BinaryLabelEncoding.bool.encode (SourceControls.controls m source index)))) := by
  unfold affineOutcomePath
  exact bankWord_ofFn_cast E (ResidualReference p.size m Reference)
    (PointBankAffineTrajectory.affineStages E points (SourceControls.controls m)
      (List.finRange (2 * m)))
    (fun index => (points index, fun input =>
      BinaryLabelEncoding.bool.encode (SourceControls.controls m input index)))
    (by
      unfold PointBankAffineTrajectory.affineStages
      exact List.ofFn_eq_map.symm)
    (affineStages_length E points) outcomes source

/-- A literal two-level control for each complete actual point outcome. -/
private def pointEntry (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
    (source : Bits m × Bits m) (index : Fin (2 * m)) :
    Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
  Recovery.Point.Instrument.pointBankBlock (environment := environment) E (points index)
    (ResidualReference p.size m Reference)
    (outcomes index).2 (outcomes index).1
    (finTwoEquiv.symm (SourceControls.controls m source index))

/-- The original affine word has these literal control entries, in its original order. -/
private lemma affineWord_pointEntries (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
    (source : Bits m × Bits m) :
    ControlledPointWords.bankWord (environment := environment) E (ResidualReference p.size m
      Reference)
        (PointBankAffineTrajectory.affineStages E points (SourceControls.controls m)
          (List.finRange (2 * m))) (affineOutcomePath E points outcomes) source =
      chronologicalProduct (List.ofFn (pointEntry (environment := environment) E points Reference
        outcomes source)) := by
  refine (affineWord_chronologicalProduct E points Reference outcomes source).trans ?_
  exact congrArg chronologicalProduct
    (congrArg List.ofFn (funext fun index : Fin (2 * m) =>
      congrArg (fun bit : Fin 2 => Recovery.Point.Instrument.pointBankBlock (environment :=
        environment) E (points index)
        (ResidualReference p.size m Reference) (outcomes index).2 (outcomes index).1 bit)
        (SourceControls.bool_encode_finTwo (SourceControls.controls m source index))))

/-- Each actual block uses the same entries at its prescribed positions. -/
private lemma blockWord_pointEntries (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
    (source : Bits m × Bits m) (second : Bool) :
    chronologicalProduct (List.ofFn (fun current : Fin m =>
        pointEntry (environment := environment) E points Reference outcomes source (position
          second current))) =
      ActualPointWords.blockWord (environment := environment) E points Reference outcomes second
        (SourceControls.blockSource second source) := by
  symm
  refine (ActualPointWords.blockWord_chronologicalProduct E points Reference outcomes
    second (SourceControls.blockSource second source)).trans ?_
  exact congrArg chronologicalProduct
    (congrArg List.ofFn (funext fun current : Fin m =>
      congrArg (fun bit : Fin 2 =>
        Recovery.Point.Instrument.pointBankBlock (environment := environment) E (points (position
          second current))
          (ResidualReference p.size m Reference)
          (outcomes (position second current)).2 (outcomes (position second current)).1 bit)
        ((SourceControls.controls_position m source second current).symm.trans
          (SourceControls.bool_encode_finTwo
            (SourceControls.controls m source (position second current))))))

/-- The two actual words are the single original affine word, in second-times-first order. -/
lemma pointPairWord_affineWord (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
    (source : Bits m × Bits m) :
    ActualPointWords.pointPairWord (environment := environment) E points Reference outcomes source =
      ControlledPointWords.bankWord (environment := environment) E (ResidualReference p.size m
        Reference)
        (PointBankAffineTrajectory.affineStages E points (SourceControls.controls m)
          (List.finRange (2 * m))) (affineOutcomePath E points outcomes) source := by
  exact ((affineWord_pointEntries E points Reference outcomes source).trans
    (chronologicalProduct_ofFn_blocks (Bank := Bank p.size m Reference) m
      (pointEntry (environment := environment) E points Reference outcomes source)
      (ActualPointWords.blockWord (environment := environment) E points Reference outcomes false
        source.1)
      (ActualPointWords.blockWord (environment := environment) E points Reference outcomes true
        source.2)
      (blockWord_pointEntries E points Reference outcomes source false)
      (blockWord_pointEntries E points Reference outcomes source true))).symm

/-- The unchanged original good set identifies every actual converted prepared column. -/
lemma convertedPointWord_prepared_column (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
    (source : Bits m × Bits m) (seed : AffinePoint E)
    (reference : (ResidualReference p.size m Reference).Index)
    (good : ExceptionalOffsetAveraging.Admissible (2 * m)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected m)
      (fun index => (points index).toGroupPoint) seed.toGroupPoint
      (SourceControls.sourceValues m source))
    (row : Bank p.size m Reference) :
    ActualPointWords.convertedPointWord (environment := environment) E points coefficient
      Reference outcomes source row
        (PointBankGoodColumns.preparedBank p (ResidualReference p.size m Reference)
          (ConvertedBankGoodColumns.encodedWords coefficient seed.x seed.y) reference) =
      (WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) ^ (2 * m) *
        (if row = PointBankGoodColumns.preparedBank p (ResidualReference p.size m Reference)
          (ConvertedBankGoodColumns.encodedWords coefficient
            (ScalarMultiplication.AffineTrajectory.path E points
              (SourceControls.controls m source)
              (List.finRange (2 * m)) seed).x
            (ScalarMultiplication.AffineTrajectory.path E points
              (SourceControls.controls m source)
              (List.finRange (2 * m)) seed).y) reference then 1 else 0) := by
  unfold ActualPointWords.convertedPointWord
  rw [pointPairWord_affineWord]
  simpa only [affineStages_length] using
    ConvertedBankGoodColumns.convertedAffineWord_prepared_column E points
      (SourceControls.controls m) source seed coefficient
      (ResidualReference p.size m Reference) (affineOutcomePath E points outcomes)
      reference good row

/-- The same column starts at the actual reset arithmetic label for the original radix. -/
lemma convertedPointWord_reset_column (points : Fin (2 * m) → AffinePoint E)
    (fieldTail : Nat) (odd : Odd p) (Reference : Register)
    (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
    (source : Bits m × Bits m) (seed : AffinePoint E)
    (reference : (ResidualReference p.size m Reference).Index)
    (good : ExceptionalOffsetAveraging.Admissible (2 * m)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected m)
      (fun index => (points index).toGroupPoint) seed.toGroupPoint
      (SourceControls.sourceValues m source))
    (row : Bank p.size m Reference) :
    ActualPointWords.convertedPointWord (environment := environment) E points (radixUnit p
      fieldTail.succ odd)
        Reference outcomes source row
        (Recovery.Initialization.resetArithmeticLabel E fieldTail seed, (0, reference)) =
      (WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) ^ (2 * m) *
        (if row = PointBankGoodColumns.preparedBank p (ResidualReference p.size m Reference)
          (ConvertedBankGoodColumns.encodedWords (radixUnit p fieldTail.succ odd)
            (ScalarMultiplication.AffineTrajectory.path E points
              (SourceControls.controls m source)
              (List.finRange (2 * m)) seed).x
            (ScalarMultiplication.AffineTrajectory.path E points
              (SourceControls.controls m source)
              (List.finRange (2 * m)) seed).y) reference then 1 else 0) := by
  rw [ActualRadixWords.resetArithmeticLabel_prepared E fieldTail odd seed]
  exact convertedPointWord_prepared_column E points
    (radixUnit p fieldTail.succ odd) Reference outcomes source seed reference good row

/-- Every actual legal path has this same reset column beside its arbitrary complete Store. -/
lemma sourceWord_reset_column (points : Fin (2 * m) → AffinePoint E)
    (fieldTail : Nat) (odd : Odd p) (Reference : Register)
    (path : Fin (2 * m) → Branch p.size m)
    (original final : Store (Recovery.Layout.terminal p.size m))
    (valid : traceValid p.size m (2 * m) id path original final)
    (source : Bits m × Bits m) (seed : AffinePoint E)
    (reference : (ResidualReference p.size m Reference).Index)
    (good : ExceptionalOffsetAveraging.Admissible (2 * m)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected m)
      (fun index => (points index).toGroupPoint) seed.toGroupPoint
      (SourceControls.sourceValues m source))
    (row : Bank p.size m Reference) :
    Recovery.Conversion.CoherentBankFamily.sourceWord (environment := environment) E points
        (radixUnit p fieldTail.succ odd) Reference path source row
        (Recovery.Initialization.resetArithmeticLabel E fieldTail seed, (0, reference)) =
      (WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) ^ (2 * m) *
        (if row = PointBankGoodColumns.preparedBank p (ResidualReference p.size m Reference)
          (ConvertedBankGoodColumns.encodedWords (radixUnit p fieldTail.succ odd)
            (ScalarMultiplication.AffineTrajectory.path E points
              (SourceControls.controls m source)
              (List.finRange (2 * m)) seed).x
            (ScalarMultiplication.AffineTrajectory.path E points
              (SourceControls.controls m source)
              (List.finRange (2 * m)) seed).y) reference then 1 else 0) := by
  rw [ActualPointWords.sourceWord_legalRun E points
    (radixUnit p fieldTail.succ odd) Reference path original final valid source]
  exact convertedPointWord_reset_column E points fieldTail odd Reference
    (fun current => (ActualOutcomeLabels.branchOutcome p.size m (path current)).1)
    source seed reference good row

end

end ActualGoodColumns
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
