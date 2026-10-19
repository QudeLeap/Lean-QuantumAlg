/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.OutcomeLabels
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.ControlledPointWords
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.FreeSourceFamily

/-!
# The actual legal arithmetic word at each coherent source

Reconstruction retains the complete original interface Store, both real point
Stores at every stage, and every physical readout bit. The arithmetic factor
depends only on the real point outcomes and the chosen coherent source.
Physical readout bits remain in the Fourier scalar of the free-source columns.

The first and second exponent blocks retain their existing chronological order:
the second bank word multiplies the first. Both original conversion pairs stay
on their original sides. These identities add no caller hypothesis, normalized
state, clean-bank condition, or success claim. Completeness and the identification
of physical readout labels with frequencies remain separate mathematical steps.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ActualPointWords

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.QuantumFourierTransform QuantumFourierTransform.Semiclassical
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open Recovery.Stage.PointCoordinates Recovery.Stage.PointCoordinates.StageWord
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity.ActualFeedback
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private lemma ofFn_get_cast {n : Nat} {Stage Outcome Value : Type}
    (stages : Fin n → Stage) (outcomes : Fin n → Outcome)
    (entry : Stage → Outcome → Value) :
    List.ofFn (fun index : Fin (List.ofFn stages).length =>
      entry ((List.ofFn stages).get index)
        (outcomes (Fin.cast (List.length_ofFn (f := stages)) index))) =
      List.ofFn (fun index : Fin n => entry (stages index) (outcomes index)) := by
  let length : (List.ofFn stages).length = n := List.length_ofFn
  calc
    _ = List.ofFn (fun index : Fin n =>
        entry ((List.ofFn stages).get (Fin.cast length.symm index))
          (outcomes (Fin.cast length (Fin.cast length.symm index)))) :=
      List.ofFn_congr length _
    _ = _ := by
      apply congrArg List.ofFn
      funext index
      rw [List.get_ofFn]
      simp only [Fin.cast_cast, Fin.cast_refl]
      rfl

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}

/-- Each block retains its original addend and its original physical source-tuple coordinate. -/
def blockStages (points : Fin (2 * m) → AffinePoint E) (second : Bool) :
    List (ControlledPointWords.Stage E (Bits m)) :=
  List.ofFn (fun current : Fin m =>
    (points (position second current), fun source => tupleCoordinates m source current))

omit [Fact p.Prime] in
lemma blockStages_length (points : Fin (2 * m) → AffinePoint E) (second : Bool) :
    (blockStages E points second).length = m := List.length_ofFn

/-- Both complete real point Stores remain attached to their original chronological position. -/
def blockWord (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
    (second : Bool) (source : Bits m) :
    Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
  ControlledPointWords.bankWord (environment := environment) E (ResidualReference p.size m
    Reference)
    (blockStages E points second)
    (fun index => outcomes
      (position second (Fin.cast (blockStages_length E points second) index))) source

/-- These are the literal full-domain point bank factors, with the first stage rightmost. -/
lemma blockWord_chronologicalProduct (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
    (second : Bool) (source : Bits m) :
    blockWord (environment := environment) E points Reference outcomes second source =
      Partner.chronologicalProduct (List.ofFn (fun current : Fin m =>
        Recovery.Point.Instrument.pointBankBlock (environment := environment) E (points (position
          second current))
          (ResidualReference p.size m Reference)
          (outcomes (position second current)).2 (outcomes (position second current)).1
          (tupleCoordinates m source current))) := by
  unfold blockWord
  rw [ControlledPointWords.bankWord_chronologicalProduct]
  apply congrArg Partner.chronologicalProduct
  exact ofFn_get_cast
    (fun current : Fin m =>
      (points (position second current), fun input : Bits m => tupleCoordinates m input current))
    (fun current : Fin m => outcomes (position second current))
    (fun stage outcome => Recovery.Point.Instrument.pointBankBlock (environment := environment) E
      stage.1
      (ResidualReference p.size m Reference) outcome.2 outcome.1 (stage.2 source))

/-- The second arithmetic block acts after the first, without commuting any bank factors. -/
def pointPairWord (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
    (source : Bits m × Bits m) :
    Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
  blockWord (environment := environment) E points Reference outcomes true source.2 *
    blockWord (environment := environment) E points Reference outcomes false source.1

/-- The original conversion pairs surround the same source-specific point word. -/
def convertedPointWord (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (Reference : Register) (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
    (source : Bits m × Bits m) :
    Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
  Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
    (InPlaceTarget.modulusWord p) coefficient
      (ResidualReference p.size m Reference) *
    pointPairWord (environment := environment) E points Reference outcomes source *
    Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
      (InPlaceTarget.modulusWord p) coefficient⁻¹
      (ResidualReference p.size m Reference)

/-- Actual reconstructed bank actions lose no point outcome, original Store or Reference data. -/
lemma reconstructed_block_word (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
    (bits : Fin (2 * m) → Fin 2) (original : Store (Recovery.Layout.terminal p.size m))
    (second : Bool) (source : Bits m) :
    OrderedBankWord.word
        (ActualFeedback.pathBankAction (environment := environment) E points Reference
          (ActualOutcomeLabels.rebuildRun p.size m (2 * m) id
            (fun current => (outcomes current, bits current)) original).1 second)
        m (binaryEquiv m source).val =
      blockWord (environment := environment) E points Reference outcomes second source := by
  rw [FourierWord.word_eq_tupleWord, blockWord_chronologicalProduct]
  unfold FourierWord.tupleWord
  apply congrArg Partner.chronologicalProduct
  apply congrArg List.ofFn
  funext current
  simp only [ActualFeedback.pathBankAction, dif_pos current.rev.isLt, bitBasis_finTwo]
  exact ActualOutcomeLabels.bankBlock_rebuildRun E (points (position second current)) m
    (2 * m) Reference id (fun index => (outcomes index, bits index)) original
    (position second current) (tupleCoordinates m source current)

/-- Every reconstructed legal path has the same converted word at a fixed coherent source. -/
lemma sourceWord_rebuildRun (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
    (bits : Fin (2 * m) → Fin 2) (original : Store (Recovery.Layout.terminal p.size m))
    (source : Bits m × Bits m) :
    Recovery.Conversion.CoherentBankFamily.sourceWord (environment := environment) E points
      coefficient Reference
        (ActualOutcomeLabels.rebuildRun p.size m (2 * m) id
          (fun current => (outcomes current, bits current)) original).1 source =
      convertedPointWord (environment := environment) E points coefficient Reference outcomes
        source := by
  unfold Recovery.Conversion.CoherentBankFamily.sourceWord OrderedBankWord.exponentPair
    convertedPointWord pointPairWord
  rw [reconstructed_block_word E points Reference outcomes bits original true source.2,
    reconstructed_block_word E points Reference outcomes bits original false source.1]

/-- Trace validity reconstructs the original complete path before the word is identified. -/
lemma sourceWord_legalRun (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (path : Fin (2 * m) → Branch p.size m)
    (original final : Store (Recovery.Layout.terminal p.size m))
    (valid : traceValid p.size m (2 * m) id path original final) (source : Bits m × Bits m) :
    Recovery.Conversion.CoherentBankFamily.sourceWord (environment := environment) E points
      coefficient Reference path source =
      convertedPointWord (environment := environment) E points coefficient Reference
        (fun current => (ActualOutcomeLabels.branchOutcome p.size m (path current)).1) source := by
  have identified := sourceWord_rebuildRun (environment := environment) E points coefficient
    Reference
    (fun current => (ActualOutcomeLabels.branchOutcome p.size m (path current)).1)
    (fun current => (ActualOutcomeLabels.branchOutcome p.size m (path current)).2) original source
  have rebuilt : ActualOutcomeLabels.rebuildRun p.size m (2 * m) id
      (fun current =>
        ((ActualOutcomeLabels.branchOutcome p.size m (path current)).1,
          (ActualOutcomeLabels.branchOutcome p.size m (path current)).2)) original =
        (path, final) :=
    ActualOutcomeLabels.rebuildRun_outcomes p.size m (2 * m) id path original final valid
  rw [rebuilt] at identified
  exact identified

/-- Physical readout choices and dirty original frames do not enter this arithmetic factor. -/
lemma sourceWord_readout_independent (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
    (firstBits secondBits : Fin (2 * m) → Fin 2)
    (firstOriginal secondOriginal : Store (Recovery.Layout.terminal p.size m))
    (source : Bits m × Bits m) :
    Recovery.Conversion.CoherentBankFamily.sourceWord (environment := environment) E points
      coefficient Reference
        (ActualOutcomeLabels.rebuildRun p.size m (2 * m) id
          (fun current => (outcomes current, firstBits current)) firstOriginal).1 source =
      Recovery.Conversion.CoherentBankFamily.sourceWord (environment := environment) E points
        coefficient Reference
        (ActualOutcomeLabels.rebuildRun p.size m (2 * m) id
          (fun current => (outcomes current, secondBits current)) secondOriginal).1 source :=
  (sourceWord_rebuildRun E points coefficient Reference outcomes firstBits firstOriginal
    source).trans
    (sourceWord_rebuildRun E points coefficient Reference outcomes secondBits secondOriginal
      source).symm

/-- Only the original Fourier scalar contains physical readout data in these rectangular entries. -/
lemma freeSourceColumns_rebuildRun_entry (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
    (bits : Fin (2 * m) → Fin 2) (original : Store (Recovery.Layout.terminal p.size m))
    (source : Bits m × Bits m) (row column : Bank p.size m Reference) :
    Recovery.Conversion.FreeSourceFamily.freeSourceColumns (environment := environment) E points
      coefficient Reference
        (ActualOutcomeLabels.rebuildRun p.size m (2 * m) id
          (fun current => (outcomes current, bits current)) original).1 row (source, column) =
      Recovery.Conversion.FreeSourceFamily.pathFourierCoefficient p.size m
          (ActualOutcomeLabels.rebuildRun p.size m (2 * m) id
            (fun current => (outcomes current, bits current)) original).1 source *
        convertedPointWord (environment := environment) E points coefficient Reference outcomes
          source row column := by
  change Recovery.Conversion.FreeSourceFamily.pathFourierCoefficient p.size m _ source *
    Recovery.Conversion.CoherentBankFamily.sourceWord (environment := environment) E points
      coefficient Reference _ source
      row column = _
  rw [sourceWord_rebuildRun]

end

end ActualPointWords
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
