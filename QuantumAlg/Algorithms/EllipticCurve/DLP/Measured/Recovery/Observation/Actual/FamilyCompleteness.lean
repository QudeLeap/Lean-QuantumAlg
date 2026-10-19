/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.PointWords
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Converted.WordCompleteness
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.ReadoutFrequencyLabels
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.FourierKrausCompleteness
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.FullFrequencyOrthogonality

/-!
# Completeness of the actual legal free-source family

Every complete legal path has one real point-outcome word and one pair of
canonical physical readout frequencies. The two complete point words retain
all four actual conversions; full-frequency orthogonality removes the
cross-source Gram entries without assuming cross-source Kraus orthogonality.

The source basis is exactly the existing pair of recursive tuples followed by
the entire bank. No preparation amplitude, normalization, clean frame or
restriction on the original Store or external Reference enters this identity.
The bijection retains every legal label, including zero CP branches and zero
width. This proof introduces no runtime or algorithm caller hypothesis, and
constructs neither a selected effect nor a success floor.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ActualFamilyCompleteness

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution
open _root_.QuantumAlg.QuantumFourierTransform.Semiclassical (Bits)
open _root_.QuantumAlg.QuantumFourierTransform.Semiclassical.Partner (fourierRows fullRows)
open Recovery.Stage.PointCoordinates (ResidualReference)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity (Branch)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity.ActualFeedback
  (position blockOutput blockFrequency pathFrequency blockFrequency_fullRow)
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private def splitOutcomeWord {Outcome : Type} (m : Nat) :
    (Fin (2 * m) → Outcome) ≃ (Fin m → Outcome) × (Fin m → Outcome) :=
  (Equiv.arrowCongr (finCongr (Nat.two_mul m)) (Equiv.refl Outcome)).trans
    (Fin.appendEquiv m m).symm

private lemma splitOutcomeWord_fst {Outcome : Type} (m : Nat)
    (outcomes : Fin (2 * m) → Outcome) (current : Fin m) :
    (splitOutcomeWord m outcomes).1 current = outcomes (position false current) := by
  change outcomes ((finCongr (Nat.two_mul m)).symm (Fin.castAdd m current)) = _
  rw [← ReadoutFrequencyLabels.position_false]

private lemma splitOutcomeWord_snd {Outcome : Type} (m : Nat)
    (outcomes : Fin (2 * m) → Outcome) (current : Fin m) :
    (splitOutcomeWord m outcomes).2 current = outcomes (position true current) := by
  change outcomes ((finCongr (Nat.two_mul m)).symm (Fin.natAdd m current)) = _
  rw [← ReadoutFrequencyLabels.position_true]

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}

private def blockPathsEquiv (points : Fin (2 * m) → AffinePoint E) :
    (Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size) ≃
      (Fin (ActualPointWords.blockStages E points false).length →
        ControlledPointWords.Outcome p.size) ×
      (Fin (ActualPointWords.blockStages E points true).length →
        ControlledPointWords.Outcome p.size) :=
  (splitOutcomeWord m).trans (Equiv.prodCongr
    (Equiv.arrowCongr
      (Fin.castOrderIso (ActualPointWords.blockStages_length E points false)).toEquiv.symm
      (Equiv.refl _))
    (Equiv.arrowCongr
      (Fin.castOrderIso (ActualPointWords.blockStages_length E points true)).toEquiv.symm
      (Equiv.refl _)))

omit [Fact p.Prime] in
private lemma blockPathsEquiv_fst (points : Fin (2 * m) → AffinePoint E)
    (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size) :
    (blockPathsEquiv E points outcomes).1 = fun index =>
      outcomes (position false
        (Fin.cast (ActualPointWords.blockStages_length E points false) index)) := by
  funext index
  exact splitOutcomeWord_fst m outcomes
    (Fin.cast (ActualPointWords.blockStages_length E points false) index)

omit [Fact p.Prime] in
private lemma blockPathsEquiv_snd (points : Fin (2 * m) → AffinePoint E)
    (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size) :
    (blockPathsEquiv E points outcomes).2 = fun index =>
      outcomes (position true
        (Fin.cast (ActualPointWords.blockStages_length E points true) index)) := by
  funext index
  exact splitOutcomeWord_snd m outcomes
    (Fin.cast (ActualPointWords.blockStages_length E points true) index)

private lemma convertedPointWord_pair (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
    (source : Bits m × Bits m) :
    ActualPointWords.convertedPointWord (environment := environment) E points coefficient
      Reference outcomes source =
      ConvertedWordCompleteness.convertedPairWord (environment := environment) E coefficient
        (ResidualReference p.size m Reference)
        (ActualPointWords.blockStages E points false)
        (ActualPointWords.blockStages E points true)
        (blockPathsEquiv E points outcomes).1 (blockPathsEquiv E points outcomes).2
        source.1 source.2 := by
  unfold ActualPointWords.convertedPointWord ActualPointWords.pointPairWord
    ActualPointWords.blockWord ConvertedWordCompleteness.convertedPairWord
  rw [blockPathsEquiv_fst, blockPathsEquiv_snd]

/-- Every complete real point-outcome word is counted once at each coherent source. -/
lemma convertedPointWord_complete (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register) (source : Bits m × Bits m) :
    ∑ outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size,
      (ActualPointWords.convertedPointWord (environment := environment) E points coefficient
        Reference outcomes
        source).conjTranspose *
        ActualPointWords.convertedPointWord (environment := environment) E points coefficient
          Reference outcomes source = 1 := by
  let family := fun paths :
      (Fin (ActualPointWords.blockStages E points false).length →
        ControlledPointWords.Outcome p.size) ×
      (Fin (ActualPointWords.blockStages E points true).length →
        ControlledPointWords.Outcome p.size) =>
    ConvertedWordCompleteness.convertedPairWord (environment := environment) E coefficient
      (ResidualReference p.size m Reference)
      (ActualPointWords.blockStages E points false)
      (ActualPointWords.blockStages E points true) paths.1 paths.2 source.1 source.2
  calc
    _ = ∑ paths, (family paths).conjTranspose * family paths := by
      simp only [convertedPointWord_pair]
      exact (blockPathsEquiv E points).sum_comp
        (fun paths => (family paths).conjTranspose * family paths)
    _ = 1 := by
      simpa only [family, Fintype.sum_prod_type] using
        ConvertedWordCompleteness.convertedPairWord_complete E coefficient
          (ResidualReference p.size m Reference)
          (ActualPointWords.blockStages E points false)
          (ActualPointWords.blockStages E points true) source.1 source.2

private lemma pathFourierCoefficient_pairRows (width m : Nat)
    (path : Fin (2 * m) → Branch width m) (source : Bits m × Bits m) :
    Conversion.FreeSourceFamily.pathFourierCoefficient width m path source =
      FullFrequencyOrthogonality.pairRows m (pathFrequency width m path) source := by
  change fourierRows true m (blockOutput width m path true) source.2 *
    fourierRows true m (blockOutput width m path false) source.1 =
      fullRows true m (blockFrequency width m path true) source.2 *
        fullRows true m (blockFrequency width m path false) source.1
  rw [blockFrequency_fullRow, blockFrequency_fullRow]

/-- Literal legal columns have exactly the independent point and frequency coordinates. -/
lemma legalColumns_eq_frequencyColumns (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (original : Store (Recovery.Layout.terminal p.size m))
    (run : Conversion.FreeSourceFamily.LegalOutcome p m original) :
    Conversion.FreeSourceFamily.legalColumns (environment := environment) E points coefficient
      Reference original run =
      FourierKrausCompleteness.columns (FullFrequencyOrthogonality.pairRows m)
        (ActualPointWords.convertedPointWord (environment := environment) E points coefficient
          Reference)
        (ReadoutFrequencyLabels.pointAndFrequencyEquiv p.size m original run).2
        (ReadoutFrequencyLabels.pointAndFrequencyEquiv p.size m original run).1 := by
  have pointLabels :
      (fun current => (ActualOutcomeLabels.branchOutcome p.size m (run.2.val current)).1) =
        (ReadoutFrequencyLabels.pointAndFrequencyEquiv p.size m original run).1 := by
    funext current
    exact (ReadoutFrequencyLabels.pointAndFrequencyEquiv_point
      p.size m original run current).symm
  ext row input
  rcases input with ⟨source, column⟩
  change Conversion.FreeSourceFamily.pathFourierCoefficient p.size m run.2.val source *
    Conversion.CoherentBankFamily.sourceWord (environment := environment) E points coefficient
      Reference run.2.val
      source row column =
      FullFrequencyOrthogonality.pairRows m
        (ReadoutFrequencyLabels.pointAndFrequencyEquiv p.size m original run).2 source *
        ActualPointWords.convertedPointWord (environment := environment) E points coefficient
          Reference
          (ReadoutFrequencyLabels.pointAndFrequencyEquiv p.size m original run).1
          source row column
  rw [ActualPointWords.sourceWord_legalRun E points coefficient Reference run.2.val
    original run.1 run.2.property source, pointLabels, pathFourierCoefficient_pairRows,
    ReadoutFrequencyLabels.pointAndFrequencyEquiv_frequency]

/-- The exact entire legal actual family is complete on the existing free-source register. -/
lemma legalColumns_complete (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (original : Store (Recovery.Layout.terminal p.size m)) :
    ∑ run : Conversion.FreeSourceFamily.LegalOutcome p m original,
      (Conversion.FreeSourceFamily.legalColumns (environment := environment) E points coefficient
        Reference original
        run).conjTranspose *
        Conversion.FreeSourceFamily.legalColumns (environment := environment) E points coefficient
          Reference original run =
      (1 : HilbertOperator (Conversion.FreeSourceFamily.sourceRegister p.size m Reference)) := by
  let columns := FourierKrausCompleteness.columns (FullFrequencyOrthogonality.pairRows m)
    (ActualPointWords.convertedPointWord (environment := environment) E points coefficient
      Reference)
  calc
    _ = ∑ run : Conversion.FreeSourceFamily.LegalOutcome p m original,
        (columns (ReadoutFrequencyLabels.pointAndFrequencyEquiv p.size m original run).2
          (ReadoutFrequencyLabels.pointAndFrequencyEquiv p.size m original run).1).conjTranspose *
        columns (ReadoutFrequencyLabels.pointAndFrequencyEquiv p.size m original run).2
          (ReadoutFrequencyLabels.pointAndFrequencyEquiv p.size m original run).1 := by
      apply Finset.sum_congr rfl
      intro run _
      rw [legalColumns_eq_frequencyColumns]
      rfl
    _ = ∑ labels : (Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size) ×
          (Fin (2 ^ m) × Fin (2 ^ m)),
        (columns labels.2 labels.1).conjTranspose * columns labels.2 labels.1 :=
      (ReadoutFrequencyLabels.pointAndFrequencyEquiv p.size m original).sum_comp
        (fun labels => (columns labels.2 labels.1).conjTranspose * columns labels.2 labels.1)
    _ = ∑ frequency : Fin (2 ^ m) × Fin (2 ^ m),
        ∑ outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size,
          (columns frequency outcomes).conjTranspose * columns frequency outcomes := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = 1 := FourierKrausCompleteness.columns_complete
      (FullFrequencyOrthogonality.pairRows m)
      (ActualPointWords.convertedPointWord (environment := environment) E points coefficient
        Reference)
      (by
        intro source target
        have orthogonal := FullFrequencyOrthogonality.pairRows_orthogonal m source target
        by_cases same : source = target
        · simpa only [if_pos same] using orthogonal
        · simpa only [if_neg same] using orthogonal)
      (convertedPointWord_complete E points coefficient Reference)

end

end ActualFamilyCompleteness
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
