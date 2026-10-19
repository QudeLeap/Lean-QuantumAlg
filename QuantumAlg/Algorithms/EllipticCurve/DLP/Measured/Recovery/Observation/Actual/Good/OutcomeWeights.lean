/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.Good.Columns
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.FamilyCompleteness
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Prepared.BankGroupKernel

/-!
# Exact weight of the complete actual point-outcome word family on a good source

The original good column has the same scalar for every complete real point
outcome word. The actual complete Gram identity, evaluated on its prepared
input, proves that the sum of the scalar squared magnitudes is one. This counts
the full final/division Store word type without a cardinality approximation,
postselection, discarded zero branch, or renormalization of the good component.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ActualGoodOutcomeWeights

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open _root_.QuantumAlg.QuantumFourierTransform.Semiclassical (Bits)
open Recovery.Stage.PointCoordinates (Bank ResidualReference)
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

/-- The literal common scalar has one measured point factor for every original stage. -/
def amplitude (width m : Nat) : ℂ :=
  (WalshHadamard.invSqrtCard width * WalshHadamard.invSqrtCard width) ^ (2 * m)

include environment in
/-- Every real final/division Store word contributes; their exact total weight is one. -/
lemma complete_point_weight {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (Reference : Register) (source : Bits m × Bits m) (seed : AffinePoint E)
    (reference : (ResidualReference p.size m Reference).Index)
    (good : ExceptionalOffsetAveraging.Admissible (2 * m)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected m)
      (fun index => (points index).toGroupPoint) seed.toGroupPoint
      (SourceControls.sourceValues m source)) :
    (∑ _outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size,
      star (amplitude p.size m) * amplitude p.size m) = 1 := by
  let input := PointBankGoodColumns.preparedBank p (ResidualReference p.size m Reference)
    (ConvertedBankGoodColumns.encodedWords coefficient seed.x seed.y) reference
  let final := ScalarMultiplication.AffineTrajectory.path E points
    (SourceControls.controls m source)
    (List.finRange (2 * m)) seed
  let output := PointBankGoodColumns.preparedBank p (ResidualReference p.size m Reference)
    (ConvertedBankGoodColumns.encodedWords coefficient final.x final.y) reference
  have column (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size)
      (row : Bank p.size m Reference) :
      ActualPointWords.convertedPointWord (environment := environment) (m := m) E points
        coefficient Reference outcomes source
          row input = amplitude p.size m * (if row = output then 1 else 0) := by
    simpa only [input, output, final, amplitude] using
      ActualGoodColumns.convertedPointWord_prepared_column (m := m) E points coefficient
        Reference
        outcomes source seed reference good row
  have gram (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome p.size) :
      ((ActualPointWords.convertedPointWord (environment := environment) (m := m) E points
        coefficient Reference outcomes
          source).conjTranspose *
        ActualPointWords.convertedPointWord (environment := environment) (m := m) E points
          coefficient Reference
          outcomes source)
        input input = star (amplitude p.size m) * amplitude p.size m := by
    simpa only [if_pos rfl, ite_true, mul_one] using
      PreparedBankGroupKernel.gram_delta_columns
        (ActualPointWords.convertedPointWord (environment := environment) (m := m) E points
          coefficient Reference
          outcomes source)
        (ActualPointWords.convertedPointWord (environment := environment) (m := m) E points
          coefficient Reference
          outcomes source)
        input input output output (amplitude p.size m) (amplitude p.size m)
        (fun row => by
          have entry := column outcomes row
          split_ifs at entry ⊢ <;> exact entry)
        (fun row => by
          have entry := column outcomes row
          split_ifs at entry ⊢ <;> exact entry)
  have complete := congrArg (fun matrix : Matrix (Bank p.size m Reference)
      (Bank p.size m Reference) ℂ => matrix input input)
    (ActualFamilyCompleteness.convertedPointWord_complete (environment := environment)
      (m := m) E points coefficient Reference source)
  simpa only [Matrix.sum_apply, gram, Matrix.one_apply_eq] using complete

end

end ActualGoodOutcomeWeights
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
