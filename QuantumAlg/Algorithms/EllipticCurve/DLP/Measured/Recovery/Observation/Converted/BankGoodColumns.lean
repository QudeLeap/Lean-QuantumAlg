/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Converted.CommonBank
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Point.Bank.AffineTrajectory
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Semantics
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Words

/-!
# Actual four-conversion columns on the original good affine trajectory

The original coefficient encodes the supplied seed coordinates. The two real
inverse-coefficient conversions recover those coordinates; the measured word
follows the original good trajectory; the two forward conversions encode its
result. The selector and complete Reference are retained. The original group
admissibility supplies every local exclusion internally. No coefficient is
silently specialized to one or to a radix, and no new algorithm input is added.

The finite-index schedule identification with ActualPointWords is a separate
statement. These local columns do not assert an ideal effect or success floor.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ConvertedBankGoodColumns

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private lemma mul_delta_column {Bank : Type} [Fintype Bank]
    (tail head : Matrix Bank Bank ℂ) (input middle output : Bank)
    (headScalar tailScalar : ℂ) (row : Bank)
    (headColumn : ∀ column, head column input =
      headScalar * (if column = middle then 1 else 0))
    (tailColumn : tail row middle = tailScalar * (if row = output then 1 else 0)) :
    (tail * head) row input =
      (tailScalar * headScalar) * (if row = output then 1 else 0) := by
  calc
    (tail * head) row input = tail row middle * headScalar := by
      rw [Matrix.mul_apply]
      simp only [headColumn, mul_ite, mul_one, mul_zero]
      exact Fintype.sum_ite_eq' middle (fun column => tail row column * headScalar)
    _ = (tailScalar * headScalar) * (if row = output then 1 else 0) := by
      rw [tailColumn, mul_right_comm]

private lemma nested_delta {Arithmetic Selector Reference : Type}
    (row : Arithmetic × (Selector × Reference))
    (arithmetic : Arithmetic) (selector : Selector) (reference : Reference)
    {arithmeticDecision : Decidable (row.1 = arithmetic)}
    {selectorDecision : Decidable (row.2.1 = selector)}
    {referenceDecision : Decidable (row.2.2 = reference)}
    {wholeDecision : Decidable (row = (arithmetic, (selector, reference)))} :
    (@ite ℂ (row.1 = arithmetic) arithmeticDecision 1 0) *
        (@ite ℂ (row.2.1 = selector) selectorDecision 1 0) *
        (@ite ℂ (row.2.2 = reference) referenceDecision 1 0) =
      @ite ℂ (row = (arithmetic, (selector, reference))) wholeDecision 1 0 := by
  by_cases sameArithmetic : row.1 = arithmetic <;>
    by_cases sameSelector : row.2.1 = selector <;>
    by_cases sameReference : row.2.2 = reference <;>
    simp [Prod.ext_iff, sameArithmetic, sameSelector, sameReference]

private lemma unitary_ket_column {R : Register} (operator : UnitaryOperator R)
    (input output row : R.Index)
    (action : operator.apply (NormalizedVector.ket input) = NormalizedVector.ket output) :
    operator row input = if row = output then 1 else 0 := by
  have entry := congrArg
    (fun vector : NormalizedVector R => (vector : HilbertVector R) row) action
  rw [UnitaryOperator.apply_coe, UnitaryOperator.applyVec,
    HilbertOperator.applyVec_ket, NormalizedVector.ket_apply] at entry
  by_cases same : row = output
  · simpa only [if_pos same] using entry
  · simpa only [if_neg same] using entry

open MeasuredPointAddition (fieldWord)

/-- Encode both ordinary field coordinates by the same unchanged unit coefficient. -/
def encodedWords {p : Nat} [Fact p.Prime] (coefficient : (ZMod p)ˣ) (x y : ZMod p) :
    Fin (2 ^ p.size) × Fin (2 ^ p.size) :=
  (fieldWord ((coefficient : ZMod p) * x), fieldWord ((coefficient : ZMod p) * y))

/-- One real runtime conversion changes only its selected prepared field coordinate. -/
lemma bankCoordinateOperator_prepared_column {p : Nat} [Fact p.Prime]
    (coefficient : (ZMod p)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (Reference : Register) (x y : ZMod p) (reference : Reference.Index)
    (row : Recovery.Point.Instrument.FiberBank p.size Reference) :
    Recovery.Reference.Converted.bankCoordinateOperator (environment := environment) p.size
      (QuantumAlg.MeasuredUncompute.InPlaceTarget.modulusWord p)
        coefficient coordinate Reference row
        (PointBankGoodColumns.preparedBank p Reference (fieldWord x, fieldWord y) reference) =
      if row = PointBankGoodColumns.preparedBank p Reference
          (match coordinate with
          | .x => (fieldWord ((coefficient : ZMod p) * x), fieldWord y)
          | .y => (fieldWord x, fieldWord ((coefficient : ZMod p) * y))) reference
      then 1 else 0 := by
  have valid : (ScalarMultiplication.MeasuredPlacement.Encoding.selectedInput coordinate
    (fieldWord x) (fieldWord y)).val < p := by
    cases coordinate
    · exact ZMod.val_lt x
    · exact ZMod.val_lt y
  have action := ScalarMultiplication.MeasuredPlacement.Encoding.runtimeProgram_prepared
    (environment := environment.quantum) p
    (Fact.out : Nat.Prime p).pos
    coefficient coordinate (fieldWord x) (fieldWord y) valid
  have entry := unitary_ket_column
    ((ScalarMultiplication.MeasuredPlacement.Encoding.runtimeProgram p.size
      (QuantumAlg.MeasuredUncompute.InPlaceTarget.modulusWord p) coefficient coordinate).matrix
        environment.quantum)
    (QuantumAlg.MeasuredUncompute.InPlaceTarget.preparedBasis p (fieldWord x) (fieldWord y))
    (ScalarMultiplication.MeasuredPlacement.Encoding.preparedRuntimeUpdate p coordinate
      (fieldWord x) (fieldWord y)
      (Nat.FixedWidth.unitProductWord (QuantumAlg.MeasuredUncompute.InPlaceTarget.modulusWord p)
        (Fact.out : Nat.Prime p).pos coefficient
        (ScalarMultiplication.MeasuredPlacement.Encoding.selectedInput coordinate (fieldWord x)
          (fieldWord y)))) row.1 action
  cases coordinate with
  | x =>
      simp only [ScalarMultiplication.MeasuredPlacement.Encoding.selectedInput,
        ScalarMultiplication.MeasuredPlacement.Encoding.preparedRuntimeUpdate,
        ScalarMultiplication.MeasuredPlacement.Encoding.unitProductWord_fieldWord] at entry
      simp only [Recovery.Reference.Converted.bankCoordinateOperator,
        PointBankGoodColumns.preparedBank]
      rw [entry]
      exact nested_delta row
        (QuantumAlg.MeasuredUncompute.InPlaceTarget.preparedBasis p (fieldWord ((coefficient :
          ZMod p) * x))
          (fieldWord y)) (0 : Fin 2) reference
  | y =>
      simp only [ScalarMultiplication.MeasuredPlacement.Encoding.selectedInput,
        ScalarMultiplication.MeasuredPlacement.Encoding.preparedRuntimeUpdate,
        ScalarMultiplication.MeasuredPlacement.Encoding.unitProductWord_fieldWord] at entry
      simp only [Recovery.Reference.Converted.bankCoordinateOperator,
        PointBankGoodColumns.preparedBank]
      rw [entry]
      exact nested_delta row
        (QuantumAlg.MeasuredUncompute.InPlaceTarget.preparedBasis p (fieldWord x)
          (fieldWord ((coefficient : ZMod p) * y))) (0 : Fin 2) reference

/-- Both actual conversions retain every prepared work bit, selector and reference. -/
lemma bankPairOperator_prepared_column {p : Nat} [Fact p.Prime]
    (coefficient : (ZMod p)ˣ) (Reference : Register) (x y : ZMod p)
    (reference : Reference.Index) (row : Recovery.Point.Instrument.FiberBank p.size Reference) :
    Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
      (QuantumAlg.MeasuredUncompute.InPlaceTarget.modulusWord p)
        coefficient Reference row
        (PointBankGoodColumns.preparedBank p Reference (fieldWord x, fieldWord y) reference) =
      if row = PointBankGoodColumns.preparedBank p Reference
          (encodedWords coefficient x y) reference then 1 else 0 := by
  unfold Recovery.Reference.Converted.bankPairOperator
  have product := mul_delta_column
    (Recovery.Reference.Converted.bankCoordinateOperator (environment := environment) p.size
      (QuantumAlg.MeasuredUncompute.InPlaceTarget.modulusWord p)
      coefficient .y Reference)
    (Recovery.Reference.Converted.bankCoordinateOperator (environment := environment) p.size
      (QuantumAlg.MeasuredUncompute.InPlaceTarget.modulusWord p)
      coefficient .x Reference)
    (PointBankGoodColumns.preparedBank p Reference (fieldWord x, fieldWord y) reference)
    (PointBankGoodColumns.preparedBank p Reference
      (fieldWord ((coefficient : ZMod p) * x), fieldWord y) reference)
    (PointBankGoodColumns.preparedBank p Reference (encodedWords coefficient x y) reference)
    1 1 row
    (fun middle => by
      have entry :=
        bankCoordinateOperator_prepared_column (environment := environment) coefficient .x
          Reference x y reference middle
      by_cases same : middle = PointBankGoodColumns.preparedBank p Reference
          (fieldWord ((coefficient : ZMod p) * x), fieldWord y) reference
      · simpa only [one_mul, if_pos same] using entry
      · simpa only [one_mul, if_neg same] using entry)
    (by
      rw [encodedWords]
      have entry := bankCoordinateOperator_prepared_column (environment := environment)
        coefficient .y Reference
        ((coefficient : ZMod p) * x) y reference row
      by_cases same : row = PointBankGoodColumns.preparedBank p Reference
          (fieldWord ((coefficient : ZMod p) * x),
            fieldWord ((coefficient : ZMod p) * y)) reference
      · simpa only [one_mul, if_pos same] using entry
      · simpa only [one_mul, if_neg same] using entry)
  by_cases same : row = PointBankGoodColumns.preparedBank p Reference
      (encodedWords coefficient x y) reference
  · simpa only [one_mul, if_pos same] using product
  · simpa only [one_mul, if_neg same] using product

/-- The actual inverse pair recovers the supplied seed, without changing its coefficient domain. -/
lemma inversePairOperator_encoded_column {p : Nat} [Fact p.Prime]
    (coefficient : (ZMod p)ˣ) (Reference : Register) (x y : ZMod p)
    (reference : Reference.Index) (row : Recovery.Point.Instrument.FiberBank p.size Reference) :
    Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
      (QuantumAlg.MeasuredUncompute.InPlaceTarget.modulusWord p)
        coefficient⁻¹ Reference row
        (PointBankGoodColumns.preparedBank p Reference
          (encodedWords coefficient x y) reference) =
      if row = PointBankGoodColumns.preparedBank p Reference
          (fieldWord x, fieldWord y) reference then 1 else 0 := by
  rw [encodedWords]
  have decodedWords :
      encodedWords coefficient⁻¹ ((coefficient : ZMod p) * x)
          ((coefficient : ZMod p) * y) = (fieldWord x, fieldWord y) := by
    simp only [encodedWords, ← mul_assoc, Units.inv_mul, one_mul]
  have decoded := congrArg
    (fun words => PointBankGoodColumns.preparedBank p Reference words reference) decodedWords
  have actual := bankPairOperator_prepared_column (environment := environment) coefficient⁻¹
    Reference
    ((coefficient : ZMod p) * x) ((coefficient : ZMod p) * y) reference row
  by_cases same : row = PointBankGoodColumns.preparedBank p Reference
      (fieldWord x, fieldWord y) reference
  · have sameEncoded : row = PointBankGoodColumns.preparedBank p Reference
        (encodedWords coefficient⁻¹ ((coefficient : ZMod p) * x)
          ((coefficient : ZMod p) * y)) reference :=
      same.trans decoded.symm
    simp only [if_pos sameEncoded] at actual
    simp only [if_pos same]
    exact actual
  · have differentEncoded : row ≠ PointBankGoodColumns.preparedBank p Reference
        (encodedWords coefficient⁻¹ ((coefficient : ZMod p) * x)
          ((coefficient : ZMod p) * y)) reference :=
      fun matched => same (matched.trans decoded)
    simp only [if_neg differentEncoded] at actual
    simp only [if_neg same]
    exact actual

/-- The unchanged original good set gives the full literal four-conversion column. -/
lemma convertedAffineWord_prepared_column {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} {Source : Type}
    (points : Fin count → AffinePoint E) (controls : Source → Fin count → Bool)
    (source : Source) (seed : AffinePoint E) (coefficient : (ZMod p)ˣ)
    (Reference : Register)
    (path : Fin (PointBankAffineTrajectory.affineStages E points controls
      (List.finRange count)).length → ControlledPointWords.Outcome p.size)
    (reference : Reference.Index)
    (good : ExceptionalOffsetAveraging.Admissible count controls
      (fun index => (points index).toGroupPoint) seed.toGroupPoint source)
    (row : Recovery.Point.Instrument.FiberBank p.size Reference) :
    (Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
      (QuantumAlg.MeasuredUncompute.InPlaceTarget.modulusWord p)
        coefficient Reference *
      ControlledPointWords.bankWord (environment := environment) E Reference
        (PointBankAffineTrajectory.affineStages E points controls (List.finRange count))
        path source *
      Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
        (QuantumAlg.MeasuredUncompute.InPlaceTarget.modulusWord p)
        coefficient⁻¹ Reference) row
      (PointBankGoodColumns.preparedBank p Reference
        (encodedWords coefficient seed.x seed.y) reference) =
      (WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) ^
        (PointBankAffineTrajectory.affineStages E points controls (List.finRange count)).length *
      (if row = PointBankGoodColumns.preparedBank p Reference
        (encodedWords coefficient
          (ScalarMultiplication.AffineTrajectory.path E points (controls source) (List.finRange
            count) seed).x
          (ScalarMultiplication.AffineTrajectory.path E points (controls source) (List.finRange
            count) seed).y)
        reference then 1 else 0) := by
  let final := ScalarMultiplication.AffineTrajectory.path E points (controls source)
    (List.finRange count) seed
  let scalar : ℂ :=
    (WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) ^
      (PointBankAffineTrajectory.affineStages E points controls (List.finRange count)).length
  have wordColumn := PointWordGoodColumns.bankWord_prepared_column
    (environment := environment) E Reference
    (PointBankAffineTrajectory.affineStages E points controls (List.finRange count))
    path source (PointBankAffineTrajectory.fieldWords seed) reference
    (PointBankAffineTrajectory.wordAllowed_finRange_of_group E points controls source seed good)
  rw [PointBankAffineTrajectory.wordResult_finRange_of_group E points controls source seed good]
    at wordColumn
  have leftColumn (middle : Recovery.Point.Instrument.FiberBank p.size Reference) :=
    mul_delta_column
    (Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
      (QuantumAlg.MeasuredUncompute.InPlaceTarget.modulusWord p)
      coefficient Reference)
    (ControlledPointWords.bankWord (environment := environment) E Reference
      (PointBankAffineTrajectory.affineStages E points controls (List.finRange count)) path source)
    (PointBankGoodColumns.preparedBank p Reference
      (PointBankAffineTrajectory.fieldWords seed) reference)
    (PointBankGoodColumns.preparedBank p Reference
      (PointBankAffineTrajectory.fieldWords final) reference)
    (PointBankGoodColumns.preparedBank p Reference
      (encodedWords coefficient final.x final.y) reference)
    scalar 1 middle
    (fun column => by
      have entry := wordColumn column
      by_cases same : column = PointBankGoodColumns.preparedBank p Reference
          (PointBankAffineTrajectory.fieldWords final) reference
      · simpa only [scalar, final, if_pos same] using entry
      · simpa only [scalar, final, if_neg same] using entry)
    (by
      have entry :=
        bankPairOperator_prepared_column (environment := environment) coefficient Reference
          final.x final.y reference middle
      by_cases same : middle = PointBankGoodColumns.preparedBank p Reference
          (encodedWords coefficient final.x final.y) reference
      · simpa only [one_mul, PointBankAffineTrajectory.fieldWords, if_pos same] using entry
      · simpa only [one_mul, PointBankAffineTrajectory.fieldWords, if_neg same] using entry)
  have product := mul_delta_column
    (Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
      (QuantumAlg.MeasuredUncompute.InPlaceTarget.modulusWord p)
        coefficient Reference *
      ControlledPointWords.bankWord (environment := environment) E Reference
        (PointBankAffineTrajectory.affineStages E points controls (List.finRange count))
        path source)
    (Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
      (QuantumAlg.MeasuredUncompute.InPlaceTarget.modulusWord p)
      coefficient⁻¹ Reference)
    (PointBankGoodColumns.preparedBank p Reference
      (encodedWords coefficient seed.x seed.y) reference)
    (PointBankGoodColumns.preparedBank p Reference
      (PointBankAffineTrajectory.fieldWords seed) reference)
    (PointBankGoodColumns.preparedBank p Reference
      (encodedWords coefficient final.x final.y) reference) 1 scalar row
    (fun middle => by
      rw [PointBankAffineTrajectory.fieldWords]
      have entry :=
        inversePairOperator_encoded_column (environment := environment) coefficient Reference
          seed.x seed.y reference middle
      by_cases same : middle = PointBankGoodColumns.preparedBank p Reference
          (fieldWord seed.x, fieldWord seed.y) reference
      · simpa only [one_mul, if_pos same] using entry
      · simpa only [one_mul, if_neg same] using entry)
    (by
      by_cases same : row = PointBankGoodColumns.preparedBank p Reference
          (encodedWords coefficient final.x final.y) reference
      · simpa only [one_mul, if_pos same] using leftColumn row
      · simpa only [one_mul, if_neg same] using leftColumn row)
  by_cases same : row = PointBankGoodColumns.preparedBank p Reference
      (encodedWords coefficient final.x final.y) reference
  · simpa only [mul_one, scalar, final, if_pos same] using product
  · simpa only [mul_one, scalar, final, if_neg same] using product

end

end ConvertedBankGoodColumns
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
