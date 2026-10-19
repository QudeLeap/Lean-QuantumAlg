/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Point.Bank.GoodColumns
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.ControlledPointWords

/-!
# Actual ordered point-bank columns on a locally admissible word trajectory

The head actual point outcome acts first. Its prepared bank column has the
same scalar for every complete real outcome, and the remaining bank word
acts on the translated complete words with the original Reference retained.
The local trajectory predicate uses precisely the original active affine
exclusions. Inactive bits impose no condition on either binary word.

This module does not derive that local predicate from the original good
source, identify any four conversion operators, or assert a success floor.
The trajectory and column statements are mathematical proof objects only.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace PointWordGoodColumns

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

/-- Apply each original complete word translation in physical chronological order. -/
def wordResult {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {Source : Type} :
    List (ControlledPointWords.Stage E Source) → Source →
      (Fin (2 ^ p.size) × Fin (2 ^ p.size)) → Fin (2 ^ p.size) × Fin (2 ^ p.size)
  | [], _, words => words
  | stage :: stages, source, words =>
      wordResult E stages source
        (PointBankGoodColumns.nextWords E stage.1 (stage.2 source) words)

/-- Every active original word pair is an affine point outside the same two exclusions. -/
def wordAllowed {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {Source : Type} :
    List (ControlledPointWords.Stage E Source) → Source →
      (Fin (2 ^ p.size) × Fin (2 ^ p.size)) → Prop
  | [], _, _ => True
  | stage :: stages, source, words =>
      (stage.2 source = 1 → ∃ P : AffinePoint E,
        words.1.val = P.x.val ∧ words.2.val = P.y.val ∧
          P ≠ stage.1 ∧ P ≠ AffinePoint.negate stage.1) ∧
        wordAllowed E stages source
          (PointBankGoodColumns.nextWords E stage.1 (stage.2 source) words)

private lemma bankWord_nil {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Reference : Register) {Source : Type}
    (path : Fin 0 → ControlledPointWords.Outcome p.size) (source : Source) :
    ControlledPointWords.bankWord (environment := environment) E Reference [] path source = 1 := rfl

private lemma bankWord_cons {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Reference : Register) {Source : Type} (stage : ControlledPointWords.Stage E Source)
    (stages : List (ControlledPointWords.Stage E Source))
    (path : Fin (stages.length + 1) → ControlledPointWords.Outcome p.size) (source : Source) :
    ControlledPointWords.bankWord (environment := environment) E Reference (stage :: stages) path
      source =
      ControlledPointWords.bankWord (environment := environment) E Reference stages (fun index =>
        path index.succ) source *
        Recovery.Point.Instrument.pointBankBlock (environment := environment) E stage.1 Reference
          (path 0).2 (path 0).1
          (stage.2 source) := rfl

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

/-- Every complete actual outcome word has one common scalar on the prepared trajectory. -/
lemma bankWord_prepared_column {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Reference : Register) {Source : Type} (stages : List (ControlledPointWords.Stage E Source))
    (path : Fin stages.length → ControlledPointWords.Outcome p.size) (source : Source)
    (words : Fin (2 ^ p.size) × Fin (2 ^ p.size)) (reference : Reference.Index)
    (allowed : wordAllowed E stages source words)
    (row : Recovery.Point.Instrument.FiberBank p.size Reference) :
    ControlledPointWords.bankWord (environment := environment) E Reference stages path source row
        (PointBankGoodColumns.preparedBank p Reference words reference) =
      (WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) ^ stages.length *
        (if row = PointBankGoodColumns.preparedBank p Reference
            (wordResult E stages source words) reference then 1 else 0) := by
  revert path words
  induction stages with
  | nil =>
      intro path words _
      rw [bankWord_nil]
      change (1 : Matrix (Recovery.Point.Instrument.FiberBank p.size Reference)
        (Recovery.Point.Instrument.FiberBank p.size Reference) ℂ) row
          (PointBankGoodColumns.preparedBank p Reference words reference) =
        (1 : ℂ) * (if row = PointBankGoodColumns.preparedBank p Reference words reference
          then 1 else 0)
      rw [Matrix.one_apply, one_mul]
  | cons stage stages ih =>
      intro path words allowed
      let scalar : ℂ := WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size
      let next := PointBankGoodColumns.nextWords E stage.1 (stage.2 source) words
      rw [bankWord_cons]
      change (ControlledPointWords.bankWord (environment := environment) E Reference stages
          (fun index => path index.succ) source *
        Recovery.Point.Instrument.pointBankBlock (environment := environment) E stage.1 Reference
          (path 0).2 (path 0).1
          (stage.2 source)) row (PointBankGoodColumns.preparedBank p Reference words reference) =
        scalar ^ (stages.length + 1) *
          (if row = PointBankGoodColumns.preparedBank p Reference
              (wordResult E stages source next) reference then 1 else 0)
      rw [pow_succ]
      have product := mul_delta_column
        (ControlledPointWords.bankWord (environment := environment) E Reference stages
          (fun index => path index.succ) source)
        (Recovery.Point.Instrument.pointBankBlock (environment := environment) E stage.1 Reference
          (path 0).2 (path 0).1
          (stage.2 source))
        (PointBankGoodColumns.preparedBank p Reference words reference)
        (PointBankGoodColumns.preparedBank p Reference next reference)
        (PointBankGoodColumns.preparedBank p Reference (wordResult E stages source next) reference)
        scalar (scalar ^ stages.length) row
        (fun column => by
          have entry := PointBankGoodColumns.pointBankBlock_prepared_column
            (environment := environment) E stage.1 Reference
            (path 0).2 (path 0).1 (stage.2 source) words reference allowed.1 column
          by_cases same : column = PointBankGoodColumns.preparedBank p Reference next reference
          · simpa only [scalar, next, if_pos same] using entry
          · simpa only [scalar, next, if_neg same] using entry)
        (by
          have entry := ih (fun index => path index.succ) next allowed.2
          by_cases same : row = PointBankGoodColumns.preparedBank p Reference
              (wordResult E stages source next) reference
          · simpa only [scalar, if_pos same] using entry
          · simpa only [scalar, if_neg same] using entry)
      by_cases same : row = PointBankGoodColumns.preparedBank p Reference
          (wordResult E stages source next) reference
      · simpa only [if_pos same] using product
      · simpa only [if_neg same] using product

end

end PointWordGoodColumns
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
