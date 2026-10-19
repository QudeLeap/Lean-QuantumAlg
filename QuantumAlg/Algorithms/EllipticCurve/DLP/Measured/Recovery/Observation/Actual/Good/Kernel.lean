/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.Good.Columns
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Prepared.BankGroupKernel

/-!
# Actual good source columns have the original group and Reference Gram kernel

At any complete legal actual path, both original good coherent source columns
have the same real-point outcome scalar. Their full bank Gram entry retains
the original group output equality and every residual Reference label. No
point outcome, frequency label or complete Store is summed out here.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ActualGoodKernel

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private lemma gram_delta_columns_decision {Bank : Type} [Fintype Bank] [DecidableEq Bank]
    (first second : Matrix Bank Bank ℂ) (inputLeft inputRight outputLeft outputRight : Bank)
    (firstScalar secondScalar : ℂ)
    (firstColumn : ∀ row, first row inputLeft =
      firstScalar * if row = outputLeft then 1 else 0)
    (secondColumn : ∀ row, second row inputRight =
      secondScalar * if row = outputRight then 1 else 0) :
    (first.conjTranspose * second) inputLeft inputRight =
      (star firstScalar * secondScalar) * if outputLeft = outputRight then 1 else 0 := by
  have gram := PreparedBankGroupKernel.gram_delta_columns (Bank := Bank)
    first second inputLeft inputRight outputLeft outputRight firstScalar secondScalar
    (fun row => by
      have entry := firstColumn row
      split_ifs at entry ⊢ <;> exact entry)
    (fun row => by
      have entry := secondColumn row
      split_ifs at entry ⊢ <;> exact entry)
  split_ifs at gram ⊢ <;> exact gram

private lemma indicator_congr_decision (condition : Prop)
    (first second : Decidable condition) :
    (@ite ℂ condition first 1 0) = (@ite ℂ condition second 1 0) :=
  congrArg (fun decision : Decidable condition => @ite ℂ condition decision 1 0)
    (Subsingleton.elim first second)

private lemma gram_delta_columns_kernel_decision {Bank : Type} [Fintype Bank]
    (first second : Matrix Bank Bank ℂ) (inputLeft inputRight outputLeft outputRight : Bank)
    (scalar : ℂ) (kernel : Prop) [Decidable kernel]
    (firstDecision secondDecision : DecidableEq Bank)
    (firstColumn : ∀ row, first row inputLeft =
      scalar * @ite ℂ (row = outputLeft) (firstDecision row outputLeft) 1 0)
    (secondColumn : ∀ row, second row inputRight =
      scalar * @ite ℂ (row = outputRight) (secondDecision row outputRight) 1 0)
    (outputSame : outputLeft = outputRight ↔ kernel) :
    (first.conjTranspose * second) inputLeft inputRight =
      (star scalar * scalar) * if kernel then 1 else 0 := by
  let bankDecision : DecidableEq Bank := Classical.decEq Bank
  have firstAdapted (row : Bank) : first row inputLeft =
      scalar * @ite ℂ (row = outputLeft) (bankDecision row outputLeft) 1 0 :=
    (firstColumn row).trans (congrArg (fun value : ℂ => scalar * value)
      (indicator_congr_decision (row = outputLeft)
        (firstDecision row outputLeft) (bankDecision row outputLeft)))
  have secondAdapted (row : Bank) : second row inputRight =
      scalar * @ite ℂ (row = outputRight) (bankDecision row outputRight) 1 0 :=
    (secondColumn row).trans (congrArg (fun value : ℂ => scalar * value)
      (indicator_congr_decision (row = outputRight)
        (secondDecision row outputRight) (bankDecision row outputRight)))
  have gram := @gram_delta_columns_decision Bank _ bankDecision
    first second inputLeft inputRight outputLeft outputRight scalar scalar
    firstAdapted secondAdapted
  have indicators : (@ite ℂ (outputLeft = outputRight)
      (bankDecision outputLeft outputRight) 1 0) = if kernel then 1 else 0 := by
    simp only [outputSame]
  exact gram.trans (congrArg (fun value : ℂ => (star scalar * scalar) * value) indicators)

open QuantumAlg.Execution (Store)
open _root_.QuantumAlg.QuantumFourierTransform.Semiclassical (Bits)
open _root_.QuantumAlg.FiniteCyclicDLP (KnownOrderProblem orderWidth)
open Recovery.Stage.PointCoordinates (Bank ResidualReference)
open GenericPointAddition.InPlace.Semantics (radixUnit)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity (Branch traceValid)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}

-- The column interface supplies the word entries; its circuit product stays sealed here.
attribute [local irreducible] Recovery.Conversion.CoherentBankFamily.sourceWord
  Recovery.Initialization.resetArithmeticLabel PointBankGoodColumns.preparedBank
  ConvertedBankGoodColumns.encodedWords
  Recovery.Point.cellsPlacement

set_option maxHeartbeats 400000 in
-- The two full bank/Reference column carriers require this finite local elaboration budget.
/-- Each full legal path keeps the original group-equality kernel on its two good source columns. -/
lemma sourceWord_reset_gram (points : Fin (2 * m) → AffinePoint E)
    (fieldTail : Nat) (odd : Odd p) (Reference : Register)
    (path : Fin (2 * m) → Branch p.size m)
    (original final : Store (Recovery.Layout.terminal p.size m))
    (valid : traceValid p.size m (2 * m) id path original final)
    (left right : Bits m × Bits m) (seed : AffinePoint E)
    (refLeft refRight : (ResidualReference p.size m Reference).Index)
    (leftGood : ExceptionalOffsetAveraging.Admissible (2 * m)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected m)
      (fun index => (points index).toGroupPoint) seed.toGroupPoint
      (SourceControls.sourceValues m left))
    (rightGood : ExceptionalOffsetAveraging.Admissible (2 * m)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected m)
      (fun index => (points index).toGroupPoint) seed.toGroupPoint
      (SourceControls.sourceValues m right)) :
    ((Recovery.Conversion.CoherentBankFamily.sourceWord (environment := environment) E points
        (radixUnit p fieldTail.succ odd) Reference path left).conjTranspose *
      Recovery.Conversion.CoherentBankFamily.sourceWord (environment := environment) E points
        (radixUnit p fieldTail.succ odd) Reference path right)
      (Recovery.Initialization.resetArithmeticLabel E fieldTail seed, (0, refLeft))
      (Recovery.Initialization.resetArithmeticLabel E fieldTail seed, (0, refRight)) =
      (star ((WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) ^
        (2 * m)) *
        (WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) ^ (2 * m)) *
      (if (ScalarMultiplication.AffineTrajectory.path E points
          (SourceControls.controls m left)
            (List.finRange (2 * m)) seed).toGroupPoint =
          (ScalarMultiplication.AffineTrajectory.path E points
          (SourceControls.controls m right)
            (List.finRange (2 * m)) seed).toGroupPoint ∧ refLeft = refRight
        then 1 else 0) := by
  let scalar : ℂ :=
    (WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) ^ (2 * m)
  let first : Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
    Recovery.Conversion.CoherentBankFamily.sourceWord (environment := environment) E points
      (radixUnit p fieldTail.succ odd) Reference path left
  let second : Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
    Recovery.Conversion.CoherentBankFamily.sourceWord (environment := environment) E points
      (radixUnit p fieldTail.succ odd) Reference path right
  let inputLeft : Bank p.size m Reference :=
    (Recovery.Initialization.resetArithmeticLabel E fieldTail seed, (0, refLeft))
  let inputRight : Bank p.size m Reference :=
    (Recovery.Initialization.resetArithmeticLabel E fieldTail seed, (0, refRight))
  let pointLeft : AffinePoint E := ScalarMultiplication.AffineTrajectory.path E points
    (SourceControls.controls m left) (List.finRange (2 * m)) seed
  let pointRight : AffinePoint E := ScalarMultiplication.AffineTrajectory.path E points
    (SourceControls.controls m right) (List.finRange (2 * m)) seed
  let outputLeft : Bank p.size m Reference :=
    PointBankGoodColumns.preparedBank p (ResidualReference p.size m Reference)
      (ConvertedBankGoodColumns.encodedWords (radixUnit p fieldTail.succ odd)
        pointLeft.x pointLeft.y) refLeft
  let outputRight : Bank p.size m Reference :=
    PointBankGoodColumns.preparedBank p (ResidualReference p.size m Reference)
      (ConvertedBankGoodColumns.encodedWords (radixUnit p fieldTail.succ odd)
        pointRight.x pointRight.y) refRight
  exact gram_delta_columns_kernel_decision (Bank := Bank p.size m Reference)
    first second inputLeft inputRight outputLeft outputRight scalar
    (pointLeft.toGroupPoint = pointRight.toGroupPoint ∧ refLeft = refRight)
    (Classical.decEq _) (Classical.decEq _)
    (fun row => by
      have column := ActualGoodColumns.sourceWord_reset_column (environment := environment) E (m
        := m)
        points fieldTail odd Reference path original final valid left seed refLeft leftGood row
      refine column.trans ?_
      exact congrArg (fun value : ℂ => scalar * value)
        (indicator_congr_decision (row = outputLeft) _ _))
    (fun row => by
      have column := ActualGoodColumns.sourceWord_reset_column (environment := environment) E (m
        := m)
        points fieldTail odd Reference path original final valid right seed refRight rightGood row
      refine column.trans ?_
      exact congrArg (fun value : ℂ => scalar * value)
        (indicator_congr_decision (row = outputRight) _ _))
    (PreparedBankGroupKernel.preparedBank_eq_iff_group (E := E)
      (radixUnit p fieldTail.succ odd) (ResidualReference p.size m Reference)
      pointLeft pointRight refLeft refRight)

/-- At the original full schedule this is exactly the original full group-oracle output kernel. -/
lemma sourceWord_reset_gram_idealGroup (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (fieldTail : Nat) (odd : Odd p) (Reference : Register)
    (path : Fin (2 * orderWidth problem) → Branch p.size (orderWidth problem))
    (original final : Store (Recovery.Layout.terminal p.size (orderWidth problem)))
    (valid : traceValid p.size (orderWidth problem) (2 * orderWidth problem) id path original final)
    (left right : Bits (orderWidth problem) × Bits (orderWidth problem))
    (refLeft refRight : (ResidualReference p.size (orderWidth problem) Reference).Index)
    (leftGood : ExceptionalOffsetAveraging.Admissible (2 * orderWidth problem)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem))
      (fun index => (points index).toGroupPoint) seed.toGroupPoint
      (SourceControls.sourceValues (orderWidth problem) left))
    (rightGood : ExceptionalOffsetAveraging.Admissible (2 * orderWidth problem)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem))
      (fun index => (points index).toGroupPoint) seed.toGroupPoint
      (SourceControls.sourceValues (orderWidth problem) right)) :
    ((Recovery.Conversion.CoherentBankFamily.sourceWord (environment := environment) E points
        (radixUnit p fieldTail.succ odd) Reference path left).conjTranspose *
      Recovery.Conversion.CoherentBankFamily.sourceWord (environment := environment) E points
        (radixUnit p fieldTail.succ odd) Reference path right)
      (Recovery.Initialization.resetArithmeticLabel E fieldTail seed, (0, refLeft))
      (Recovery.Initialization.resetArithmeticLabel E fieldTail seed, (0, refRight)) =
      (star ((WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) ^
        (2 * orderWidth problem)) *
        (WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) ^
          (2 * orderWidth problem)) *
      (if ECDLP.Measured.idealGroupOutput problem seed
            (SourceControls.sourceValues (orderWidth problem) left) =
          ECDLP.Measured.idealGroupOutput problem seed
            (SourceControls.sourceValues (orderWidth problem) right) ∧ refLeft = refRight
        then 1 else 0) := by
  have leftEndpoint := OriginalGroupEndpoint.affinePath_eq_idealGroupOutput E problem points
    seed addends (SourceControls.sourceValues (orderWidth problem) left) leftGood
  have rightEndpoint := OriginalGroupEndpoint.affinePath_eq_idealGroupOutput E problem points
    seed addends (SourceControls.sourceValues (orderWidth problem) right) rightGood
  change (ScalarMultiplication.AffineTrajectory.path E points
    (SourceControls.controls (orderWidth problem) left)
    (List.finRange (2 * orderWidth problem)) seed).toGroupPoint = _ at leftEndpoint
  change (ScalarMultiplication.AffineTrajectory.path E points
    (SourceControls.controls (orderWidth problem) right)
    (List.finRange (2 * orderWidth problem)) seed).toGroupPoint = _ at rightEndpoint
  have gram := sourceWord_reset_gram (environment := environment) E points fieldTail odd Reference
    path original final valid
    left right seed refLeft refRight leftGood rightGood
  rw [leftEndpoint, rightEndpoint] at gram
  exact gram

end

end ActualGoodKernel
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
