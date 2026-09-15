/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Comparison.Prepared
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Target.Coherent
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Target.Group
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Target.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Readout.Kernel
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Measurement.Observation
import all QuantumAlg.Core.Base.Gate.Effect.Columns

/-!
# Complete coherent agreement with the original group oracle

The actual scalar output and the original full-group target have identical
observable columns on every original good branch and every reference label.
Their complete coherent weights agree, including all complex cross terms.
Actual initialization, original inverse Fourier readout and terminal cell
allocation retain this equality. The original good-input agreement is thus
derived without an additional support, basis-only, or normalization premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open ScalarMultiplication.MeasuredPlacement.Encoding
open GenericPointAddition.InPlace FiniteCyclicDLP ConcreteCircuitAccess

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private def goodReferenceBranches (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (Reference : Register) :
    Finset ((Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem)) × Reference.Index) :=
  (preparedAdmissibleBranches problem points seed).product Finset.univ

private def branchReferenceLabel (problem : KnownOrderProblem E.GroupPoint)
    (Reference : Register) :
    (Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem)) × Reference.Index →
      ((idealBranchRegister problem).prod Reference).Index := fun label => label

/-- The original good branch vector keeps every reference amplitude without renormalization. -/
def idealGoodBranchVector (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    HilbertVector ((idealBranchRegister problem).prod Reference) :=
  ∑ label ∈ goodReferenceBranches problem points seed Reference,
    (preparedBranchAmplitude problem label.1 * reference label.2) •
      (NormalizedVector.ket (branchReferenceLabel problem Reference label)).vec

variable [Fact p.Prime]

/-- The physical good vector is exactly the original good branch vector at its actual seed. -/
theorem idealGoodBranchVector_montgomery (problem : KnownOrderProblem E.GroupPoint)
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    Effect.extensionVector
      (idealMontgomeryEmbedding problem fieldTail sameWidth fits seed Reference)
      (idealGoodBranchVector problem points seed reference) =
        preparedGoodVector problem fieldTail sameWidth fits points seed reference := by
  have sumExpansion := Finset.sum_product (preparedAdmissibleBranches problem points seed)
    (Finset.univ : Finset Reference.Index) (fun label =>
      (preparedBranchAmplitude problem label.1 * reference label.2) •
        (NormalizedVector.ket (branchReferenceLabel problem Reference label)).vec)
  refine (congrArg (Effect.extensionVector
    (idealMontgomeryEmbedding problem fieldTail sameWidth fits seed Reference))
      sumExpansion).trans ?_
  rw [extensionVector_sum]
  simp only [extensionVector_sum, extensionVector_smul, extensionVector_ket]
  rw [preparedGoodVector, referenceFrame_sum_ket]
  rfl

/-- The original good branch vector has exactly the norm of its actual physical image. -/
theorem idealGoodBranchVector_norm (problem : KnownOrderProblem E.GroupPoint)
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    ‖idealGoodBranchVector problem points seed reference‖ =
      ‖preparedGoodVector problem fieldTail sameWidth fits points seed reference‖ := by
  rw [← Effect.norm_extensionVector
    (idealMontgomeryEmbedding problem fieldTail sameWidth fits seed Reference)
    (idealMontgomeryEmbedding_injective problem fieldTail sameWidth fits seed Reference),
    idealGoodBranchVector_montgomery]

private def goodOutputLabel (problem : KnownOrderProblem E.GroupPoint)
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (Reference : Register) :
    (Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem)) × Reference.Index →
      ((after p.size (2 * orderWidth problem)).register.prod Reference).Index :=
  fun label => initializedOutputEmbedding p (2 * orderWidth problem) Reference
    (pairedMontgomeryInput fieldTail (orderWidth problem) sameWidth fits
      (ScalarMultiplication.AffineTrajectory.path E points
        (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) label.1)
        (List.finRange (2 * orderWidth problem)) seed) label.1, label.2)

private theorem goodOutputLabel_sum (problem : KnownOrderProblem E.GroupPoint)
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    (∑ label ∈ goodReferenceBranches problem points seed Reference,
      (preparedBranchAmplitude problem label.1 * reference label.2) •
        (NormalizedVector.ket
          (goodOutputLabel problem fieldTail sameWidth fits points seed Reference label)).vec) =
      convertedGoodVector problem fieldTail sameWidth fits points seed reference := by
  exact Finset.sum_product (preparedAdmissibleBranches problem points seed)
    (Finset.univ : Finset Reference.Index) (fun label =>
      (preparedBranchAmplitude problem label.1 * reference label.2) •
        (NormalizedVector.ket
          (goodOutputLabel problem fieldTail sameWidth fits points seed Reference label)).vec)

private theorem goodOutputLabel_effect_column (problem : KnownOrderProblem E.GroupPoint)
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (odd : Odd p) (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) (Reference : Register)
    (left right : (Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem)) × Reference.Index)
    (leftGood : left ∈ goodReferenceBranches problem points seed Reference)
    (rightGood : right ∈ goodReferenceBranches problem points seed Reference) :
    (afterExponentReadoutEffect p problem event Reference).matrix
        (goodOutputLabel problem fieldTail sameWidth fits points seed Reference left)
        (goodOutputLabel problem fieldTail sameWidth fits points seed Reference right) =
      (idealBranchEffect problem seed event Reference).matrix
        (branchReferenceLabel problem Reference left)
        (branchReferenceLabel problem Reference right) := by
  have leftBranch := (Finset.mem_product.mp leftGood).1
  have rightBranch := (Finset.mem_product.mp rightGood).1
  let path := fun branch => ScalarMultiplication.AffineTrajectory.path E points
    (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) branch)
    (List.finRange (2 * orderWidth problem)) seed
  have groups : (path left.1).toGroupPoint = (path right.1).toGroupPoint ↔
      problem.toSourceScope.oracleMultiplier left.1.1.val left.1.2.val =
        problem.toSourceScope.oracleMultiplier right.1.1.val right.1.2.val := by
    rw [preparedGoodPath_groupOutput problem points seed addends left.1 leftBranch,
      preparedGoodPath_groupOutput problem points seed addends right.1 rightBranch]
    exact mul_left_cancel_iff
  have actual := afterExponentReadoutEffect_initialized_matrix p problem event Reference
    left.1 right.1
    (montgomeryCoordinates fieldTail sameWidth fits (path left.1)).1
    (montgomeryCoordinates fieldTail sameWidth fits (path left.1)).2
    (montgomeryCoordinates fieldTail sameWidth fits (path right.1)).1
    (montgomeryCoordinates fieldTail sameWidth fits (path right.1)).2 left.2 right.2
  have sameCoordinates :=
    (montgomeryCoordinates_eq_iff_group fieldTail sameWidth fits odd
      (path left.1) (path right.1)).trans groups
  unfold goodOutputLabel
  rw [pairedMontgomeryInput_coordinates, pairedMontgomeryInput_coordinates]
  refine actual.trans ?_
  rw [idealBranchEffect_matrix]
  simp only [Prod.mk.eta, branchReferenceLabel, sameCoordinates]
  by_cases multiplierSame :
      problem.toSourceScope.oracleMultiplier left.1.1.val left.1.2.val =
        problem.toSourceScope.oracleMultiplier right.1.1.val right.1.2.val
  · by_cases referenceSame : left.2 = right.2 <;> simp [multiplierSame, referenceSame]
  · simp [multiplierSame]

/-- Actual scalar output and original group labels have the same complete good observable weight. -/
theorem convertedGoodVector_idealBranch_weight (problem : KnownOrderProblem E.GroupPoint)
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (odd : Odd p) (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    {Reference : Register} (reference : NormalizedVector Reference) :
    (afterExponentReadoutEffect p problem event Reference).weight
        (DensityOperator.ofSubnormalizedVector
          (convertedGoodVector problem fieldTail sameWidth fits points seed reference)
          (convertedGoodVector_norm_le_one problem fieldTail sameWidth fits odd
            points seed reference)) =
      (idealBranchEffect problem seed event Reference).weight
        (DensityOperator.ofSubnormalizedVector (idealGoodBranchVector problem points seed reference)
          (by
            rw [idealGoodBranchVector_norm problem fieldTail sameWidth fits]
            exact preparedGoodVector_norm_le_one problem fieldTail sameWidth fits
              points seed reference)) := by
  have equality := Effect.weight_eq_of_coherent_columns
    (goodReferenceBranches problem points seed Reference)
    (fun label => preparedBranchAmplitude problem label.1 * reference label.2)
    (goodOutputLabel problem fieldTail sameWidth fits points seed Reference)
    (branchReferenceLabel problem Reference)
    (afterExponentReadoutEffect p problem event Reference)
    (idealBranchEffect problem seed event Reference)
    (by
      rw [goodOutputLabel_sum]
      exact convertedGoodVector_norm_le_one problem fieldTail sameWidth fits odd
        points seed reference)
    (by
      change ‖idealGoodBranchVector problem points seed reference‖ ≤ 1
      rw [idealGoodBranchVector_norm problem fieldTail sameWidth fits]
      exact preparedGoodVector_norm_le_one problem fieldTail sameWidth fits points seed reference)
    (fun left leftGood right rightGood => goodOutputLabel_effect_column problem fieldTail
      sameWidth fits odd points seed addends event Reference left right leftGood rightGood)
  rw [Effect.weight_ofSubnormalizedVector, Effect.weight_ofSubnormalizedVector] at equality ⊢
  rw [goodOutputLabel_sum] at equality
  exact equality

/-- The original physical good density has its exact ideal branch observable weight. -/
theorem idealPreparedEffect_good_weight (problem : KnownOrderProblem E.GroupPoint)
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    {Reference : Register} (reference : NormalizedVector Reference) :
    (idealPreparedEffect problem fieldTail sameWidth fits seed event Reference).weight
        (DensityOperator.ofSubnormalizedVector
          (preparedGoodVector problem fieldTail sameWidth fits points seed reference)
          (preparedGoodVector_norm_le_one problem fieldTail sameWidth fits points seed reference)) =
      (idealBranchEffect problem seed event Reference).weight
        (DensityOperator.ofSubnormalizedVector (idealGoodBranchVector problem points seed reference)
          (by
            rw [idealGoodBranchVector_norm problem fieldTail sameWidth fits]
            exact preparedGoodVector_norm_le_one problem fieldTail sameWidth fits
              points seed reference)) := by
  have equality := idealPreparedEffect_weight problem fieldTail sameWidth fits seed event Reference
    (idealGoodBranchVector problem points seed reference)
    (by
      rw [idealGoodBranchVector_norm problem fieldTail sameWidth fits]
      exact preparedGoodVector_norm_le_one problem fieldTail sameWidth fits points seed reference)
  rw [Effect.weight_ofSubnormalizedVector, Effect.weight_ofSubnormalizedVector] at equality ⊢
  rw [idealGoodBranchVector_montgomery] at equality
  exact equality

/-- Actual original-good input execution agrees with the original ideal observable completely. -/
theorem idealInputEffect_goodAgreement (problem : KnownOrderProblem E.GroupPoint)
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (odd : Odd p) (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    {Reference : Register} (reference : NormalizedVector Reference) :
    (QubitReadouts.eventEffect (exponentMeasurementWires p (orderWidth problem))
      event Reference).weight
        (exponentRunDensity E fieldTail odd problem points Reference
          (DensityOperator.ofSubnormalizedVector
            (goodInputVector problem fieldTail sameWidth fits points seed reference)
            (goodInputVector_norm_le_one problem fieldTail sameWidth fits
              points seed reference))) =
      (idealInputEffect problem fieldTail sameWidth fits seed event Reference).weight
        (DensityOperator.ofSubnormalizedVector
          (goodInputVector problem fieldTail sameWidth fits points seed reference)
          (goodInputVector_norm_le_one problem fieldTail sameWidth fits
            points seed reference)) := by
  rw [exponentRunDensity_eventWeight, preMeasurementDensity,
    goodInputVector_preparedDensity, convertedResultDensity_preparedGood,
    ← Effect.weight_pullbackUnitary]
  change (afterExponentReadoutEffect p problem event Reference).weight _ = _
  rw [convertedGoodVector_idealBranch_weight problem fieldTail sameWidth fits odd
    points seed addends event reference,
    idealInputEffect_weight, goodInputVector_preparedDensity,
    idealPreparedEffect_good_weight]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
