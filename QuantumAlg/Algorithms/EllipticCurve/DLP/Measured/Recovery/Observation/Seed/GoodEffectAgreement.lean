/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Seed.EventCoordinates
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.Good.EffectAgreement
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.GoodKernelAgreement

/-!
# The actual seed event agrees on the original coherent good component

The compressed actual event retains the original two exponent labels and the
external Reference. The reset bank and its residual frame are fixed internally,
so the residual Reference delta is exactly the original external delta. Every
original good off-diagonal entry agrees with the unchanged ideal observable.
The resulting pure-component lower bound uses the original exceptional mass.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace SeedGoodEffectAgreement

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg.Execution (Store)
open _root_.QuantumAlg.QuantumFourierTransform.Semiclassical (binaryEquiv)
open _root_.QuantumAlg.FiniteCyclicDLP (KnownOrderProblem orderWidth fourierModulus)
open _root_.QuantumAlg.FiniteCyclicDLP.Canonical.Probability (SecretInput)
open GenericPointAddition.InPlace.Semantics (radixUnit)
open Recovery.Stage.PointCoordinates (ResidualReference)
open ECDLP.Measured (idealBranchRegister idealBranchEffect)
open ECDLP.Measured (preparedAdmissibleBranches preparedExceptionalMass)
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

omit [Fact p.Prime] in
/-- The internally fixed residual frame preserves precisely the full external Reference delta. -/
private lemma ideal_residual_matrix (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) (Reference : Register)
    (left right : ((idealBranchRegister problem).prod Reference).Index) :
    (idealBranchEffect problem seed event
      (ResidualReference p.size (orderWidth problem) Reference)).matrix
        (left.1, SeedEventCoordinates.residualReference (p := p) (orderWidth problem) Reference
          left.2)
        (right.1, SeedEventCoordinates.residualReference (p := p) (orderWidth problem) Reference
          right.2) =
      (idealBranchEffect problem seed event Reference).matrix left right := by
  rw [IdealFrequencyKernel.idealBranchEffect_matrix_frequency,
    IdealFrequencyKernel.idealBranchEffect_matrix_frequency]
  simp only [SeedEventCoordinates.residualReference_eq_iff]

set_option maxHeartbeats 400000 in
-- The complete good-source matrix calculation needs a finite local elaboration budget.
/-- The compressed actual event has the original ideal entry for every original good source pair. -/
lemma sourceEffect_good_matrix (problem : KnownOrderProblem E.GroupPoint)
    (fieldTail : Nat) (seed : AffinePoint E)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (odd : Odd p) (Reference : Register)
    (original : Store (Recovery.Layout.terminal p.size (orderWidth problem)))
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (left right : ((idealBranchRegister problem).prod Reference).Index)
    (leftGood : left.1 ∈ preparedAdmissibleBranches problem points seed)
    (rightGood : right.1 ∈ preparedAdmissibleBranches problem points seed) :
    (SeedEventCoordinates.sourceEffect (environment := environment) E problem fieldTail seed points
      (radixUnit p fieldTail.succ odd) Reference original
      (fun final => event
        (ActualFrequencyEvent.resultBits p.size (orderWidth problem) final) = true)).matrix
      left right = (idealBranchEffect problem seed event Reference).matrix left right := by
  classical
  let admissionDecision : DecidablePred
      (ExceptionalOffsetAveraging.Admissible (2 * orderWidth problem)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem))
      (fun index => (points index).toGroupPoint) seed.toGroupPoint) :=
    fun _ => Classical.propDecidable _
  dsimp only [preparedAdmissibleBranches] at leftGood rightGood
  have leftAdmissible := ((@Finset.mem_filter _ _ admissionDecision _ _).mp leftGood).2
  have rightAdmissible := ((@Finset.mem_filter _ _ admissionDecision _ _).mp rightGood).2
  let leftBits := ((binaryEquiv (orderWidth problem)).symm left.1.1,
    (binaryEquiv (orderWidth problem)).symm left.1.2)
  let rightBits := ((binaryEquiv (orderWidth problem)).symm right.1.1,
    (binaryEquiv (orderWidth problem)).symm right.1.2)
  have agreement := ActualGoodEffectAgreement.eventEffect_good_reset_matrix (environment :=
    environment) E problem points
    seed addends fieldTail odd Reference original leftBits rightBits
    (SeedEventCoordinates.residualReference (p := p) (orderWidth problem) Reference left.2)
    (SeedEventCoordinates.residualReference (p := p) (orderWidth problem) Reference right.2)
    (by
      dsimp only [leftBits, SourceControls.sourceValues]
      simp only [Equiv.apply_symm_apply]
      exact leftAdmissible)
    (by
      dsimp only [rightBits, SourceControls.sourceValues]
      simp only [Equiv.apply_symm_apply]
      exact rightAdmissible) event
  simp only [SourceControls.sourceValues, leftBits, rightBits,
    Equiv.apply_symm_apply] at agreement
  change (ActualSelectedEffect.eventEffect (environment := environment) E points
    (radixUnit p fieldTail.succ odd) Reference original
    (fun final => event (ActualFrequencyEvent.resultBits p.size (orderWidth problem) final) =
      true)).matrix
      (SeedEventCoordinates.sourceEmbedding E problem fieldTail seed Reference left)
      (SeedEventCoordinates.sourceEmbedding E problem fieldTail seed Reference right) = _
  rw [SeedEventCoordinates.sourceEmbedding, SeedEventCoordinates.sourceEmbedding,
    SeedEventCoordinates.seedBank_apply, SeedEventCoordinates.seedBank_apply]
  exact agreement.trans (ideal_residual_matrix E problem seed event Reference left right)

/-- The same actual pure Reference component retains the original success floor and loss. -/
lemma referenceComponent_selected_lower (problem : KnownOrderProblem E.GroupPoint)
    (fieldTail : Nat) (seed : AffinePoint E)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (odd : Odd p) (input : SecretInput problem) {Reference : Register}
    (original : Store (Recovery.Layout.terminal p.size (orderWidth problem)))
    (reference : NormalizedVector Reference) :
    (problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed) ≤
      ActualReferenceEvent.referenceComponentWeight (environment := environment) E fieldTail seed
        problem.order points
        (radixUnit p fieldTail.succ odd) original
        (fun final => ECDLP.Measured.selectedExponentEvent problem input
          (ActualFrequencyEvent.resultBits p.size (orderWidth problem) final) = true)
        reference := by
  rw [← SeedEventCoordinates.sourceEffect_weight E problem fieldTail seed points
    (radixUnit p fieldTail.succ odd) original _ reference]
  apply GoodKernelAgreement.selected_effect_lower_of_good_matrix problem points seed input
    reference
  intro left right leftGood rightGood
  exact sourceEffect_good_matrix E problem fieldTail seed points addends odd Reference original
    (ECDLP.Measured.selectedExponentEvent problem input) left right leftGood rightGood

end

end SeedGoodEffectAgreement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
