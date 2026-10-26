/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Sequence.Cons
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Sequence.Terminal
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Completions.Chronological
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Sequence.Empty
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Arithmetic
import all Mathlib.Data.Nat.Init

/-!
# Backward equality for the complete actual coherent suffix

The induction keeps the original event, source amplitudes and
Reference vector. It applies the actual next-suffix equality at each full
returned record, partitions Fourier completions for each fixed arithmetic
outcome, and only then normalizes the real arithmetic outcome family.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window.Source
open scoped BigOperators

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

attribute [local irreducible] branchGood prefixAffine
  Driver.namedDriverInstrument Sampling.Locality.namedMeasuredMiddleInstrument

private def nextSuffixEntry (parameters : Sampling.Parameters ctx)
    (index : Sampling.WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type}
    (original : Store ctx × (services.HiddenState × History)) :=
  let point := Driver.namedDriverInstrument (services := services)
    (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
  let : Fintype point.1 := point.2.1
  let reset := Sampling.Reset.instrument parameters index environment
  let middle := Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment
  let zero := Sampling.Reset.zeroOutcome (index.lowerWidth + 1) (parameters.wire index)
  fun (pointOutcome : point.1) (outcome : Bits (index.lowerWidth + 1)) =>
    sourceFullRetainedRecord (services := services) middle.record
      (Instrument.retainedRecord (services := services) reset.record original zero)
      (pointOutcome, outcome)

private lemma nextSuffixEntry_store (parameters : Sampling.Parameters ctx)
    (index : Sampling.WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type}
    (original : Store ctx × (services.HiddenState × History)) :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ (pointOutcome : point.1) (outcome : Bits (index.lowerWidth + 1)),
      (nextSuffixEntry parameters index environment original pointOutcome outcome).1 =
      ((Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment).record
        ((parameters.resetParameters.zeroRunRecord (services := services)
          (index.lowerWidth + 1) (parameters.wire index) original.1).1, original.2.1)
        (pointOutcome, outcome)).1.1 := by
  dsimp only
  intro pointOutcome outcome
  dsimp only [nextSuffixEntry]
  apply retained_middle_store
  exact congrArg Prod.fst
    (Sampling.Reset.runInstrument_zero_record parameters.resetParameters environment
      (index.lowerWidth + 1) (parameters.wire index) original.1)

private lemma nextSuffixEntry_prepared (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (index : Sampling.WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type}
    (original : Store ctx × (services.HiddenState × History))
    (prepared : Prepared parameters I original.1) :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ (pointOutcome : point.1) (outcome : Bits (index.lowerWidth + 1)),
      Prepared parameters I
        (nextSuffixEntry parameters index environment original pointOutcome outcome).1 := by
  dsimp only
  intro pointOutcome outcome
  rw [nextSuffixEntry_store]
  exact prepared_named_middle parameters I index environment
    ((parameters.resetParameters.zeroRunRecord (services := services)
      (index.lowerWidth + 1) (parameters.wire index) original.1).1, original.2.1)
    (pointOutcome, outcome) (prepared_reset_zero parameters I index original.1 prepared)

private def chronologicalWeight (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (processed : Nat) (within : processed ≤ 34)
    (store : Store ctx) (amplitude : GoodBranch I → ℂ)
    {Reference : Register} (reference : HilbertVector Reference)
    (event : Sampling.SourceRegister.Index → Bool) : ℝ :=
  completionWeight parameters I (firstCount processed) (secondCount processed)
    (firstCount_le processed) (secondCount_le processed within) store amplitude reference event

private def NextSuffixPartitionStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (position : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type}
    (original : Store ctx × (services.HiddenState × History))
    (amplitude : GoodBranch I → ℂ) {Reference : Register} (reference : HilbertVector Reference)
    (event : Sampling.SourceRegister.Index → Bool),
    let index := Sampling.chronologicalIndex position
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ pointOutcome : point.1,
      (∑ outcome : Bits (index.lowerWidth + 1),
        chronologicalWeight parameters I (position.val + 1) (Nat.succ_le_of_lt position.isLt)
          (nextSuffixEntry parameters index environment original pointOutcome outcome).1
          amplitude reference event) =
      chronologicalWeight parameters I position.val position.isLt.le
        original.1 amplitude reference event

private lemma nextSuffix_partition : NextSuffixPartitionStatement := by
  intro ctx services parameters I position environment History original amplitude
    Reference reference event
  dsimp only
  intro pointOutcome
  let index := Sampling.chronologicalIndex position
  let zeroStore := (parameters.resetParameters.zeroRunRecord (services := services)
    (index.lowerWidth + 1) (parameters.wire index) original.1).1
  have moved := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun (outcome : Bits (index.lowerWidth + 1)) _ =>
      congrArg (fun store : Store ctx =>
        chronologicalWeight parameters I (position.val + 1)
          (Nat.succ_le_of_lt position.isLt) store amplitude reference event)
        (nextSuffixEntry_store parameters index environment original pointOutcome outcome))
  refine moved.trans ?_
  exact (chronologicalCompletion_middle parameters I position environment zeroStore
    original.2.1 amplitude reference event pointOutcome).trans
    (completionWeight_reset_zero (services := services) parameters I index
      (firstCount position.val) (secondCount position.val) (firstCount_le position.val)
      (secondCount_le position.val position.isLt.le) original.1 amplitude reference event)

private def WeightedPartitionStatement : Prop :=
  ∀ {Point Outcome Scalar : Type}
    [Fintype Point] [Fintype Outcome] [Semiring Scalar]
    (first next : Point → Outcome → Scalar) (weight before : Scalar)
    (_agreed : ∀ point outcome, first point outcome = next point outcome)
    (_partition : ∀ point, (∑ outcome, next point outcome) = before)
    (_normalized : (∑ _point : Point, weight) = 1),
    (∑ point, ∑ outcome, weight * first point outcome) = before

private lemma weighted_partition : WeightedPartitionStatement := by
  intro Point Outcome Scalar _ _ _ first next weight before agreed partition normalized
  have same : first = next := funext (fun point => funext (agreed point))
  subst first
  calc
    (∑ point : Point, ∑ outcome : Outcome, weight * next point outcome) =
        ∑ point : Point, weight * (∑ outcome : Outcome, next point outcome) :=
      Finset.sum_congr rfl (fun point _ =>
        (Finset.mul_sum Finset.univ (next point) weight).symm)
    _ = ∑ _point : Point, weight * before :=
      congrArg (fun values : Point → Scalar => ∑ point : Point, weight * values point)
        (funext partition)
    _ = (∑ _point : Point, weight) * before :=
      (Finset.sum_mul Finset.univ (fun _point : Point => weight) before).symm
    _ = before :=
      (congrArg (fun value : Scalar => value * before) normalized).trans (one_mul before)

private def SuffixValueCompletionWithBranchStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (_sameSpec : parameters.modulus = (actualCurveSpec I).field)
    (scratch : Sampling.Storage.Frame ctx 256 256)
    (_assigned : ∀ position : Fin 34,
      Driver.driverScratchReferences
        (parameters.pointParameters (Sampling.chronologicalIndex position)) scratch
        (fun bit => Fin.castLE (Sampling.chronologicalIndex position).lowCapacity bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (_branch : GoodBranch I) (amplitude : GoodBranch I → ℂ)
    {Reference : Register} (reference : HilbertVector Reference)
    (event : Sampling.SourceRegister.Index → Bool) (processed : Nat)
    (within : processed ≤ 34),
    ∀ {History : Type} [Finite History]
      (original : Store ctx × (services.HiddenState × History)),
      Prepared parameters I original.1 →
      suffixValue parameters I environment processed within original amplitude reference event =
        completionWeight parameters I (firstCount processed) (secondCount processed)
          (firstCount_le processed) (secondCount_le processed within)
          original.1 amplitude reference event

private lemma suffixValue_eq_completionWeight_with_branch :
    SuffixValueCompletionWithBranchStatement := by
  intro ctx services parameters I sameSpec scratch assigned environment branch amplitude
    Reference reference event processed within
  classical
  induction within using Nat.decreasingInduction with
  | self =>
      intro History _ original _prepared
      simpa only [firstCount_final, secondCount_final] using
        suffixValue_terminal parameters I environment original amplitude reference event
  | of_succ processed remaining ih =>
      intro History _ original prepared
      let position : Fin 34 := ⟨processed, remaining⟩
      let index := Sampling.chronologicalIndex position
      let point := Driver.namedDriverInstrument (services := services)
        (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
      let : Fintype point.1 := point.2.1
      let zeroStore := (parameters.resetParameters.zeroRunRecord (services := services)
        (index.lowerWidth + 1) (parameters.wire index) original.1).1
      let NextHistory :=
        ((History × (parameters.reset (services := services) index).Path) ×
          (parameters.measuredMiddle (services := services) index).Path)
      let nextEntry := nextSuffixEntry parameters index environment original
      let weight : ℝ := ‖NormalizedVector.invSqrt2 ^ 2048‖ ^ 2
      let beforeWeight : ℝ := chronologicalWeight parameters I processed
        (Nat.le_of_lt remaining) original.1 amplitude reference event
      let nextWeight (pointOutcome : point.1) (outcome : Bits (index.lowerWidth + 1)) : ℝ :=
        chronologicalWeight parameters I (processed + 1) (Nat.succ_le_of_lt remaining)
          (nextEntry pointOutcome outcome).1 amplitude reference event
      have resetPrepared : Prepared parameters I zeroStore :=
        prepared_reset_zero parameters I index original.1 prepared
      have afterPrepared :=
        nextSuffixEntry_prepared parameters I index environment original prepared
      have nextEquality (pointOutcome : point.1) (outcome : Bits (index.lowerWidth + 1)) :=
        ih (History := NextHistory) (nextEntry pointOutcome outcome)
          (afterPrepared pointOutcome outcome)
      have partition := nextSuffix_partition parameters I position environment
        original amplitude reference event
      have normalized : (∑ _pointOutcome : point.1, weight) = 1 :=
        point_scalar_sum_norm_sq parameters I sameSpec scratch branch.val branch.property
          position (assigned position) environment zeroStore original.2.1
          (Prepared.driverInputValues parameters I zeroStore resetPrepared position)
      have step := suffixValue_cons parameters I sameSpec scratch position (assigned position)
        environment original prepared amplitude reference event
      refine step.trans ?_
      apply weighted_partition (Point := point.1) (Outcome := Bits (index.lowerWidth + 1))
        _ nextWeight weight beforeWeight
      · exact nextEquality
      · exact partition
      · exact normalized

/-- Every actual suffix has exactly its original complete-output coherent weight. -/
lemma suffixValue_eq_completionWeight (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (sameSpec : parameters.modulus = (actualCurveSpec I).field)
    (scratch : Sampling.Storage.Frame ctx 256 256)
    (assigned : ∀ position : Fin 34,
      Driver.driverScratchReferences
        (parameters.pointParameters (Sampling.chronologicalIndex position)) scratch
        (fun bit => Fin.castLE (Sampling.chronologicalIndex position).lowCapacity bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (processed : Nat) (within : processed ≤ 34)
    {Reference : Register} {History : Type} [Finite History]
    (original : Store ctx × (services.HiddenState × History))
    (prepared : Prepared parameters I original.1) (amplitude : GoodBranch I → ℂ)
    (reference : HilbertVector Reference) (event : Sampling.SourceRegister.Index → Bool) :
    suffixValue parameters I environment processed within original amplitude reference event =
      completionWeight parameters I (firstCount processed) (secondCount processed)
        (firstCount_le processed) (secondCount_le processed within)
        original.1 amplitude reference event := by
  classical
  rcases isEmpty_or_nonempty (GoodBranch I) with empty | inhabited
  · let : IsEmpty (GoodBranch I) := empty
    rw [suffixValue_empty, completionWeight_empty]
  · obtain ⟨branch⟩ := inhabited
    exact suffixValue_eq_completionWeight_with_branch parameters I sameSpec scratch assigned
      environment branch amplitude reference event processed within original prepared

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
