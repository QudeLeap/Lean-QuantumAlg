/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Fourier.Slice
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Terminal

/-!
# Complete physical-output weights equal the original coherent Fourier slices

The sum is reindexed over all original frequencies by one explicit equivalence.
Every group-output collision and Reference cross term remains inside its slice
norm. Arbitrary raw Reference and zero mass need no division or normalization.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass ECDLP.Measured
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open scoped BigOperators

attribute [local irreducible] branchGood prefixAffine

attribute [local irreducible] sourceBranch

private def completionWeightReadoutStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (store : Store ctx) (amplitude : GoodBranch I → ℂ)
    {Reference : Register} (reference : HilbertVector Reference)
    (event : (Fin (2 * Cascade.exponentWidth I) → Bool) → Bool),
    completionWeight parameters I 0 0 (Nat.zero_le 260) (Nat.zero_le 260) store
        amplitude reference
        (fun complete => event (ExceptionalOffsetAveraging.pairedBigEndianSelected
          (Cascade.exponentWidth I) (decodedFrequency I complete))) =
      ∑ frequency : (idealBranchRegister
          (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))).Index,
        if event (ExceptionalOffsetAveraging.pairedBigEndianSelected
            (Cascade.exponentWidth I) frequency) = true then
          ‖idealReadoutSlice (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
            (FullRange.chronologicalFixedSeed I) Reference
            ((idealReadoutOperator (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
                (FullRange.chronologicalFixedSeed I) Reference).applyVec
              (Effect.extensionVector
                (idealOracleEmbedding (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
                  (FullRange.chronologicalFixedSeed I) Reference)
                (∑ branch : GoodBranch I, ∑ ref : Reference.Index,
                  (amplitude branch * reference ref) •
                    (NormalizedVector.ket
                      (R := (idealBranchRegister
                        (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))).prod Reference)
                      (branch.val, ref)).vec))) frequency‖ ^ 2 else 0

private lemma completionWeightReadoutStatement_proof : completionWeightReadoutStatement := by
  intro ctx parameters I store amplitude Reference reference event
  let problem := ECDLP.Canonical.problem (Cascade.ecdlpInstance I)
  let seed := FullRange.chronologicalFixedSeed I
  let source : HilbertVector ((idealBranchRegister problem).prod Reference) :=
    ∑ branch : GoodBranch I, ∑ ref : Reference.Index,
      (amplitude branch * reference ref) •
        (NormalizedVector.ket (R := (idealBranchRegister problem).prod Reference)
          (branch.val, ref)).vec
  let slice : (idealBranchRegister problem).Index →
      HilbertVector ((idealGroupRegister problem seed).prod Reference) := fun frequency =>
    idealReadoutSlice problem seed Reference
      ((idealReadoutOperator problem seed Reference).applyVec
        (Effect.extensionVector (idealOracleEmbedding problem seed Reference) source)) frequency
  let weight := fun frequency : (idealBranchRegister problem).Index =>
    if event (ExceptionalOffsetAveraging.pairedBigEndianSelected
      (Cascade.exponentWidth I) frequency) = true then ‖slice frequency‖ ^ 2 else 0
  have terminal (complete : Sampling.SourceRegister.Index) :
      ‖coherentPrefix parameters I 34 (Nat.le_refl 34) 520
        (completedAmplitude I complete amplitude) (Reference := Reference) reference‖ =
      ‖slice (decodedFrequency I complete)‖ := by
    have physical := coherentPrefix_terminal_norm (ctx := ctx) parameters I
      (completedAmplitude I complete amplitude) (Reference := Reference) reference
    have coherent := original_coherent_slice I amplitude (Reference := Reference) reference complete
    have same := congrArg
      (fun vector : HilbertVector ((idealGroupRegister problem seed).prod Reference) => ‖vector‖)
      coherent
    exact physical.trans same.symm
  refine (completionWeight_initial parameters I store amplitude (Reference := Reference)
    reference (fun complete => event (ExceptionalOffsetAveraging.pairedBigEndianSelected
      (Cascade.exponentWidth I) (decodedFrequency I complete)))).trans ?_
  trans ∑ complete : Sampling.SourceRegister.Index, weight (decodedFrequency I complete)
  · apply Finset.sum_congr rfl
    intro complete _
    exact congrArg (fun value : ℝ =>
      if event (ExceptionalOffsetAveraging.pairedBigEndianSelected
        (Cascade.exponentWidth I) (decodedFrequency I complete)) = true
      then value ^ 2 else 0) (terminal complete)
  · exact Equiv.sum_comp (decodedFrequency I) weight

/-- The complete raw continuation weight is the exact sum of original coherent Fourier slices. -/
lemma completionWeight_readout_slices {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (store : Store ctx) (amplitude : GoodBranch I → ℂ)
    {Reference : Register} (reference : HilbertVector Reference)
    (event : (Fin (2 * Cascade.exponentWidth I) → Bool) → Bool) :
    completionWeight parameters I 0 0 (Nat.zero_le 260) (Nat.zero_le 260) store
        amplitude reference
        (fun complete => event (ExceptionalOffsetAveraging.pairedBigEndianSelected
          (Cascade.exponentWidth I) (decodedFrequency I complete))) =
      ∑ frequency : (idealBranchRegister
          (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))).Index,
        if event (ExceptionalOffsetAveraging.pairedBigEndianSelected
            (Cascade.exponentWidth I) frequency) = true then
          ‖idealReadoutSlice (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
            (FullRange.chronologicalFixedSeed I) Reference
            ((idealReadoutOperator (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
                (FullRange.chronologicalFixedSeed I) Reference).applyVec
              (Effect.extensionVector
                (idealOracleEmbedding (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
                  (FullRange.chronologicalFixedSeed I) Reference)
                (∑ branch : GoodBranch I, ∑ ref : Reference.Index,
                  (amplitude branch * reference ref) •
                    (NormalizedVector.ket
                      (R := (idealBranchRegister
                        (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))).prod Reference)
                      (branch.val, ref)).vec))) frequency‖ ^ 2 else 0 :=
  completionWeightReadoutStatement_proof (ctx := ctx) parameters I store amplitude
    (Reference := Reference) reference event

/-- The original good component has exactly its unchanged subnormalized branch-effect weight. -/
lemma completionWeight_idealBranchEffect {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (store : Store ctx) {Reference : Register} (reference : NormalizedVector Reference)
    (event : (Fin (2 * Cascade.exponentWidth I) → Bool) → Bool) :
    completionWeight parameters I 0 0 (Nat.zero_le 260) (Nat.zero_le 260) store
        (fun branch => EllipticCurve.FullRange.branchAmplitude
          (Cascade.exponentWidth I) branch.val) reference.vec
        (fun complete => event (ExceptionalOffsetAveraging.pairedBigEndianSelected
          (Cascade.exponentWidth I) (decodedFrequency I complete))) =
      (idealBranchEffect (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
        (FullRange.chronologicalFixedSeed I) event Reference).weight
        (DensityOperator.ofSubnormalizedVector
          (EllipticCurve.FullRange.Geometry.goodVector (Cascade.exponentWidth I) 34
            (FullRange.chronologicalSelected I) (FullRange.chronologicalAddend I)
            (FullRange.chronologicalFixedSeed I).toGroupPoint reference)
          (EllipticCurve.FullRange.Geometry.goodVector_norm_le_one
            (Cascade.exponentWidth I) 34 (FullRange.chronologicalSelected I)
            (FullRange.chronologicalAddend I)
            (FullRange.chronologicalFixedSeed I).toGroupPoint reference)) := by
  refine (completionWeight_readout_slices parameters I store
    (fun branch => EllipticCurve.FullRange.branchAmplitude
      (Cascade.exponentWidth I) branch.val) (Reference := Reference) reference.vec event).trans ?_
  refine (congrArg
    (fun vector : HilbertVector ((idealBranchRegister
        (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))).prod Reference) =>
      ∑ frequency : (idealBranchRegister
          (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))).Index,
        if event (ExceptionalOffsetAveraging.pairedBigEndianSelected
            (Cascade.exponentWidth I) frequency) = true then
          ‖idealReadoutSlice (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
            (FullRange.chronologicalFixedSeed I) Reference
            ((idealReadoutOperator (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
                (FullRange.chronologicalFixedSeed I) Reference).applyVec
              (Effect.extensionVector
                (idealOracleEmbedding (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
                  (FullRange.chronologicalFixedSeed I) Reference) vector)) frequency‖ ^ 2 else 0)
    (original_goodVector_expansion I (Reference := Reference) reference).symm).trans ?_
  exact (idealBranchEffect_weight_slices
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
    (FullRange.chronologicalFixedSeed I) event Reference
    (EllipticCurve.FullRange.Geometry.goodVector (Cascade.exponentWidth I) 34
      (FullRange.chronologicalSelected I) (FullRange.chronologicalAddend I)
      (FullRange.chronologicalFixedSeed I).toGroupPoint reference)
    (EllipticCurve.FullRange.Geometry.goodVector_norm_le_one
      (Cascade.exponentWidth I) 34 (FullRange.chronologicalSelected I)
      (FullRange.chronologicalAddend I)
      (FullRange.chronologicalFixedSeed I).toGroupPoint reference)).symm

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
