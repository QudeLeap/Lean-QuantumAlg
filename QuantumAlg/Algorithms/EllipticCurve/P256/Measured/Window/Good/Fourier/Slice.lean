/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Fourier.Slice
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Fourier.Original
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Fourier.Coordinates

/-!
# The unchanged original good vector has exactly the complete physical-output slice

The original full-range branch amplitudes and the full
Reference remain inside the coherent sum. No source-range preparation formula
or normalization of the good mass is introduced.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open PrimeFieldShortWeierstrass ECDLP.Measured
open scoped BigOperators

attribute [local irreducible] branchGood

/-- Arbitrary original amplitudes and raw Reference keep each complete coherent slice. -/
lemma original_coherent_slice (I : DomainParameters.PublicKeyInstance)
    (amplitude : GoodBranch I → ℂ)
    {Reference : Register} (reference : HilbertVector Reference)
    (complete : Arithmetic.P256.Point.Window.Sampling.SourceRegister.Index) :
    idealReadoutSlice (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
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
                  (branch.val, ref)).vec)))
        (decodedFrequency I complete) =
      ∑ branch : GoodBranch I, ∑ ref : Reference.Index,
        (completedAmplitude I complete amplitude branch * reference ref) •
          (NormalizedVector.ket
            (R := (idealGroupRegister
              (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
              (FullRange.chronologicalFixedSeed I)).prod Reference)
            (idealGroupLabel (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
              (FullRange.chronologicalFixedSeed I) branch.val, ref)).vec := by
  refine (idealReadoutSlice_extension_family
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
    (FullRange.chronologicalFixedSeed I) Reference (Branch := GoodBranch I)
    (fun branch : GoodBranch I => branch.val) amplitude reference
    (decodedFrequency I complete)).trans ?_
  apply Finset.sum_congr rfl
  intro branch _
  apply Finset.sum_congr rfl
  intro ref _
  have rows := exponentReadout_fullRows
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
    (decodedFrequency I complete) branch.val
  have coefficient := (congrArg (fun row : ℂ => amplitude branch * row) rows).trans
    (completedAmplitude_fullRows I complete amplitude branch).symm
  exact congrArg (fun scalar : ℂ => (scalar * reference ref) •
    (NormalizedVector.ket
      (R := (idealGroupRegister
        (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
        (FullRange.chronologicalFixedSeed I)).prod Reference)
      (idealGroupLabel (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
        (FullRange.chronologicalFixedSeed I) branch.val, ref)).vec) coefficient


/-- Every complete output gives exactly the original good vector's coherent Fourier slice. -/
lemma original_goodVector_slice (I : DomainParameters.PublicKeyInstance)
    {Reference : Register} (reference : NormalizedVector Reference)
    (complete : Arithmetic.P256.Point.Window.Sampling.SourceRegister.Index) :
    idealReadoutSlice (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
        (FullRange.chronologicalFixedSeed I) Reference
        ((idealReadoutOperator (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
            (FullRange.chronologicalFixedSeed I) Reference).applyVec
          (Effect.extensionVector
            (idealOracleEmbedding (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
              (FullRange.chronologicalFixedSeed I) Reference)
            (EllipticCurve.FullRange.Geometry.goodVector (Cascade.exponentWidth I) 34
              (FullRange.chronologicalSelected I) (FullRange.chronologicalAddend I)
              (FullRange.chronologicalFixedSeed I).toGroupPoint reference)))
        (decodedFrequency I complete) =
      ∑ branch : GoodBranch I, ∑ ref : Reference.Index,
        (completedAmplitude I complete
            (fun branch => EllipticCurve.FullRange.branchAmplitude
              (Cascade.exponentWidth I) branch.val) branch * reference ref) •
          (NormalizedVector.ket
            (R := (idealGroupRegister
              (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
              (FullRange.chronologicalFixedSeed I)).prod Reference)
            (idealGroupLabel (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
              (FullRange.chronologicalFixedSeed I) branch.val, ref)).vec := by
  rw [original_goodVector_expansion]
  exact original_coherent_slice I
    (fun branch => EllipticCurve.FullRange.branchAmplitude (Cascade.exponentWidth I) branch.val)
    (Reference := Reference) reference.vec complete

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
