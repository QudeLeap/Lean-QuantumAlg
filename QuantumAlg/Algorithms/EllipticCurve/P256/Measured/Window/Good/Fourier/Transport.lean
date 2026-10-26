/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Geometry.Transport
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Fourier.Source
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Sequence.Initial

/-!
# The actual source effect in the unchanged original width coordinates

The existing width equality transports the same positive contractive effect.
Its complete coherent quadratic form is unchanged for any finite source family
and raw Reference vector. The original good component remains subnormalized,
including zero mass; the full source has its existing normalized weight.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open scoped BigOperators

/-- The same certified source effect expressed at the original problem's exponent width. -/
def sourceWidthEffect (I : DomainParameters.PublicKeyInstance) {Reference : Register}
    (effect : Effect (Sampling.SourceRegister.prod Reference)) :
    Effect ((EllipticCurve.FullRange.Geometry.branchRegister
      (Cascade.exponentWidth I)).prod Reference) :=
  EllipticCurve.FullRange.Geometry.widthEffect (Cascade.exponentWidth_eq_260 I) effect

/-- The complete raw coherent source has precisely its original-width quadratic weight. -/
lemma sourceWidthEffect_coherent_quadratic (I : DomainParameters.PublicKeyInstance)
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference)
    (effect : Effect (Sampling.SourceRegister.prod Reference)) :
    HilbertOperator.quadraticWeight (sourceWidthEffect I effect).matrix
        (∑ branch : GoodBranch I, ∑ ref : Reference.Index,
          (amplitude branch * reference ref) •
            (NormalizedVector.ket
              (R := (EllipticCurve.FullRange.Geometry.branchRegister
                (Cascade.exponentWidth I)).prod Reference) (branch.val, ref)).vec) =
      HilbertOperator.quadraticWeight effect.matrix
        (coherentSource I amplitude (Reference := Reference) reference) :=
  EllipticCurve.FullRange.Geometry.widthEffect_family_quadratic (Cascade.exponentWidth_eq_260 I)
    (fun branch : GoodBranch I => branch.val) amplitude (Reference := Reference) reference effect

/-- The original complete good component has its actual source weight, including zero mass. -/
lemma sourceWidthEffect_good_weight (I : DomainParameters.PublicKeyInstance)
    {Reference : Register} (reference : NormalizedVector Reference)
    (effect : Effect (Sampling.SourceRegister.prod Reference)) :
    (sourceWidthEffect I effect).weight
        (DensityOperator.ofSubnormalizedVector
          (EllipticCurve.FullRange.Geometry.goodVector (Cascade.exponentWidth I) 34
            (FullRange.chronologicalSelected I) (FullRange.chronologicalAddend I)
            (FullRange.chronologicalFixedSeed I).toGroupPoint reference)
          (EllipticCurve.FullRange.Geometry.goodVector_norm_le_one
            (Cascade.exponentWidth I) 34 (FullRange.chronologicalSelected I)
            (FullRange.chronologicalAddend I)
            (FullRange.chronologicalFixedSeed I).toGroupPoint reference)) =
      effect.weight (DensityOperator.ofSubnormalizedVector
        (coherentSource I (fun branch =>
          EllipticCurve.FullRange.branchAmplitude (Cascade.exponentWidth I) branch.val)
          (Reference := Reference) reference.vec)
        (sourceBranch_good_norm_le_one I (Reference := Reference) reference)) := by
  have expanded := congrArg
    (fun vector : HilbertVector ((EllipticCurve.FullRange.Geometry.branchRegister
        (Cascade.exponentWidth I)).prod Reference) =>
      HilbertOperator.quadraticWeight (sourceWidthEffect I effect).matrix vector)
    (original_goodVector_expansion I (Reference := Reference) reference)
  have transported := sourceWidthEffect_coherent_quadratic I
    (fun branch => EllipticCurve.FullRange.branchAmplitude (Cascade.exponentWidth I) branch.val)
    (Reference := Reference) reference.vec effect
  have left := Effect.weight_ofSubnormalizedVector (sourceWidthEffect I effect)
    (EllipticCurve.FullRange.Geometry.goodVector (Cascade.exponentWidth I) 34
      (FullRange.chronologicalSelected I) (FullRange.chronologicalAddend I)
      (FullRange.chronologicalFixedSeed I).toGroupPoint reference)
    (EllipticCurve.FullRange.Geometry.goodVector_norm_le_one
      (Cascade.exponentWidth I) 34 (FullRange.chronologicalSelected I)
      (FullRange.chronologicalAddend I)
      (FullRange.chronologicalFixedSeed I).toGroupPoint reference)
  have right := Effect.weight_ofSubnormalizedVector effect
    (coherentSource I (fun branch =>
      EllipticCurve.FullRange.branchAmplitude (Cascade.exponentWidth I) branch.val)
      (Reference := Reference) reference.vec)
    (sourceBranch_good_norm_le_one I (Reference := Reference) reference)
  exact left.trans (expanded.trans (transported.trans right.symm))

/-- The full original source has exactly the weight used by the actual uniform-source bridge. -/
lemma sourceWidthEffect_full_weight (I : DomainParameters.PublicKeyInstance)
    {Reference : Register} (reference : NormalizedVector Reference)
    (effect : Effect (Sampling.SourceRegister.prod Reference)) :
    (sourceWidthEffect I effect).weight
        (DensityOperator.ofPure
          (EllipticCurve.FullRange.Geometry.sourceState (Cascade.exponentWidth I) reference)) =
      effect.weight
        (DensityOperator.ofPure (EllipticCurve.FullRange.Geometry.sourceState 260 reference)) :=
  EllipticCurve.FullRange.Geometry.widthEffect_sourceState_weight (Cascade.exponentWidth_eq_260 I)
    (Reference := Reference) reference effect

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
