/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Fourier.Original

/-!
# The unchanged original coherent source under its unsigned width transport

The same finite good support and all raw Reference amplitudes are retained.
The original width equality alone preserves the complete coherent norm, and
the existing good-vector bound includes empty support and zero good mass.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass ECDLP.Measured
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open scoped BigOperators

attribute [local irreducible] branchGood prefixAffine

private lemma norm_cast_family {before after : Nat} (widths : before = after)
    {Family : Type} [Fintype Family]
    (input : Family → EllipticCurve.FullRange.Branch before) (amplitude : Family → ℂ)
    {Reference : Register} (reference : HilbertVector Reference) :
    ‖∑ branch : Family, ∑ ref : Reference.Index,
      (amplitude branch * reference ref) •
        (NormalizedVector.ket
          (R := (EllipticCurve.FullRange.Geometry.branchRegister after).prod Reference)
          ((Fin.cast (congrArg (fun width : Nat => 2 ^ width) widths) (input branch).1,
            Fin.cast (congrArg (fun width : Nat => 2 ^ width) widths)
              (input branch).2), ref)).vec‖ =
      ‖∑ branch : Family, ∑ ref : Reference.Index,
        (amplitude branch * reference ref) •
          (NormalizedVector.ket
            (R := (EllipticCurve.FullRange.Geometry.branchRegister before).prod Reference)
            (input branch, ref)).vec‖ := by
  cases widths
  rfl

/-- The original unsigned width transport preserves the complete raw coherent source norm. -/
lemma sourceBranch_coherent_norm (I : DomainParameters.PublicKeyInstance)
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) :
    ‖∑ branch : GoodBranch I, ∑ ref : Reference.Index,
      (amplitude branch * reference ref) •
        (NormalizedVector.ket (R := Sampling.SourceRegister.prod Reference)
          (sourceBranch I branch.val, ref)).vec‖ =
      ‖∑ branch : GoodBranch I, ∑ ref : Reference.Index,
        (amplitude branch * reference ref) •
          (NormalizedVector.ket
            (R := (EllipticCurve.FullRange.Geometry.branchRegister
              (Cascade.exponentWidth I)).prod Reference) (branch.val, ref)).vec‖ :=
  norm_cast_family (Cascade.exponentWidth_eq_260 I)
    (fun branch : GoodBranch I => branch.val) amplitude (Reference := Reference) reference

/-- The unchanged original good-vector bound also bounds its actual source-width image. -/
lemma sourceBranch_good_norm_le_one (I : DomainParameters.PublicKeyInstance)
    {Reference : Register} (reference : NormalizedVector Reference) :
    ‖∑ branch : GoodBranch I, ∑ ref : Reference.Index,
      (EllipticCurve.FullRange.branchAmplitude (Cascade.exponentWidth I) branch.val *
        reference ref) •
        (NormalizedVector.ket (R := Sampling.SourceRegister.prod Reference)
          (sourceBranch I branch.val, ref)).vec‖ ≤ 1 := by
  have same := sourceBranch_coherent_norm I
    (fun branch => EllipticCurve.FullRange.branchAmplitude (Cascade.exponentWidth I) branch.val)
    (Reference := Reference) reference.vec
  exact same.trans_le ((congrArg
    (fun vector : HilbertVector ((EllipticCurve.FullRange.Geometry.branchRegister
      (Cascade.exponentWidth I)).prod Reference) => ‖vector‖)
    (original_goodVector_expansion I (Reference := Reference) reference)).symm.trans_le
    (EllipticCurve.FullRange.Geometry.goodVector_norm_le_one
      (Cascade.exponentWidth I) 34 (FullRange.chronologicalSelected I)
      (FullRange.chronologicalAddend I)
      (FullRange.chronologicalFixedSeed I).toGroupPoint reference))

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
