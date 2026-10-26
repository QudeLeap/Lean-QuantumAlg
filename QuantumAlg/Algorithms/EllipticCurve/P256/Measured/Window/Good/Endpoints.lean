/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Prefix
import all QuantumAlg.Util.EllipticCurve.Representation

/-!
# Original seed and completed signed-power endpoints

The same chronological prefix starts at the selected affine seed and ends
at its left translation of the two original full-range powers. No source
digit is reduced and the original target appears with its inverse sign.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open PrimeFieldShortWeierstrass

attribute [local irreducible] branchGood prefixAffine

/-- Before any window the original complete prefix is exactly the chosen seed. -/
lemma prefixGroup_initial (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) :
    prefixGroup I branch 0 = (FullRange.chronologicalFixedSeed I).toGroupPoint := by
  simp only [prefixGroup, ExceptionalOffsetAveraging.prefixMultiplier, List.take_zero,
    List.foldl_nil, mul_one]

/-- The affine initial column is the original seed, independent of its admissibility witness. -/
lemma prefixAffine_initial (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (good : branchGood I branch) (within : 0 ≤ 34) :
    prefixAffine I branch good 0 within = FullRange.chronologicalFixedSeed I := by
  apply AffinePoint.toGroupPoint_injective
  exact (prefixAffine_group I branch good 0 within).trans (prefixGroup_initial I branch)

/-- Every original unsigned source digit contributes to the exact completed signed powers. -/
lemma prefixGroup_terminal (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) :
    prefixGroup I branch 34 =
      (FullRange.chronologicalFixedSeed I).toGroupPoint *
        ((ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).generator ^ branch.1.val *
          ((ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).target ^ branch.2.val)⁻¹) := by
  unfold prefixGroup
  rw [FullRange.chronologicalPrefix_complete]

/-- The complete final affine column represents that same original group endpoint. -/
lemma prefixAffine_terminal_group (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (good : branchGood I branch) (within : 34 ≤ 34) :
    (prefixAffine I branch good 34 within).toGroupPoint =
      (FullRange.chronologicalFixedSeed I).toGroupPoint *
        ((ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).generator ^ branch.1.val *
          ((ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).target ^ branch.2.val)⁻¹) :=
  (prefixAffine_group I branch good 34 within).trans (prefixGroup_terminal I branch)

private lemma equality_iff_of_translated_injective {Label G : Type}
    [Group G] (encode : Label → G) (injective : Function.Injective encode)
    (seed firstValue lastValue : G) (first last : Label)
    (firstEq : encode first = seed * firstValue)
    (lastEq : encode last = seed * lastValue) :
    first = last ↔ firstValue = lastValue := by
  rw [← injective.eq_iff, firstEq, lastEq, mul_left_cancel_iff]

/-- Distinctness of final affine labels is exactly the original signed-power kernel. -/
lemma prefixAffine_terminal_eq_iff (I : DomainParameters.PublicKeyInstance)
    (first last : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (firstGood : branchGood I first) (lastGood : branchGood I last)
    (firstWithin lastWithin : 34 ≤ 34) :
    prefixAffine I first firstGood 34 firstWithin =
        prefixAffine I last lastGood 34 lastWithin ↔
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).generator ^ first.1.val *
          ((ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).target ^ first.2.val)⁻¹ =
        (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).generator ^ last.1.val *
          ((ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).target ^ last.2.val)⁻¹ := by
  exact equality_iff_of_translated_injective
    (G := (DomainParameters.curve I.curveCert).GroupPoint)
    AffinePoint.toGroupPoint AffinePoint.toGroupPoint_injective
    (FullRange.chronologicalFixedSeed I).toGroupPoint _ _ _ _
    (prefixAffine_terminal_group I first firstGood firstWithin)
    (prefixAffine_terminal_group I last lastGood lastWithin)

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
