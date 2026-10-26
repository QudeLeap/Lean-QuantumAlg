/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Address

/-!
# The original source-width transport as a complete equivalence

The product of the two existing finite-width equivalences has exactly
the existing sourceBranch values. No source label,
amplitude, admissibility predicate, or original domain is changed.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window

noncomputable section

open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

private def branchWidthEquiv {before after : Nat} (widths : before = after) :
    EllipticCurve.FullRange.Branch before ≃ EllipticCurve.FullRange.Branch after :=
  Equiv.prodCongr
    (finCongr (congrArg (fun width : Nat => 2 ^ width) widths))
    (finCongr (congrArg (fun width : Nat => 2 ^ width) widths))

private lemma branchWidthEquiv_apply {before after : Nat} (widths : before = after)
    (branch : EllipticCurve.FullRange.Branch before) :
    branchWidthEquiv widths branch = castBranch widths branch := by
  cases widths
  rfl

/-- The same original width cast, now with its inverse for complete-output reindexing. -/
def sourceBranchEquiv (I : DomainParameters.PublicKeyInstance) :
    EllipticCurve.FullRange.Branch (Cascade.exponentWidth I) ≃
      Sampling.SourceRegister.Index :=
  branchWidthEquiv (Cascade.exponentWidth_eq_260 I)

/-- The equivalence is the already used sourceBranch map on every original input. -/
lemma sourceBranchEquiv_apply (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) :
    sourceBranchEquiv I branch = sourceBranch I branch :=
  branchWidthEquiv_apply (Cascade.exponentWidth_eq_260 I) branch

/-- Every complete physical pair has exactly its original-width preimage. -/
lemma sourceBranchEquiv_inverse (I : DomainParameters.PublicKeyInstance)
    (source : Sampling.SourceRegister.Index) :
    sourceBranch I ((sourceBranchEquiv I).symm source) = source :=
  (sourceBranchEquiv_apply I ((sourceBranchEquiv I).symm source)).symm.trans
    ((sourceBranchEquiv I).apply_symm_apply source)

private lemma pairedBits_cast {before after : Nat} (widths : before = after)
    (branch : EllipticCurve.FullRange.Branch before) (position : Fin (2 * before)) :
    ExceptionalOffsetAveraging.pairedBigEndianSelected after
        (castBranch widths branch)
        (Fin.cast (congrArg (fun width : Nat => 2 * width) widths) position) =
      ExceptionalOffsetAveraging.pairedBigEndianSelected before branch position := by
  cases widths
  rfl

/-- The same width equivalence also preserves every original ordered event bit. -/
lemma sourceBranch_selectedBits (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (position : Fin (2 * Cascade.exponentWidth I)) :
    ExceptionalOffsetAveraging.pairedBigEndianSelected 260 (sourceBranch I branch)
        (Fin.cast (congrArg (fun width : Nat => 2 * width)
          (Cascade.exponentWidth_eq_260 I)) position) =
      ExceptionalOffsetAveraging.pairedBigEndianSelected (Cascade.exponentWidth I)
        branch position :=
  pairedBits_cast (Cascade.exponentWidth_eq_260 I) branch position

end

end QuantumAlg.EllipticCurve.P256.Measured.Window
