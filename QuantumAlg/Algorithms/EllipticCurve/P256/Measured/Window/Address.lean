/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Address
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.FullRange.Seed.Chronological

/-!
# Actual source digits in the fresh chronological full-range seed family

The original width equality preserves each exponent's unsigned value.
Actual source selection then gives exactly the address and whole-digit
enable of the new chronological family, including every zero address and
the high four-bit tails. This is a mathematical source-coordinate bridge;
no physical system, source feed or reference is replaced.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window

noncomputable section

open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

private def castBranch {before after : Nat} (widths : before = after)
    (branch : EllipticCurve.FullRange.Branch before) : EllipticCurve.FullRange.Branch after :=
  (Fin.cast (congrArg (fun width => 2 ^ width) widths) branch.1,
    Fin.cast (congrArg (fun width => 2 ^ width) widths) branch.2)

private lemma castBranch_values {before after : Nat} (widths : before = after)
    (branch : EllipticCurve.FullRange.Branch before) :
    (castBranch widths branch).1.val = branch.1.val ∧
      (castBranch widths branch).2.val = branch.2.val := ⟨rfl, rfl⟩

private lemma castBranch_injective {before after : Nat} (widths : before = after) :
    Function.Injective (castBranch widths) := by
  cases widths
  intro first last same
  exact same

/-- The original full pair in the same 260-bit mathematical source, preserving both values. -/
def sourceBranch (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) :
    Sampling.SourceRegister.Index := castBranch (Cascade.exponentWidth_eq_260 I) branch

lemma sampling_sourceBranch_values (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) :
    (sourceBranch I branch).1.val = branch.1.val ∧
      (sourceBranch I branch).2.val = branch.2.val :=
  castBranch_values (Cascade.exponentWidth_eq_260 I) branch

/-- The width transport preserves every original complete exponent pair distinctly. -/
lemma sampling_sourceBranch_injective (I : DomainParameters.PublicKeyInstance) :
    Function.Injective (sourceBranch I) :=
  castBranch_injective (Cascade.exponentWidth_eq_260 I)

private lemma chronologicalAddress_digit (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) (position : Fin 34) :
    FullRange.chronologicalAddress I branch position =
      Nat.FixedWidth.Radix.digit (2 ^ 16)
        (Sampling.sourceValue (Sampling.chronologicalIndex position) (sourceBranch I branch)).val
        (Sampling.chronologicalIndex position).logical.val := by
  refine Fin.addCases (m := 17) (n := 17) (fun index => ?_) (fun index => ?_) position
  · rw [Sampling.chronologicalIndex_first, FullRange.chronologicalAddress_first]
    change Nat.FixedWidth.Radix.digit (2 ^ 16) branch.1.val index.rev.val =
      Nat.FixedWidth.Radix.digit (2 ^ 16) (sourceBranch I branch).1.val index.rev.val
    exact congrArg (fun value => Nat.FixedWidth.Radix.digit (2 ^ 16) value index.rev.val)
      (sampling_sourceBranch_values I branch).1.symm
  · rw [Sampling.chronologicalIndex_second, FullRange.chronologicalAddress_second]
    change Nat.FixedWidth.Radix.digit (2 ^ 16) branch.2.val index.rev.val =
      Nat.FixedWidth.Radix.digit (2 ^ 16) (sourceBranch I branch).2.val index.rev.val
    exact congrArg (fun value => Nat.FixedWidth.Radix.digit (2 ^ 16) value index.rev.val)
      (sampling_sourceBranch_values I branch).2.symm

/-- Each real source partition uses the exact address in the fresh chronological seed family. -/
lemma sampling_sourcePartition_chronologicalAddress {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) (position : Fin 34) :
    (parameters.sourcePartition (Sampling.chronologicalIndex position)
      (sourceBranch I branch)).1.val = FullRange.chronologicalAddress I branch position :=
  (parameters.sampling_sourcePartition_digit_val _ _).trans
    (chronologicalAddress_digit I branch position).symm

/-- The actual current whole-digit predicate is exactly the fresh family's selected predicate. -/
lemma sampling_sourcePartition_chronologicalSelected {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) (position : Fin 34) :
    decide ((parameters.sourcePartition (Sampling.chronologicalIndex position)
      (sourceBranch I branch)).1.val ≠ 0) = FullRange.chronologicalSelected I branch position :=
  congrArg (fun value : Nat => decide (value ≠ 0))
    (sampling_sourcePartition_chronologicalAddress parameters I branch position)

end

end QuantumAlg.EllipticCurve.P256.Measured.Window
