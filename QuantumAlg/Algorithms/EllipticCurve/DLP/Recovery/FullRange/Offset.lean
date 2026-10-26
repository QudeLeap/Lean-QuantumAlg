/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Support
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Offset

/-!
# One full-range good subgroup seed

The finite averaging is over the complete physical square of exponent labels
and permits branch-dependent window addends.  The resulting mass bound is for
the full-range amplitudes, rather than a subgroup-order range preparation.
-/

namespace QuantumAlg.EllipticCurve.FullRange

noncomputable section

open PrimeFieldShortWeierstrass ECDLP.Measured

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- A single nonidentity affine subgroup seed controls the bad cardinality on
all full-range branches, with branch-dependent addends. -/
lemma exists_fixedSeed_exceptional_card_bound
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (orderAtLeastTwo : 2 ≤ problem.order) (width steps : Nat)
    (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → GroupPoint E) :
    ∃ seed : AffinePoint E,
      seed.toGroupPoint ∈ Subgroup.zpowers problem.generator ∧
      seed.toGroupPoint ≠ 1 ∧
      (problem.order - 1) *
        (exceptionalBranches width steps selected addend seed.toGroupPoint).card ≤
        (2 ^ width * 2 ^ width) * (2 * steps) := by
  classical
  obtain ⟨offset, member, bound⟩ :=
    ExceptionalOffsetAveraging.exists_fixed_offset_branch_addends
      (candidateOffsets problem) (Finset.univ : Finset (Branch width))
      (candidateOffsets_nonempty problem orderAtLeastTwo) steps selected addend
  have membership := (mem_candidateOffsets problem offset).mp member
  obtain ⟨seed, seedGroup⟩ := exists_affineRepresentative offset membership.2
  refine ⟨seed, ?_, ?_, ?_⟩
  · simpa only [seedGroup] using membership.1
  · simpa only [seedGroup] using membership.2
  · simpa only [exceptionalBranches, seedGroup, candidateOffsets_card, Finset.card_univ,
      branch_card] using bound

/-- Full-range squared-amplitude mass, including every physical label, obeys
the two-exceptions-per-step average for one fixed affine subgroup seed. -/
lemma exists_fixedSeed_exceptionalMass_bound
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (orderAtLeastTwo : 2 ≤ problem.order) (width steps : Nat)
    (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → GroupPoint E) :
    ∃ seed : AffinePoint E,
      seed.toGroupPoint ∈ Subgroup.zpowers problem.generator ∧
      seed.toGroupPoint ≠ 1 ∧
      exceptionalMass width steps selected addend seed.toGroupPoint ≤
        (2 * steps : Nat) / ((problem.order - 1 : Nat) : ℝ) := by
  obtain ⟨seed, subgroup, nonidentity, bound⟩ :=
    exists_fixedSeed_exceptional_card_bound problem orderAtLeastTwo width steps selected addend
  refine ⟨seed, subgroup, nonidentity, ?_⟩
  exact exceptionalMass_le_of_card_bound width steps (problem.order - 1) (2 * steps)
    selected addend seed.toGroupPoint (by omega) bound

end

end QuantumAlg.EllipticCurve.FullRange
