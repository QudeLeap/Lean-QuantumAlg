/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Classical.OrderRecovery

/-!
# Candidate bounds along the actual Euclidean cursor path

The remaining candidates after any number of guarded Euclidean visits are a
suffix of the original finite continued fraction. An active cursor therefore
produces a genuine source denominator, bounded by the dyadic cardinality and
strictly below the widened word capacity.
-/

namespace QuantumAlg.ClassicalAlgorithms.OrderRecovery

/-- The head of any active raw cursor is one of that cursor's actual candidates. -/
lemma euclideanCursor_candidate_mem_of_active (cursor : EuclideanContinuantCursor)
    (active : cursor.denominator ≠ 0) :
    cursor.candidate.denominator ∈ cursor.actualCandidates := by
  rw [EuclideanContinuantCursor.actualCandidates_cons_of_active cursor active]
  exact List.mem_cons_self

/-- Advancing once leaves a suffix of exactly the same actual raw candidate path. -/
lemma euclideanCursor_advance_candidates_subset (cursor : EuclideanContinuantCursor)
    (active : cursor.denominator ≠ 0) :
    cursor.advance.actualCandidates ⊆ cursor.actualCandidates := by
  rw [EuclideanContinuantCursor.actualCandidates_cons_of_active cursor active]
  exact List.subset_cons_self _ _

/-- Every candidate remaining after fixed fuel belongs to the original finite source trace. -/
lemma dyadicCursor_remaining_candidates_subset {phaseBits : Nat}
    (numerator : Word phaseBits) (processed : Nat) :
    ((EuclideanContinuantCursor.initial numerator.val (2 ^ phaseBits)).advanceN
      processed).actualCandidates ⊆ finiteCandidates numerator := by
  rw [EuclideanContinuantCursor.actualCandidates_advanceN,
    initialEuclideanContinuantCandidates_eq_finiteCandidates]
  exact List.drop_subset _ _

/-- The next active candidate at every position is still an original source convergent. -/
lemma dyadicCursor_candidate_mem_of_active {phaseBits : Nat}
    (numerator : Word phaseBits) (processed : Nat)
    (active : ((EuclideanContinuantCursor.initial numerator.val (2 ^ phaseBits)).advanceN
      processed).denominator ≠ 0) :
    ((EuclideanContinuantCursor.initial numerator.val (2 ^ phaseBits)).advanceN
      processed).candidate.denominator ∈ finiteCandidates numerator :=
  dyadicCursor_remaining_candidates_subset numerator processed
    (euclideanCursor_candidate_mem_of_active _ active)

/-- Every active source cursor whose remaining path is genuine has a fitted next candidate. -/
lemma dyadicCursor_candidate_fits_of_remaining {phaseBits : Nat}
    (numerator : Word phaseBits) (cursor : EuclideanContinuantCursor)
    (remaining : cursor.actualCandidates ⊆ finiteCandidates numerator)
    (active : cursor.denominator ≠ 0) :
    cursor.candidate.denominator < 2 ^ (phaseBits + 1) := by
  have bounded := finiteCandidate_le_phaseCardinality numerator
    (remaining (euclideanCursor_candidate_mem_of_active cursor active))
  have positive := Nat.two_pow_pos phaseBits
  rw [Nat.pow_succ]
  omega

/-- The widened word never truncates a candidate on the actual initialized finite path. -/
lemma dyadicCursor_candidate_fits_of_active {phaseBits : Nat}
    (numerator : Word phaseBits) (processed : Nat)
    (active : ((EuclideanContinuantCursor.initial numerator.val (2 ^ phaseBits)).advanceN
      processed).denominator ≠ 0) :
    ((EuclideanContinuantCursor.initial numerator.val (2 ^ phaseBits)).advanceN
      processed).candidate.denominator < 2 ^ (phaseBits + 1) :=
  dyadicCursor_candidate_fits_of_remaining numerator _
    (dyadicCursor_remaining_candidates_subset numerator processed) active

end QuantumAlg.ClassicalAlgorithms.OrderRecovery
