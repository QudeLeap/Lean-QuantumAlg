/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Execution

/-!
# Joint borrowed-state restoration for actual signed division

Only writable classical cells are modified. Composition preserves the complete
borrowed classical and quantum interface jointly with every external reference,
independently of output promises or the arithmetic preconditions.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem identity_restores (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.id ctx).BorrowedRestored Reference state
      ((Circuit.id ctx).execute Reference state) := by
  rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext, Circuit.execute_id]
  exact observeBorrowed_mapHistory state _

/-- The actual preparation prefix restores the complete borrowed interface. -/
theorem prepare_borrowedRestored (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (prepare refs).BorrowedRestored Reference state ((prepare refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact SignedWord.normalizeMagnitude_borrowedRestored refs.numerator refs.negative
      refs.magnitude Reference state
  · apply Circuit.borrowedRestored_seq
    · exact Circuit.borrowedRestored_seq _ _ _
        (Circuit.borrowedRestored_classical _ _) (Circuit.borrowedRestored_classical _ _)
    · exact Circuit.borrowedRestored_classical _ _

/-- Conditional correction restores borrowed state on each actual selected input fiber. -/
theorem rounding_borrowedRestored (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (roundingArm refs).BorrowedRestored Reference state
      ((roundingArm refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_classical _ _
  · apply Circuit.borrowedRestored_seq
    · apply Circuit.borrowedRestored_branch
      intro value history _ current
      cases value with
      | bit flag =>
          cases flag
          · exact identity_restores Reference current
          · exact Circuit.borrowedRestored_classical _ current
    · exact Circuit.borrowedRestored_classical _ _

/-- The final stored-sign dispatch also preserves all borrowed correlations. -/
theorem finish_borrowedRestored (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (finish refs).BorrowedRestored Reference state ((finish refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_classical _ _
  · apply Circuit.borrowedRestored_branch
    intro value history _ current
    cases value with
    | bit flag =>
        cases flag
        · exact identity_restores Reference current
        · exact Circuit.borrowedRestored_seq _ _ current
            (Circuit.borrowedRestored_classical _ _) (Circuit.borrowedRestored_classical _ _)

/-- Complete actual signed division restores the joint borrowed state for every reference input. -/
theorem body_borrowedRestored (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (body refs).BorrowedRestored Reference state ((body refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact prepare_borrowedRestored refs Reference state
  · apply Circuit.borrowedRestored_seq
    · exact rounding_borrowedRestored refs Reference _
    · apply Circuit.borrowedRestored_seq
      · exact Circuit.borrowedRestored_classical _ _
      · exact finish_borrowedRestored refs Reference _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv
