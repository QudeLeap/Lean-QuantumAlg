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

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The actual preparation prefix restores the complete borrowed interface. -/
theorem prepare_borrowedRestored (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (prepare (model := model) refs).BorrowedRestored Reference state
      ((prepare (model := model) refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact SignedWord.normalizeMagnitude_borrowedRestored refs.numerator refs.negative
      refs.magnitude Reference state
  · apply Circuit.borrowedRestored_seq
    · exact Circuit.borrowedRestored_seq _ _ _
        (Circuit.borrowedRestored_classical _ _) (Circuit.borrowedRestored_classical _ _)
    · exact Circuit.borrowedRestored_classical _ _

/-- Conditional correction restores borrowed state on each actual selected input fiber. -/
theorem rounding_borrowedRestored (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (roundingArm (model := model) refs).BorrowedRestored Reference state
      ((roundingArm (model := model) refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_classical _ _
  · apply Circuit.borrowedRestored_seq
    · apply Circuit.borrowedRestored_branch
      intro value _history _ current
      cases value with
      | bit flag =>
          cases flag
          · exact Circuit.borrowedRestored_id current
          · exact Circuit.borrowedRestored_classical _ current
    · exact Circuit.borrowedRestored_classical _ _

/-- The final stored-sign dispatch also preserves all borrowed correlations. -/
theorem finish_borrowedRestored (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (finish (model := model) refs).BorrowedRestored Reference state
      ((finish (model := model) refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_classical _ _
  · apply Circuit.borrowedRestored_branch
    intro value _history _ current
    cases value with
    | bit flag =>
        cases flag
        · exact Circuit.borrowedRestored_id current
        · exact Circuit.borrowedRestored_seq _ _ current
            (Circuit.borrowedRestored_classical _ _) (Circuit.borrowedRestored_classical _ _)

/-- Complete actual signed division restores the joint borrowed state for every reference input. -/
theorem body_borrowedRestored (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (body (model := model) refs).BorrowedRestored Reference state
      ((body (model := model) refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact prepare_borrowedRestored refs Reference state
  · apply Circuit.borrowedRestored_seq
    · exact rounding_borrowedRestored refs Reference _
    · apply Circuit.borrowedRestored_seq
      · exact Circuit.borrowedRestored_classical _ _
      · exact finish_borrowedRestored refs Reference _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv
