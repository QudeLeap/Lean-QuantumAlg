/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Mathlib.Algebra.BigOperators.Fin

public import QuantumAlg.Core.Base.Gate.Basic

import all QuantumAlg.Core.Base.Gate.Effect
import Mathlib.Algebra.BigOperators.Fin

/-!
# Full retained-block sums on the actual intermediate classical record

This algebraic composition preserves all original-record fibers, including
overwrites. The second operator reads precisely the intermediate record
produced by the first. Consumers separately connect both component sums to
their actual interpreter equations; this lemma supplies no quantum operation.
-/

@[expose] public section

namespace QuantumAlg.Execution.Instrument

noncomputable section

open scoped BigOperators

/-- Compose complete retained block sums without an injectivity or separability assumption. -/
lemma composeRetainedBlocks {Original FirstOutcome Intermediate SecondOutcome Result : Type}
    [Fintype Original] [Fintype FirstOutcome] [Fintype Intermediate] [Fintype SecondOutcome]
    [DecidableEq Intermediate] [DecidableEq Result]
    {R : Register} (firstRecord : Original → FirstOutcome → Intermediate)
    (secondRecord : Intermediate → SecondOutcome → Result)
    (firstBlock : Original → FirstOutcome → HilbertOperator R)
    (secondOperator : Intermediate → SecondOutcome → HilbertOperator R) (result : Result) :
    (∑ middle : Intermediate, ∑ second : SecondOutcome,
      if secondRecord middle second = result then
        secondOperator middle second *
          (∑ original : Original, ∑ first : FirstOutcome,
            if firstRecord original first = middle then firstBlock original first else 0) *
          (secondOperator middle second).conjTranspose
      else 0) =
    ∑ original : Original, ∑ first : FirstOutcome, ∑ second : SecondOutcome,
      if secondRecord (firstRecord original first) second = result then
        secondOperator (firstRecord original first) second * firstBlock original first *
          (secondOperator (firstRecord original first) second).conjTranspose
      else 0 := by
  have expand (middle : Intermediate) (second : SecondOutcome) :
      (if secondRecord middle second = result then
        secondOperator middle second *
          (∑ original : Original, ∑ first : FirstOutcome,
            if firstRecord original first = middle then firstBlock original first else 0) *
          (secondOperator middle second).conjTranspose
       else 0) =
      ∑ original : Original, ∑ first : FirstOutcome,
        if firstRecord original first = middle then
          (if secondRecord middle second = result then
            secondOperator middle second * firstBlock original first *
              (secondOperator middle second).conjTranspose
           else 0)
        else 0 := by
    by_cases selected : secondRecord middle second = result
    · simp only [if_pos selected, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro original _
      apply Finset.sum_congr rfl
      intro first _
      split_ifs <;> simp
    · simp [selected]
  simp_rw [expand]
  have reorder := Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun middle : Intermediate × SecondOutcome =>
      fun original : Original × FirstOutcome =>
        if firstRecord original.1 original.2 = middle.1 then
          (if secondRecord middle.1 middle.2 = result then
            secondOperator middle.1 middle.2 * firstBlock original.1 original.2 *
              (secondOperator middle.1 middle.2).conjTranspose
           else 0)
        else 0)
  rw [show (∑ middle : Intermediate, ∑ second : SecondOutcome,
      ∑ original : Original, ∑ first : FirstOutcome,
        if firstRecord original first = middle then
          (if secondRecord middle second = result then
            secondOperator middle second * firstBlock original first *
              (secondOperator middle second).conjTranspose
           else 0)
        else 0) =
      ∑ original : Original, ∑ first : FirstOutcome,
        ∑ middle : Intermediate, ∑ second : SecondOutcome,
          if firstRecord original first = middle then
            (if secondRecord middle second = result then
              secondOperator middle second * firstBlock original first *
                (secondOperator middle second).conjTranspose
             else 0)
          else 0 by
    simpa only [Fintype.sum_prod_type] using reorder]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro second _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

end

end QuantumAlg.Execution.Instrument
