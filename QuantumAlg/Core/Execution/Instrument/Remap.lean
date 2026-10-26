/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ExecutionState

public import QuantumAlg.Core.Execution.Instrument.Retained

import all QuantumAlg.Core.Execution.Instrument.Retained
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Exact classical remapping of full retained physical blocks

Chronological path reassociation and Store overwrites sum every original
record fiber. The block matrices remain complete; no quantum marginal or
probability-only replacement is used.
-/

@[expose] public section

namespace QuantumAlg.Execution.Instrument

noncomputable section

open scoped BigOperators

/-- Remapping full retained records preserves every original block and overwrite fiber. -/
lemma remapRetainedBlocks {Original Outcome Intermediate Result : Type}
    [Fintype Original] [Fintype Outcome] [Fintype Intermediate]
    [DecidableEq Intermediate] [DecidableEq Result]
    {R : Register} (record : Original → Outcome → Intermediate)
    (update : Intermediate → Result) (branchBlock : Original → Outcome → HilbertOperator R)
    (result : Result) :
    (∑ middle : Intermediate, if update middle = result then
      (∑ original : Original, ∑ outcome : Outcome,
        if record original outcome = middle then branchBlock original outcome else 0)
      else 0) =
    ∑ original : Original, ∑ outcome : Outcome,
      if update (record original outcome) = result then branchBlock original outcome else 0 := by
  simpa only [Fintype.sum_unique, Matrix.conjTranspose_one, one_mul, mul_one] using
    composeRetainedBlocks record (fun middle (_ : Unit) => update middle) branchBlock
      (fun _ _ => (1 : HilbertOperator R)) result

/-- A proved component block equation transports through the actual classical state map. -/
lemma mapClassical_retained_matrix {Original Outcome Intermediate Result : Type}
    [Fintype Original] [Fintype Outcome] [Fintype Intermediate] [Fintype Result]
    [DecidableEq Intermediate] [DecidableEq Result]
    {R : Register} (state : ExecutionState Intermediate R)
    (record : Original → Outcome → Intermediate)
    (branchBlock : Original → Outcome → HilbertOperator R)
    (blockEquation : ∀ middle, (state.block middle).matrix =
      ∑ original : Original, ∑ outcome : Outcome,
        if record original outcome = middle then branchBlock original outcome else 0)
    (update : Intermediate → Result) (result : Result) :
    ((state.mapClassical update).block result).matrix =
      ∑ original : Original, ∑ outcome : Outcome,
        if update (record original outcome) = result then branchBlock original outcome else 0 := by
  rw [ExecutionState.mapClassical_block_matrix]
  simp_rw [blockEquation]
  exact remapRetainedBlocks record update branchBlock result

end

end QuantumAlg.Execution.Instrument
