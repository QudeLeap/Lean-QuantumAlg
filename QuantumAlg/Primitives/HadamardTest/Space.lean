/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Primitives.HadamardTest.Specification
import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum

/-!
# Complete live space of the Hadamard test

The original owned input, the actual prepared control, and the measured
classical cell remain live. Both resident and auxiliary-role capacities count
these same resources [AJL06, qf2.tex:625-645].
-/

namespace QuantumAlg.HadamardTest

noncomputable section

open Execution

private lemma context_spaces (width : Nat) (frame : RuntimeCtx .quantum)
    (present : frame ∈ [pre width, prepared width, post width]) :
    frame.residentSpace ≤ spaceBudget width ∧ frame.auxiliarySpace ≤ spaceBudget width := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl
  all_goals
    constructor <;> intro axis
  all_goals
    simp only [pre, prepared, post, OwnedQubitPrefix.pre, OwnedQubitPrefix.post,
      RuntimeCtx.residentSpace_addOwnedLayout, RuntimeCtx.auxiliarySpace_addOwnedLayout,
      RuntimeCtx.residentSpace_addRetained, RuntimeCtx.auxiliarySpace_addRetained,
      RuntimeCtx.residentSpace_empty, RuntimeCtx.auxiliarySpace_empty, Pi.add_apply,
      Pi.zero_apply]
    cases axis with
    | classicalBits =>
        norm_num [SpacePool.ofQuantumLayout, SpacePool.ofShape, spaceBudget, CShape.bitWidth]
        all_goals decide
    | quantumSystems dimension =>
        simp only [SpacePool.ofQuantumLayout, SpacePool.ofShape,
          QubitLayout.toQuantumLayout_dimensionCount, spaceBudget]
        split <;> omega

private lemma visited_spaces (width : Nat)
    (path : (code width).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (code width).visitedContexts path) :
    frame.residentSpace ≤ spaceBudget width ∧ frame.auxiliarySpace ≤ spaceBudget width := by
  apply context_spaces width frame
  change frame ∈ ([pre width, prepared width] ++
    ([prepared width] ++ [prepared width, post width])) ++ [post width, post width] at present
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present ⊢
  tauto

/-- Actual resident peaks include the complete retained output. -/
lemma code_residentSpace (width : Nat)
    (path : (code width).Path) :
    (code width).peakResidentSpace path ≤ spaceBudget width :=
  Circuit.peakResidentSpace_le_of_visited (code width) path (spaceBudget width)
    (fun frame present => (visited_spaces width path frame present).1)

/-- Actual auxiliary-role peaks count the same owned words and retained result cell. -/
lemma code_auxiliarySpace (width : Nat)
    (path : (code width).Path) :
    (code width).peakAuxiliarySpace path ≤ spaceBudget width :=
  Circuit.peakAuxiliarySpace_le_of_visited (code width) path (spaceBudget width)
    (fun frame present => (visited_spaces width path frame present).2)

end

end QuantumAlg.HadamardTest
