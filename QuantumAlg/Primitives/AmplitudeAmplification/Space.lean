/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.AmplitudeAmplification.Execution
import all QuantumAlg.Primitives.AmplitudeAmplification.Specification
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum

/-!
# Actual complete amplification space

The source and selected helper are created once and never released. Every
actual visited context respects the independent dimension-indexed budget,
and every owned system also contributes to auxiliary capacity.
-/

namespace QuantumAlg.AmplitudeAmplification

noncomputable section

private theorem pre_residentSpace : pre.residentSpace = 0 := by
  ext axis
  cases axis <;> rfl

private theorem pre_auxiliarySpace : pre.auxiliarySpace = 0 := rfl

theorem post_residentSpace (n k : Nat) : (post n k).residentSpace = spaceBudget n k := by
  rw [post, RuntimeCtx.residentSpace_addOwnedLayout, pre_residentSpace, add_zero]
  ext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension => exact (qubitLayout n k).toQuantumLayout_dimensionCount dimension

theorem post_auxiliarySpace (n k : Nat) : (post n k).auxiliarySpace = spaceBudget n k := by
  rw [post, RuntimeCtx.auxiliarySpace_addOwnedLayout, pre_auxiliarySpace, add_zero]
  ext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension => exact (qubitLayout n k).toQuantumLayout_dimensionCount dimension

private theorem visited_spaces {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    (path : (code M k).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (code M k).visitedContexts path) :
    frame.residentSpace ≤ spaceBudget n k ∧ frame.auxiliarySpace ≤ spaceBudget n k := by
  change frame ∈ [pre, post n k] ++ [post n k] at present
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with (same | same) | same
  · subst frame
    rw [pre_residentSpace, pre_auxiliarySpace]
    exact ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  · subst frame
    rw [post_residentSpace, post_auxiliarySpace]
    exact ⟨le_rfl, le_rfl⟩
  · subst frame
    rw [post_residentSpace, post_auxiliarySpace]
    exact ⟨le_rfl, le_rfl⟩

/-- The resident bound holds on every actual path. -/
theorem code_residentSpace {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    (path : (code M k).Path) : (code M k).peakResidentSpace path ≤ spaceBudget n k :=
  Circuit.peakResidentSpace_le_of_visited (code M k) path (spaceBudget n k)
    (fun frame present => (visited_spaces M k path frame present).1)

/-- The same live owned systems satisfy the independent auxiliary bound. -/
theorem code_auxiliarySpace {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    (path : (code M k).Path) : (code M k).peakAuxiliarySpace path ≤ spaceBudget n k :=
  Circuit.peakAuxiliarySpace_le_of_visited (code M k) path (spaceBudget n k)
    (fun frame present => (visited_spaces M k path frame present).2)

end

end QuantumAlg.AmplitudeAmplification
