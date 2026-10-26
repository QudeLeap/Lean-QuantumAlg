/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Classical state maps independent of equality decisions

Finite classical relabeling depends only on the mapped values. Different
proofs that equality is decidable do not change any quantum block or its mass.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

/-- Pointwise equal classical maps give the same state under any equality decisions. -/
public lemma executionState_mapClassical_congr_decision
    {C D : Type} [Fintype C] [Fintype D] {R : Register}
    (state : ExecutionState C R) (left right : C → D)
    (same : ∀ entry, left entry = right entry) (firstDecision secondDecision : DecidableEq D) :
    @mapClassical C D _ _ R firstDecision state left =
      @mapClassical C D _ _ R secondDecision state right := by
  have decisionEquality : firstDecision = secondDecision := Subsingleton.elim _ _
  subst secondDecision
  exact congrArg (fun update =>
    @mapClassical C D _ _ R firstDecision state update) (funext same)

/-- A mapped block is positive exactly when one of its actual input blocks is positive. -/
public lemma mapClassical_block_mass_pos_iff {C D : Type} [Fintype C] [Fintype D]
    [DecidableEq D] {R : Register}
    (state : ExecutionState C R) (update : C → D) (value : D) :
    0 < ((state.mapClassical update).block value).mass ↔
      ∃ original, update original = value ∧ 0 < (state.block original).mass := by
  have mass : ((state.mapClassical update).block value).mass =
      ∑ original, if update original = value then (state.block original).mass else 0 :=
    sum_fiber_trace state update value
  rw [mass]
  have nonnegative : ∀ original ∈ (Finset.univ : Finset C),
      0 ≤ if update original = value then (state.block original).mass else 0 := by
    intro original _
    split
    · exact (state.block original).mass_nonneg
    · exact le_rfl
  rw [Finset.sum_pos_iff_of_nonneg nonnegative]
  constructor
  · rintro ⟨original, _member, positive⟩
    by_cases same : update original = value
    · exact ⟨original, same, by simpa only [same, if_true] using positive⟩
    · simp only [same, if_false, lt_self_iff_false] at positive
  · rintro ⟨original, same, positive⟩
    exact ⟨original, Finset.mem_univ _, by simpa only [same, if_true] using positive⟩


end

end QuantumAlg.ExecutionState
