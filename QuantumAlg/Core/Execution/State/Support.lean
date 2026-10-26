/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-! # Support of deterministic classical updates and history maps -/

namespace QuantumAlg.Execution
noncomputable section
local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A register-carrier equality does not change the support of a mapped
classical label. Kept generic to avoid reducing a concrete P-256 register. -/
public lemma supported_register_cast_mapClassical
    {C D : Type} [Fintype C] [Fintype D]
    {R S Reference : Register} (h : R = S)
    (decision : DecidableEq D)
    (state : ExecutionState C (Register.prod R Reference))
    (update : C → D) (property : D → Prop)
    (all : ∀ original, property (update original))
    (value : D)
    (supported :
      0 < ((Eq.mp
        (congrArg
          (fun register : Register => ExecutionState D (Register.prod register Reference)) h)
        (@ExecutionState.mapClassical C D _ _ _ decision state update)).block value).mass) :
    property value := by
  cases h
  change 0 < ((@ExecutionState.mapClassical C D _ _ _ decision state update).block value).mass
    at supported
  obtain ⟨original, same, _positive⟩ :=
    (@ExecutionState.mapClassical_block_mass_pos_iff C D _ _ decision
      (Register.prod R Reference) state update value).mp supported
  exact same ▸ all original

/-- Rebracketing a complete execution history cannot create a newly supported
store; it preserves the store coordinate of each actual source block. -/
lemma State.supported_store_mapHistory
    {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
    {H K : Type} [Fintype H] [Fintype K]
    (state : State ctx Reference H) (historyMap : H → K)
    (property : Store ctx → Prop)
    (all : ∀ value, 0 < (state.block value).mass → property value.1)
    (value : Store ctx × K)
    (supported : 0 < ((State.mapHistory state historyMap).block value).mass) :
    property value.1 := by
  unfold State.mapHistory at supported
  obtain ⟨original, same, positive⟩ :=
    (ExecutionState.mapClassical_block_mass_pos_iff state
      (fun record => (record.1, historyMap record.2)) value).mp supported
  have storeSame : original.1 = value.1 := congrArg Prod.fst same
  rw [← storeSame]
  exact all original positive


end
end QuantumAlg.Execution
