/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Restart.Sequence
import all QuantumAlg.Core.Execution.SelectionAll
import all QuantumAlg.Core.Execution.Input.Oracle

/-!
# A fixed physical cleanup seed at the next section's input

The actual predecessor execution is grouped by its output store and service
state in `nextInput`. A joint-state witness separates that concrete execution
from the dependent all-wires selection transport.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {pre post : RuntimeCtx model.kind}

/-- Every service/store input block has an actual joint extension with one
fixed owned seed. The reference register is existential only because this
predicate observes the local input after its external reference is traced out. -/
def JointSeededInitialization (post : RuntimeCtx model.kind)
    (seed : post.quantumLayout.SelectedBasis post.borrowedSelectionᶜ)
    (state : ExecutionState
      (Store post × model.classicalOracles.HiddenState) post.register) : Prop :=
  ∀ entry, ∃ (Reference : Register)
      (joint : DensityOperator (Register.prod post.register Reference)),
    state.block entry = joint.marginalLeft ∧
      (StatePromise.pure (NormalizedVector.ket seed)).Holds
        (DensityOperator.observeSelection post.quantumLayout
          post.borrowedSelectionᶜ Reference joint)

/-- Actual reinitialization supplies the local joint-state witness after
`nextInput` groups real histories, for arbitrary original references. -/
lemma ReinitializedAt.nextInput_jointSeeded
    (code : Circuit model pre post)
    (environment : model.Environment)
    (seed : post.quantumLayout.SelectedBasis post.borrowedSelectionᶜ)
    (fixed : ReinitializedAt code environment seed)
    {Reference : Register}
    (input : OracleInput model.classicalOracles pre Reference) :
    JointSeededInitialization post seed (code.nextInput environment input).localState := by
  intro entry
  let entered := input.state.mapClassical (fun value => (value.1, (value.2, ())))
  let read := fun record : Store post ×
      (model.classicalOracles.HiddenState × (Unit × code.Path)) =>
        (record.1, record.2.1)
  let grouped : ExecutionState (Store post × model.classicalOracles.HiddenState)
      (Register.prod post.register Reference) :=
    @ExecutionState.mapClassical _ _ _ _ _
      (@RestartCleanup.instDecidableEq
        (Store post × model.classicalOracles.HiddenState))
      (code.execute environment Reference entered) read
  have pure := (RestartCleanup.groupedPureAt environment fixed) Reference entered read entry
  have stateEq0 : (code.nextInput environment input).state =
      (code.execute environment Reference entered).mapClassical read := rfl
  have stateEq : (code.nextInput environment input).state = grouped :=
    stateEq0.trans (ExecutionState.executionState_mapClassical_congr_decision
      (code.execute environment Reference entered) read read (by intro; rfl) _ _)
  refine ⟨Reference, grouped.block entry, ?_, ?_⟩
  · rw [OracleInput.oracleInput_localState_block]
    exact congrArg (fun state => (state.block entry).marginalLeft) stateEq
  · exact pure

private lemma pure_allSelection {count : Nat} (layout : QuantumLayout count)
    (selection : Finset (Fin count)) (all : selection = Finset.univ)
    (seed : layout.SelectedBasis selection) (Reference : Register)
    (state : DensityOperator (Register.prod layout.register Reference))
    (pure : (StatePromise.pure (NormalizedVector.ket seed)).Holds
      (DensityOperator.observeSelection layout selection Reference state)) :
    (StatePromise.pure (NormalizedVector.ket (all ▸ seed))).Holds
      (state.marginalLeft.reindex
        (S := layout.selectedRegister Finset.univ) layout.allSelectedBasisEquiv) := by
  cases all
  simpa only [DensityOperator.observeSelection_all] using pure

/-- With no borrowed quantum wires, the joint-state witness is exactly the
full fixed pure seed on each local input block. -/
lemma JointSeededInitialization.allSeed
    (post : RuntimeCtx model.kind)
    (seed : post.quantumLayout.SelectedBasis post.borrowedSelectionᶜ)
    (all : post.borrowedSelectionᶜ = Finset.univ)
    (state : ExecutionState
      (Store post × model.classicalOracles.HiddenState) post.register)
    (seeded : JointSeededInitialization post seed state) (entry) :
    (StatePromise.pure (NormalizedVector.ket (all ▸ seed))).Holds
      ((state.block entry).reindex
        (S := post.quantumLayout.selectedRegister Finset.univ)
        post.quantumLayout.allSelectedBasisEquiv) := by
  obtain ⟨Reference, joint, blockEq, pure⟩ := seeded entry
  rw [blockEq]
  exact pure_allSelection post.quantumLayout post.borrowedSelectionᶜ all
    seed Reference joint pure

end

end QuantumAlg.Circuit
