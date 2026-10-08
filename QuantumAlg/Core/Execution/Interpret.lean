/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Circuit
public import QuantumAlg.Core.Execution.State
public import QuantumAlg.Core.Execution.Classical.Step
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Control

/-!
# One interpretation of typed circuits

Every execution retains its actual classical store, complete quantum state,
external reference correlations, persistent classical oracle state and finite
path record. The oracle state is shared by every instruction and iteration;
only a granted query transition can change it. The mass equality
is proved during structural interpretation; no caller supplies a transition,
distribution, event trace, or normalization certificate.

Classical branching first reads the current store, then executes the selected
body. Quantum control remains part of the pure unitary circuit supplied by a
unitary instruction.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private abbrev Preserving {kind : ProblemKind} (Hidden : Type) [Fintype Hidden]
    (pre post : RuntimeCtx kind) (Reference : Register) (Path : Type) [Fintype Path] :=
  {H : Type} → [Fintype H] → (state : State pre Reference (Hidden × H)) →
    {result : State post Reference (Hidden × (H × Path)) // result.mass = state.mass}

private def preserveService {kind : ProblemKind} {pre post : RuntimeCtx kind}
    {Reference : Register} {Hidden H Path : Type}
    [Fintype Hidden] [Fintype H] [Fintype Path]
    (state : State pre Reference (Hidden × H))
    (result : {result : State post Reference ((Hidden × H) × Path) //
      result.mass = state.mass}) :
    {result : State post Reference (Hidden × (H × Path)) // result.mass = state.mass} :=
  ⟨result.val.mapHistory (fun history => (history.1.1, (history.1.2, history.2))),
    (result.val.mapHistory_mass _).trans result.property⟩

private def repeatPreserving {kind : ProblemKind} {Hidden : Type} [Fintype Hidden]
    {ctx : RuntimeCtx kind} {Reference : Register} {Path : Type} [Fintype Path]
    (body : Preserving Hidden ctx ctx Reference Path) :
    (count : Nat) → Preserving Hidden ctx ctx Reference (Fin count → Path)
  | 0 => fun state =>
      ⟨state.mapHistory (fun history => (history.1, (history.2, Fin.elim0))),
        state.mapHistory_mass _⟩
  | count + 1 => fun state =>
      let first := body state
      let rest := repeatPreserving body count first.val
      ⟨rest.val.mapHistory (fun history =>
        (history.1, (history.2.1.1, Fin.cons history.2.1.2 history.2.2))),
        (rest.val.mapHistory_mass _).trans (rest.property.trans first.property)⟩

/-- Structurally execute the single instruction language and prove its mass equality. -/
def interpret {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (Reference : Register) :
    Preserving model.HiddenState pre post Reference code.Path :=
  match code with
  | .id _ctx => fun state => preserveService state ⟨state.skip, state.skip_mass⟩
  | .classical application => fun state =>
      preserveService state ⟨nativeStep application state, nativeStep_mass application state⟩
  | .classicalQuery application => fun state =>
      ⟨queryStep application state, queryStep_mass application state⟩
  | .unitary program => fun state =>
      preserveService state ⟨state.unitary program.matrix, state.unitary_mass program.matrix⟩
  | .measureZ wire output => fun state =>
      preserveService state
        ⟨State.measureZ state wire output, State.measureZ_mass state wire output⟩
  | .retain _ctx key shape fresh => fun state =>
      preserveService state ⟨state.retain key shape fresh, state.retain_mass key shape fresh⟩
  | .prepareZero _ctx key layout fresh disjoint => fun state =>
      preserveService state
        ⟨state.prepare key layout fresh disjoint (BasisPreparation.zero layout),
          state.prepare_mass key layout fresh disjoint (BasisPreparation.zero layout)⟩
  | .seq first second => fun state =>
      let left := interpret first Reference state
      let right := interpret second Reference left.val
      ⟨right.val.mapHistory (fun history =>
        (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))),
        (right.val.mapHistory_mass _).trans (right.property.trans left.property)⟩
  | .branch input body => fun state =>
      let read := fun value => value.1.read input
      let selected := fun value part =>
        (interpret (body value) Reference part).val.mapHistory
          (fun history => (history.1, (history.2.1, ⟨value, history.2.2⟩)))
      have selectedMass : ∀ value part, (selected value part).mass = part.mass := by
        intro value part
        exact (State.mapHistory_mass _ _).trans
          (interpret (body value) Reference part).property
      ⟨runSelected state read selected selectedMass,
        runSelected_mass state read selected selectedMass⟩
  | .iterate count body => repeatPreserving (interpret body Reference) count
  | .workspace _ctx key shape fresh body => fun state =>
      let extended := state.pushWorkspace key shape fresh
      let result := interpret body Reference extended
      ⟨State.popWorkspace key shape fresh result.val,
        (State.popWorkspace_mass key shape fresh result.val).trans
          (result.property.trans (state.pushWorkspace_mass key shape fresh))⟩
termination_by structural code

end

end QuantumAlg.Execution

namespace QuantumAlg.Circuit

noncomputable section

/-- The final state and actual path record are obtained from the unique interpreter. -/
public def execute {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State pre Reference (model.HiddenState × H)) :
    Execution.State post Reference (model.HiddenState × (H × code.Path)) :=
  (Execution.interpret code Reference state).val

/-- Every finite circuit preserves mass, including on arbitrary external reference inputs. -/
theorem execute_mass {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State pre Reference (model.HiddenState × H)) :
    (code.execute Reference state).mass = state.mass :=
  (Execution.interpret code Reference state).property

end

end QuantumAlg.Circuit
