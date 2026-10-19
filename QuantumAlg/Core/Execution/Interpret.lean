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
import all QuantumAlg.Core.Execution.Interpret.Preserving
import all QuantumAlg.Core.Execution.Composition.Embedding
import all QuantumAlg.Core.Execution.Composition.Parallel

/-!
# One interpretation of typed circuits

Every execution retains its actual classical store, complete quantum state,
external reference correlations, persistent classical oracle state and finite
path record. The oracle state is shared by every instruction and iteration;
only a granted query transition can change it. The mass equality
is proved during structural interpretation; the environment supplies query
interpretations, while the interpreter derives
the distribution, event trace and normalization certificate.

Classical branching first reads the current store, then executes the selected
body. Quantum control remains part of the pure unitary circuit supplied by a
unitary instruction.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

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
    {allowAllocation : Bool} (code : Circuit model pre post allowAllocation)
    (environment : model.Environment) (Reference : Register)
        :
    Preserving model.HiddenState pre post Reference code.Path :=
  match code with
  | .id _ctx => fun state => preserveService state ⟨state.skip, state.skip_mass⟩
  | .classical application => fun state =>
      preserveService state ⟨nativeStep application state, nativeStep_mass application state⟩
  | .classicalQuery application => fun state =>
      ⟨queryStep environment.classical application state,
        queryStep_mass environment.classical application state⟩
  | .unitary program => fun state =>
      preserveService state ⟨state.unitary (program.matrix environment.quantum),
          state.unitary_mass (program.matrix environment.quantum)⟩
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
      let left := interpret first environment Reference state
      let right := interpret second environment Reference left.val
      ⟨right.val.mapHistory (fun history =>
        (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))),
        (right.val.mapHistory_mass _).trans (right.property.trans left.property)⟩
  | .branch input body => fun state =>
      let read := fun value => value.1.read input
      let selected := fun value part =>
        (interpret (body value) environment Reference part).val.mapHistory
          (fun history => (history.1, (history.2.1, ⟨value, history.2.2⟩)))
      have selectedMass : ∀ value part, (selected value part).mass = part.mass := by
        intro value part
        exact (State.mapHistory_mass _ _).trans
          (interpret (body value) environment Reference part).property
      ⟨runSelected state read selected selectedMass,
        runSelected_mass state read selected selectedMass⟩
  | .iterate count body => repeatPreserving (interpret body environment Reference) count
  | .workspace _ctx key shape fresh body => fun state =>
      let extended := state.pushWorkspace key shape fresh
      let result := interpret body environment Reference extended
      ⟨State.popWorkspace key shape fresh result.val,
        (State.popWorkspace_mass key shape fresh result.val).trans
          (result.property.trans (state.pushWorkspace_mass key shape fresh))⟩
  | .embed placement body =>
      embedPreserving placement Reference
        (interpret body environment (Register.prod placement.frame.register Reference))
  | .parallelClassical (left := left) (right := right) join separate first second =>
      parallelPreserving join separate
        (interpret first ⟨environment.quantum, join.interpretationLeft environment.classical⟩
          (Register.prod right.register Reference))
        (interpret second ⟨environment.quantum, join.interpretationRight environment.classical⟩
          (Register.prod left.register Reference))
  | .parallelQuantum (left := left) (right := right) join separate first second =>
      parallelPreserving join separate
        (interpret first ⟨environment.quantum, join.interpretationLeft environment.classical⟩
          (Register.prod right.register Reference))
        (interpret second ⟨environment.quantum, join.interpretationRight environment.classical⟩
          (Register.prod left.register Reference))
termination_by structural code

end

end QuantumAlg.Execution

namespace QuantumAlg.Circuit

noncomputable section

/-- The final state and actual path record are obtained from the unique interpreter. -/
public def execute {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {allowAllocation : Bool} (code : Circuit model pre post allowAllocation)
    (environment : model.Environment) (Reference : Register)
        {H : Type} [Fintype H]
    (state : Execution.State pre Reference (model.HiddenState × H)) :
    Execution.State post Reference (model.HiddenState × (H × code.Path)) :=
  (Execution.interpret code environment Reference state).val

/-- Every finite circuit preserves mass, including on arbitrary external reference inputs. -/
lemma execute_mass {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {allowAllocation : Bool} (code : Circuit model pre post allowAllocation)
    (environment : model.Environment) (Reference : Register)
        {H : Type} [Fintype H]
    (state : Execution.State pre Reference (model.HiddenState × H)) :
    (code.execute environment Reference state).mass = state.mass :=
  (Execution.interpret code environment Reference state).property

end

end QuantumAlg.Circuit
