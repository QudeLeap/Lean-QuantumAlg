/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Quantum.Selection
public import QuantumAlg.Core.Execution.State.Promise
public import QuantumAlg.Core.Execution.Output
public import QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.State.Promise

/-!
# Independently specified output state observations

A requirement selects actual output wires and an actual classical observation.
The unit observation sums all classical results; a typed read conditions only
on the value actually stored. Execution histories are summed before checking
the promise, so an unobserved measurement does not acquire a spurious pure
conditional state.

Single-wire, multi-wire and full-layout selections specify marginal, joint and
complete states. Reference-aware targets also retain the external reference.
These requirements belong to the problem specification, not to the run.
-/

namespace QuantumAlg

/-- Closed output state promises with independently chosen observation scopes. -/
public inductive StateRequirement {kind : ProblemKind} (pre post : RuntimeCtx kind) : Type 1 where
  /-- Observe selected actual systems, summing their complement and the reference. -/
  | marginal (selection : Finset (Fin post.systemCount)) {shape : CShape}
      (read : OutputRead post shape)
      (target : ExecutionState (Execution.Store pre) pre.register →
        shape.Value → StatePromise (post.quantumLayout.selectedRegister selection))
  /-- Observe selected actual systems jointly with any external reference. -/
  | jointReference (selection : Finset (Fin post.systemCount)) {shape : CShape}
      (read : OutputRead post shape)
      (target : (Reference : Register) → Execution.Input pre Reference →
        shape.Value → StatePromise
          (Register.prod (post.quantumLayout.selectedRegister selection) Reference))

namespace StateRequirement

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {pre post : RuntimeCtx kind} {Reference : Register}

/-- Check the specification on blocks aggregated by its actual classical observation. -/
public def Holds (requirement : StateRequirement pre post) (input : Execution.Input pre Reference)
    (final : ExecutionState (Execution.Store post) (Register.prod post.register Reference)) :
    Prop :=
  match requirement with
  | .marginal selection read target =>
      let observed := final.mapClassical read.eval
      ∀ value, (target input.localState value).Holds
        (DensityOperator.observeSelection post.quantumLayout selection Reference
          (observed.block value))
  | .jointReference selection read target =>
      let observed := final.mapClassical read.eval
      ∀ value, (target Reference input value).Holds
        (DensityOperator.observeSelectionWithReference post.quantumLayout selection Reference
          (observed.block value))

/-- A constant marginal pure promise is checked on each actual output-read
block, after every unobserved classical path has been summed. -/
theorem marginal_pure_holds_iff
    (selection : Finset (Fin post.systemCount)) {shape : CShape}
    (read : OutputRead post shape)
    (target : NormalizedVector (post.quantumLayout.selectedRegister selection))
    (input : Execution.Input pre Reference)
    (final : ExecutionState (Execution.Store post) (Register.prod post.register Reference)) :
    (StateRequirement.marginal selection read
      (fun _ _ => StatePromise.pure target)).Holds input final ↔
      ∀ value, (StatePromise.pure target).Holds
        (DensityOperator.observeSelection post.quantumLayout selection Reference
          ((final.mapClassical read.eval).block value)) := Iff.rfl

/-- A dirty requirement omits state information while leaving its observed systems live. -/
theorem marginal_dirty_holds (selection : Finset (Fin post.systemCount)) {shape : CShape}
    (read : OutputRead post shape) (input : Execution.Input pre Reference)
    (final : ExecutionState (Execution.Store post) (Register.prod post.register Reference)) :
    (StateRequirement.marginal selection read (fun _ _ => .dirty)).Holds input final := by
  intro value
  exact StatePromise.holds_dirty _

/-- Omitting a joint promise does not assert restoration or remove any resource. -/
theorem jointReference_dirty_holds (selection : Finset (Fin post.systemCount))
    {shape : CShape} (read : OutputRead post shape) (input : Execution.Input pre Reference)
    (final : ExecutionState (Execution.Store post) (Register.prod post.register Reference)) :
    (StateRequirement.jointReference selection read (fun _ _ _ => .dirty)).Holds input final := by
  intro value
  exact StatePromise.holds_dirty _

end

end StateRequirement

end QuantumAlg
