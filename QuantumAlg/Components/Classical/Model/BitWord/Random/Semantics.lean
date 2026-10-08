/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord.Random
public import QuantumAlg.Core.Execution.State
public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Core.Execution.Random.Kernel.Map
public import QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Components.Classical.Model.BitWord.Random
import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Random.Kernel

/-!
# Exact state semantics of selected uniform random-bit generation

The real lexical unit operand is released after the actual native sampling leaf.
The generated bit string is written to the original output, with that same
value represented in the circuit's actual path. Every prior joint block and
shared hidden service state retains its original correlations and sample weight.
-/

namespace QuantumAlg.BitWord.Random

open Execution

noncomputable section

variable {execution : ExecutionModel} [Selected execution]
  {ctx : RuntimeCtx execution.kind} {width : Nat}

open scoped Classical in
/-- The actual sampled value drives both the original output write and the real returned path. -/
public theorem randomCode_execute (output : CWriteRef ctx (.bits width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (execution.HiddenState × History)) :
    (code (execution := execution) output).execute Reference state =
      (kernelChoice state (fun _ => uniformBits width)).mapClassical (fun entry =>
        (entry.1.1.write output entry.2,
          (entry.1.2.1, (entry.1.2.2,
            (pathEquiv (execution := execution) output).symm entry.2)))) := by
  classical
  cases execution with
  | classical operations services =>
      have same := Selected.operations_eq (execution := .classical operations services)
      change operations = BitWord.model at same
      cases same
      dsimp only [code]
      rw [Circuit.execute_workspace, Circuit.execute_classical]
      change State.popWorkspace ctx.canonicalFreshKey .unit
        ctx.runtimeCtx_canonicalFreshKey_fresh
        ((kernelChoice (state.pushWorkspace ctx.canonicalFreshKey .unit
          ctx.runtimeCtx_canonicalFreshKey_fresh) (fun _ => uniformBits width)).mapClassical
          (fun entry =>
            (entry.1.1.write (output.underWorkspace ctx.canonicalFreshKey .unit
              ctx.runtimeCtx_canonicalFreshKey_fresh) entry.2,
              (entry.1.2.1, (entry.1.2.2, entry.2))))) =
        (kernelChoice state (fun _ => uniformBits width)).mapClassical
          (fun entry => (entry.1.1.write output entry.2,
            (entry.1.2.1, (entry.1.2.2, entry.2))))
      rw [State.state_popWorkspace_as_mapClassical,
        State.state_pushWorkspace_as_mapClassical]
      erw [kernelChoice_mapClassical (R := Register.prod ctx.register Reference)
        (afterMap := Classical.decEq _)]
      erw [ExecutionState.executionState_mapClassical_comp_instances
          (R := Register.prod ctx.register Reference) (result := inferInstance),
        ExecutionState.executionState_mapClassical_comp_instances
          (R := Register.prod ctx.register Reference) (result := inferInstance)]
      apply ExecutionState.executionState_mapClassical_congr
      funext entry
      rfl
  | quantum gates oracles operations services =>
      have same := Selected.operations_eq (execution := .quantum gates oracles operations services)
      change operations = BitWord.model at same
      cases same
      dsimp only [code]
      rw [Circuit.execute_workspace, Circuit.execute_classical]
      change State.popWorkspace ctx.canonicalFreshKey .unit
        ctx.runtimeCtx_canonicalFreshKey_fresh
        ((kernelChoice (state.pushWorkspace ctx.canonicalFreshKey .unit
          ctx.runtimeCtx_canonicalFreshKey_fresh) (fun _ => uniformBits width)).mapClassical
          (fun entry =>
            (entry.1.1.write (output.underWorkspace ctx.canonicalFreshKey .unit
              ctx.runtimeCtx_canonicalFreshKey_fresh) entry.2,
              (entry.1.2.1, (entry.1.2.2, entry.2))))) =
        (kernelChoice state (fun _ => uniformBits width)).mapClassical
          (fun entry => (entry.1.1.write output entry.2,
            (entry.1.2.1, (entry.1.2.2, entry.2))))
      rw [State.state_popWorkspace_as_mapClassical,
        State.state_pushWorkspace_as_mapClassical]
      erw [kernelChoice_mapClassical (R := Register.prod ctx.register Reference)
        (afterMap := Classical.decEq _)]
      erw [ExecutionState.executionState_mapClassical_comp_instances
          (R := Register.prod ctx.register Reference) (result := inferInstance),
        ExecutionState.executionState_mapClassical_comp_instances
          (R := Register.prod ctx.register Reference) (result := inferInstance)]
      apply ExecutionState.executionState_mapClassical_congr
      funext entry
      rfl

open scoped Classical in
/-- Every output block is the complete weighted sum of its actual source and random outcome. -/
public theorem randomCode_block_matrix (output : CWriteRef ctx (.bits width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (execution.HiddenState × History))
    (result : Store ctx × (execution.HiddenState ×
      (History × (code (execution := execution) output).Path))) :
    (((code (execution := execution) output).execute Reference state).block result).matrix =
      ∑ entry : (Store ctx × (execution.HiddenState × History)) × CShape.Value (.bits width),
        if (entry.1.1.write output entry.2,
            (entry.1.2.1, (entry.1.2.2,
              (pathEquiv (execution := execution) output).symm entry.2))) = result then
          (uniformBits width entry.2).toReal • (state.block entry.1).matrix else 0 := by
  classical
  rw [randomCode_execute, ExecutionState.mapClassical_block_matrix]
  apply Finset.sum_congr rfl
  intro entry _
  exact congrArg (fun matrix => if (entry.1.1.write output entry.2,
    (entry.1.2.1, (entry.1.2.2,
      (pathEquiv (execution := execution) output).symm entry.2))) = result then matrix else 0)
    (kernelChoice_block_matrix state (fun _ => uniformBits width) entry.1 entry.2)

end

end QuantumAlg.BitWord.Random
