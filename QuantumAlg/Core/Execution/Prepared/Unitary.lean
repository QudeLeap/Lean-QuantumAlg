/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Execution.Reference.Preparation
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.Unitary.Local

/-!
# Exact joint state after preparation and unitary execution

The mathematical target tensors a fresh pure state with the entire incoming
context and reference, then applies the specified unitary. The actual
zero-preparation/unitary sequence realizes its corresponding canonical-zero
joint density operator. The allocation bridge uses the new physical wire
records, and no caller initialization or factorization premise is needed.

The same allocation and execution laws apply to every physical context and
arbitrary external reference. No initialization is imposed on existing systems.
-/

namespace QuantumAlg.Execution

noncomputable section


local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {ctx : RuntimeCtx .quantum} {systemCount : Nat}

/-- Independently tensor a fresh pure word with the complete incoming quantum state. -/
def preparedDensity (key : StorageKey) (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) (Reference : Register)
    (input : DensityOperator (Register.prod ctx.register Reference)) :
    DensityOperator
      (Register.prod (ctx.addOwnedLayout key layout fresh disjoint).register Reference) :=
  DensityOperator.reindex (Execution.prependPrepared input prepared)
    (prepareContextBasisEquiv ctx Reference key layout fresh disjoint)

theorem preparedDensity_mass (key : StorageKey) (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) (Reference : Register)
    (input : DensityOperator (Register.prod ctx.register Reference)) :
    (preparedDensity key layout fresh disjoint prepared Reference input).mass = input.mass := by
  rw [preparedDensity, DensityOperator.reindex_mass, Execution.prependPrepared_mass]

/-- The actual preparation context has the independent complete joint density. -/
theorem prepareContext_quantumMarginal_eq_preparedDensity
    {C : Type} [Fintype C] {Reference : Register}
    (state : ExecutionState C (Register.prod ctx.register Reference))
    (key : StorageKey) (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) :
    (prepareContext state key layout fresh disjoint prepared).quantumMarginal =
      preparedDensity key layout fresh disjoint prepared Reference state.quantumMarginal := by
  apply DensityOperator.ext
  ext row column
  obtain ⟨⟨newRow, oldRow⟩, rfl⟩ :=
    (prepareContextBasisEquiv ctx Reference key layout fresh disjoint).surjective row
  obtain ⟨⟨newColumn, oldColumn⟩, rfl⟩ :=
    (prepareContextBasisEquiv ctx Reference key layout fresh disjoint).surjective column
  rw [prepareContext_quantumMarginal_joined_entry, preparedDensity,
    DensityOperator.reindex_entry]
  simp only [Equiv.symm_apply_apply]
  rfl

/-- The actual zero-preparation/unitary run gives the independent joint tensor/unitary target. -/
theorem preparedUnitary_finalState_quantumMarginal
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel} (key : StorageKey)
    (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (body : UnitaryCircuit gates oracles
      (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout)
    {shape : CShape} (output : Output (ctx.addOwnedLayout key layout fresh disjoint) shape)
    (Reference : Register)
    (input : ExecutionState (Execution.Store ctx × services.HiddenState)
      (Register.prod ctx.register Reference)) :
    (({ code := (Circuit.prepareZero (gates := gates) (oracles := oracles)
          (operations := operations) (classicalOracles := services)
          ctx key layout fresh disjoint).seq (Circuit.unitary body), output := output } :
        AlgorithmRun (.quantum gates oracles operations services) ctx
          (ctx.addOwnedLayout key layout fresh disjoint) shape).finalState
          Reference input).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor body.matrix (1 : UnitaryOperator Reference))
        (preparedDensity key layout fresh disjoint (BasisPreparation.zero layout).normalized
          Reference input.quantumMarginal) := by
  rw [AlgorithmRun.finalState, ExecutionState.mapClassical_quantumMarginal,
    AlgorithmRun.execute, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.unitary_jointDensity, Circuit.execute_prepareZero, State.mapHistory_quantumMarginal,
    State.prepare_quantumMarginal,
    prepareContext_quantumMarginal_eq_preparedDensity, ExecutionState.mapClassical_quantumMarginal]

end

end QuantumAlg.Execution
