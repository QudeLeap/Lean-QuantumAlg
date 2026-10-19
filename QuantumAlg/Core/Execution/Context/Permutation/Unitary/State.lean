/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Permutation.State
import all QuantumAlg.Core.Execution.Context.Permutation.Unitary
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.Interpret.Laws

/-!
# Complete unitary execution under entry permutation

The same actual unitary instruction commutes with the full store and quantum
coordinate bijections. Its joint action retains an arbitrary external reference
and each complete classical block, including correlations with the quantum input.
-/

namespace QuantumAlg.Execution.ContextPermutation

noncomputable section

variable {allowAllocation : Bool}

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {source target : RuntimeCtx .quantum}
  (same : source.entries.Perm target.entries)
  (program : UnitaryCircuit gates oracles source.quantumLayout)
  (environment : (ExecutionModel.quantum gates oracles operations services).Environment)

/-- The complete joint operator has exactly the corresponding reference coordinates. -/
lemma unitary_referenceBasis (Reference : Register) :
    UnitaryOperator.reindex (referenceBasis same Reference)
      (UnitaryOperator.prodTensor (program.matrix environment.quantum)
        (1 : UnitaryOperator Reference)) =
        UnitaryOperator.prodTensor ((unitaryProgram same program).matrix environment.quantum)
          (1 : UnitaryOperator Reference) := by
  apply Subtype.ext
  funext row column
  exact (unitaryProgram_joint_entry same program environment.quantum Reference
    row.1 column.1 row.2 column.2).symm

private lemma density_naturality {Reference : Register}
    (density : DensityOperator (Register.prod source.register Reference)) :
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (program.matrix environment.quantum)
        (1 : UnitaryOperator Reference)) density).reindex
        (referenceBasis same Reference) =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor ((unitaryProgram same program).matrix environment.quantum)
          (1 : UnitaryOperator Reference))
        (density.reindex (referenceBasis same Reference)) :=
  (DensityOperator.applyUnitary_reindex
    (UnitaryOperator.prodTensor (program.matrix environment.quantum)
      (1 : UnitaryOperator Reference)) density
    (referenceBasis same Reference)).trans
      (congrArg (fun operator => DensityOperator.applyUnitary operator
        (density.reindex (referenceBasis same Reference)))
        (unitary_referenceBasis same program environment Reference))

/-- Full unitary execution preserves the service state in the same permuted coordinates. -/
lemma state_unitary {Reference : Register} {H : Type} [Fintype H]
    (original : State source Reference (services.HiddenState × H)) :
    state same ((Circuit.unitary
        (allowAllocation := allowAllocation)
        (operations := operations) (classicalOracles := services)
      program).execute environment Reference original) =
      (Circuit.unitary
          (allowAllocation := allowAllocation)
          (operations := operations) (classicalOracles := services)
        (unitaryProgram same program)).execute environment Reference (state same original) := by
  have block_eq {K : Type} [Fintype K] (value : State source Reference K)
      (stored : Store target) (history : K) :
      (state same value).block (stored, history) =
        (value.block (store same.symm stored, history)).reindex
          (referenceBasis same Reference) := by
    apply DensityOperator.ext
    ext row column
    exact state_entry same value (stored, history) row column
  apply ExecutionState.ext
  rintro ⟨stored, hidden, history, path⟩
  cases path
  rw [block_eq]
  change (((Circuit.unitary
      (allowAllocation := allowAllocation)
      (operations := operations) (classicalOracles := services)
    program).execute environment Reference original).block
    (store same.symm stored, (hidden, (history, ())))).reindex
      (referenceBasis same Reference) = _
  rw [Circuit.execute_unitary_block (allowAllocation := allowAllocation), density_naturality]
  rw [← block_eq original stored (hidden, history)]
  exact (Circuit.execute_unitary_block
      (allowAllocation := allowAllocation) (operations := operations) (services := services)
      (quantumEnvironment := environment)
    (state same original) (unitaryProgram same program) stored hidden history).symm

end

end QuantumAlg.Execution.ContextPermutation
