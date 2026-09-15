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

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {source target : RuntimeCtx .quantum}
  (same : source.entries.Perm target.entries) (program : UnitaryCircuit source.register)

/-- The complete joint operator has exactly the corresponding reference coordinates. -/
theorem unitary_referenceBasis (Reference : Register) :
    UnitaryOperator.reindex (referenceBasis same Reference)
      (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)) =
        UnitaryOperator.prodTensor (unitaryProgram same program).matrix
          (1 : UnitaryOperator Reference) := by
  apply Subtype.ext
  funext row column
  exact (unitaryProgram_joint_entry same program Reference row.1 column.1 row.2 column.2).symm

private theorem density_naturality {Reference : Register}
    (density : DensityOperator (Register.prod source.register Reference)) :
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)) density).reindex
        (referenceBasis same Reference) =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (unitaryProgram same program).matrix
          (1 : UnitaryOperator Reference))
        (density.reindex (referenceBasis same Reference)) :=
  (DensityOperator.applyUnitary_reindex
    (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)) density
    (referenceBasis same Reference)).trans
      (congrArg (fun operator => DensityOperator.applyUnitary operator
        (density.reindex (referenceBasis same Reference)))
        (unitary_referenceBasis same program Reference))

/-- Exact state coordinates preserve the actual unitary step and its unique path. -/
theorem state_unitary (placed : program.physical_idx = source.physicalIdx)
    {Reference : Register} {H : Type} [Fintype H] (original : State source Reference H) :
    state same (original.unitary program) =
      (state same original).unitary (unitaryProgram same program) := by
  have block_eq {K : Type} [Fintype K] (value : State source Reference K)
      (stored : Store target) (history : K) :
      (state same value).block (stored, history) =
        (value.block (store same.symm stored, history)).reindex
          (referenceBasis same Reference) := by
    apply DensityOperator.ext
    ext row column
    exact state_entry same value (stored, history) row column
  apply ExecutionState.ext
  rintro ⟨stored, history, path⟩
  cases path
  rw [block_eq]
  change (((Circuit.unitary program placed).execute Reference original).block
    (store same.symm stored, (history, ()))).reindex (referenceBasis same Reference) = _
  rw [Circuit.execute_unitary_block, density_naturality]
  rw [← block_eq original stored history]
  exact (Circuit.execute_unitary_block (state same original)
    (unitaryProgram same program) (unitaryProgram_physical same program placed)
    stored history).symm

end

end QuantumAlg.Execution.ContextPermutation
