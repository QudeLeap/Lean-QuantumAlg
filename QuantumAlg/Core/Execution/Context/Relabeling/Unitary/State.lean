/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Relabeling.State
import all QuantumAlg.Core.Execution.Context.Relabeling.Unitary
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.Interpret.Laws

/-!
# Complete unitary execution under injective placement

The same actual unitary instruction commutes with the full store and quantum
coordinate bijections. Its joint action retains an arbitrary external reference
and each complete classical block, including correlations with the quantum input.
-/

namespace QuantumAlg.Execution.ContextRelabeling

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {source : RuntimeCtx .quantum}
  (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
  (program : UnitaryCircuit source.register) (placed : program.physical_idx = source.physicalIdx)

/-- The complete joint operator has exactly the corresponding reference coordinates. -/
theorem unitary_referenceBasis (Reference : Register) :
    UnitaryOperator.reindex (referenceBasis (source := source) keys physical Reference)
      (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)) =
        UnitaryOperator.prodTensor (unitaryProgram source keys physical program placed).matrix
          (1 : UnitaryOperator Reference) := by
  apply Subtype.ext
  funext row column
  exact (unitaryProgram_joint_entry source keys physical program placed Reference
    row.1 column.1 row.2 column.2).symm

private theorem density_naturality {Reference : Register}
    (density : DensityOperator (Register.prod source.register Reference)) :
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)) density).reindex
        (referenceBasis (source := source) keys physical Reference) =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (unitaryProgram source keys physical program placed).matrix
          (1 : UnitaryOperator Reference))
        (density.reindex (referenceBasis (source := source) keys physical Reference)) :=
  (DensityOperator.applyUnitary_reindex
    (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)) density
    (referenceBasis (source := source) keys physical Reference)).trans
      (congrArg (fun operator => DensityOperator.applyUnitary operator
        (density.reindex (referenceBasis (source := source) keys physical Reference)))
        (unitary_referenceBasis keys physical program placed Reference))

/-- Exact state coordinates preserve the actual unitary step and its unique path. -/
theorem state_unitary
    {Reference : Register} {H : Type} [Fintype H] (original : State source Reference H) :
    state keys physical (original.unitary program) =
      (state keys physical original).unitary
        (unitaryProgram source keys physical program placed) := by
  have block_eq {K : Type} [Fintype K] (value : State source Reference K)
      (stored : Store (source.relabel keys physical)) (history : K) :
      (state keys physical value).block (stored, history) =
        (value.block ((storeEquiv keys physical source).symm stored, history)).reindex
          (referenceBasis (source := source) keys physical Reference) := by
    apply DensityOperator.ext
    ext row column
    exact state_entry keys physical value (stored, history) row column
  apply ExecutionState.ext
  rintro ⟨stored, history, path⟩
  cases path
  rw [block_eq]
  change (((Circuit.unitary program placed).execute Reference original).block
    ((storeEquiv keys physical source).symm stored, (history, ()))).reindex
      (referenceBasis (source := source) keys physical Reference) = _
  rw [Circuit.execute_unitary_block, density_naturality keys physical program placed]
  rw [← block_eq original stored history]
  exact (Circuit.execute_unitary_block (state keys physical original)
    (unitaryProgram source keys physical program placed)
    (unitaryProgram_physical source keys physical program placed)
    stored history).symm

end

end QuantumAlg.Execution.ContextRelabeling
