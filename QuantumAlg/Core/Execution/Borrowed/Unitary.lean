/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.ComplementUnitary
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Borrowed restoration from exact complementary unitary action

The actual execution preserves the entire joint borrowed classical, quantum
and external-reference observation when its full operator factors as identity
on borrowed wires and a unitary on the remaining wires. The matrix argument
retains off-diagonal correlations [dW19, qcnotes.tex:5381,5405].
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace Execution

/-- Complementary unitary action preserves every borrowed classical block and its correlations. -/
theorem observeBorrowed_applyUnitary_complement {ctx : RuntimeCtx .quantum}
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference H) (operator : UnitaryOperator ctx.register)
    (complement : UnitaryOperator (ctx.quantumLayout.complementRegister ctx.borrowedSelection))
    (factorization :
      UnitaryOperator.reindex (ctx.quantumLayout.selectionBasisEquiv ctx.borrowedSelection)
        operator =
      UnitaryOperator.prodTensor
        (1 : UnitaryOperator (ctx.quantumLayout.selectedRegister ctx.borrowedSelection))
        complement) :
    observeBorrowed Reference
      (state.applyUnitary fun _ =>
        UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference)) =
    observeBorrowed Reference state := by
  apply ExecutionState.ext
  intro value
  rw [observeBorrowed_block, observeBorrowed_block]
  have regroup := ExecutionState.applyUnitary_mapClassical state
    (fun label : Store ctx × H => label.1.readBorrowedClassical)
    (fun _ : ctx.borrowedClassicalShape.Value =>
      UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference))
  rw [← regroup]
  simp only [ExecutionState.applyUnitary_block, RuntimeCtx.observeBorrowedWithReference]
  rw [DensityOperator.observeSelectionWithReference_applyUnitary_complement
    ctx.quantumLayout ctx.borrowedSelection operator complement factorization]

end Execution

namespace Circuit

/-- The interpreter restores all borrowed resources jointly when its matrix has exact
identity action on the borrowed subsystem. This requires no product-state input premise. -/
theorem borrowedRestored_unitary_complement {ctx : RuntimeCtx .quantum}
    {Reference : Register} {H : Type} [Fintype H]
    (program : UnitaryCircuit ctx.register) (placed : program.physical_idx = ctx.physicalIdx)
    (complement : UnitaryOperator (ctx.quantumLayout.complementRegister ctx.borrowedSelection))
    (factorization :
      UnitaryOperator.reindex (ctx.quantumLayout.selectionBasisEquiv ctx.borrowedSelection)
        program.matrix =
      UnitaryOperator.prodTensor
        (1 : UnitaryOperator (ctx.quantumLayout.selectedRegister ctx.borrowedSelection))
        complement)
    (state : Execution.State ctx Reference H) :
    (Circuit.unitary program placed).BorrowedRestored Reference state
      ((Circuit.unitary program placed).execute Reference state) := by
  rw [BorrowedRestored, Execution.observeBorrowedAfter_sameContext, execute_unitary]
  apply ExecutionState.ext
  intro value
  simp only [Execution.observeBorrowed_block, Execution.State.unitary,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact congrArg
    (fun observed : ExecutionState ctx.borrowedClassicalShape.Value
      (Register.prod ctx.borrowedQuantumLayout.register Reference) => observed.block value)
    (Execution.observeBorrowed_applyUnitary_complement state program.matrix complement
      factorization)

end Circuit

end

end QuantumAlg
