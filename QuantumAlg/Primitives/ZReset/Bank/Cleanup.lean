/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank.State
import all QuantumAlg.Core.Execution.Pure.Selection
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Physical restart of an actual fully owned bank reset

The fixed zero seed is chosen before execution. The certificate quantifies
over every external reference, prior history, incoming state and complete
output record. The required nonempty and all-owned layout conditions are
explicit; resetting a borrowed quantum target cannot establish restoration.
-/

namespace QuantumAlg.ZReset.Bank

noncomputable section

open Execution

variable {allowAllocation : Bool} {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {services : ClassicalOracleModel}
  {environment : (ExecutionModel.quantum AlgorithmGate.model oracles .empty services).Environment}
  (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
  (scratch : CWriteRef ctx (.finite 2)) (operations : ClassicalOpModel)

/-- Every complete actual reset record has the same predetermined owned zero seed. -/
lemma zResetBank_reinitializedAt (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.ReinitializedAt
      (code (allowAllocation := allowAllocation) (oracles := oracles)
        qubits scratch operations services)
      ⟨environment.quantum, environment.classical⟩
      (ctx.quantumLayout.restrictSelectedBasis ctx.borrowedSelectionᶜ
        ctx.quantumLayout.zeroLabel) := by
  have empty : ctx.borrowedSelection = ∅ := by
    ext wire
    simp [RuntimeCtx.mem_borrowedSelection, noBorrowed]
  have all : ctx.borrowedSelectionᶜ = Finset.univ := by simp [empty]
  unfold Circuit.ReinitializedAt
  rw [all]
  intro Reference History _ state record
  exact StatePromise.pureKet_fullSelection_of_localMarginal ctx.quantumLayout
    (((code (allowAllocation := allowAllocation) (oracles := oracles)
      qubits scratch operations services).execute
        ⟨environment.quantum, environment.classical⟩ Reference state).block record)
    ctx.quantumLayout.zeroLabel
    (zResetBank_block_pure (allowAllocation := allowAllocation)
      qubits scratch operations state record)

/-- The actual nonempty all-owned bank reset measures, restores and has one fixed seed. -/
lemma zResetBank_restartCleanup (positive : 0 < ctx.systemCount)
    (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.RestartCleanup
      (code (allowAllocation := allowAllocation) (oracles := oracles)
        qubits scratch operations services) ⟨environment.quantum, environment.classical⟩ where
  measured := zResetBank_measured (allowAllocation := allowAllocation)
    qubits scratch operations positive
  restores := by
    intro Reference History _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (code (allowAllocation := allowAllocation) (oracles := oracles)
        qubits scratch operations services)
          ⟨environment.quantum, environment.classical⟩ noBorrowed Reference state
  reinitialized := ⟨ctx.quantumLayout.restrictSelectedBasis ctx.borrowedSelectionᶜ
    ctx.quantumLayout.zeroLabel,
    zResetBank_reinitializedAt (allowAllocation := allowAllocation)
      qubits scratch operations noBorrowed⟩

end

end QuantumAlg.ZReset.Bank
