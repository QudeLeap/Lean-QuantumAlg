/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.ZReset.Bank.Semantics
public import QuantumAlg.Core.Execution.Pure.Point
import all QuantumAlg.Primitives.ZReset.Bank
import all QuantumAlg.Primitives.ZReset.Bank.Semantics
import all QuantumAlg.Primitives.ZReset.Sequence.OperationModel
import all QuantumAlg.Core.Execution.Pure.Point
import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Core.Base.State.Density

/-!
# Actual bank reset at arbitrary input mass

The real measurement-and-correction sequence establishes the pure zero
marginal at the incoming mass, including mass zero. An additional classical
operation grant changes no quantum state. The guarantee requires no incoming
seed, independence assumption or caller-provided reset certificate.
-/

namespace QuantumAlg.ZReset.Bank

noncomputable section

variable {services : ClassicalOracleModel}

open Execution

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {environment :
    (ExecutionModel.quantum AlgorithmGate.model oracles .empty services).Environment}

/-- The actual reset has pure zero local density at its real subnormalized mass. -/
lemma zResetBank_localDensity_pure {allowAllocation : Bool}
    (qubits : ∀ wire : Fin ctx.systemCount, (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) (operations : ClassicalOpModel)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles operations services).HiddenState ×
        History)) :
    (StatePromise.pure
      (NormalizedVector.ket (R := ctx.register) ctx.quantumLayout.zeroLabel)).Holds
        ((code (allowAllocation := allowAllocation) (services := services) (oracles := oracles)
            qubits scratch operations).execute
      ⟨environment.quantum, environment.classical⟩
        Reference state).quantumMarginal.marginalLeft := by
  have erased := congrArg ExecutionState.quantumMarginal
    (ZReset.sequence_execute_operationModel (environment := environment)
      (allowAllocation := allowAllocation) (implementations
        (oracles := oracles) qubits)
      (readouts qubits scratch) operations state)
  simp only [State.mapHistory_quantumMarginal] at erased
  apply StatePromise.statePromise_pureKet_of_row_support
  intro row different column
  rw [DensityOperator.marginalLeft_matrix]
  apply Finset.sum_eq_zero
  intro reference _
  change ((ZReset.sequence (allowAllocation := allowAllocation) (services := services)
      (implementations (oracles := oracles) qubits)
    (readouts qubits scratch) operations).execute
      ⟨environment.quantum, environment.classical⟩ Reference state).quantumMarginal.matrix
      (row, reference) (column, reference) = 0
  rw [erased]
  change ((code (allowAllocation := allowAllocation) (services := services) (oracles := oracles)
      qubits scratch).execute
      ⟨environment.quantum, environment.classical⟩ Reference
    state).quantumMarginal.matrix
    (row, reference) (column, reference) = 0
  rw [zResetBank_complete_entry (allowAllocation := allowAllocation)]
  simp only [different, false_and, if_false]

end

end QuantumAlg.ZReset.Bank
