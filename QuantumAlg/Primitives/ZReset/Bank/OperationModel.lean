/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank.Semantics
import all QuantumAlg.Primitives.ZReset.Sequence.OperationModel
import all QuantumAlg.Primitives.ZReset.Frame

/-!
# Complete bank-reset semantics under an arbitrary classical operation grant

Reset contains no classical arithmetic or service call. The full execution,
including persistent service state, agrees after erasing only the mathematical
path record. The existing complete-reference and retained-read equations
therefore apply with any surrounding classical operation language.
-/

namespace QuantumAlg.ZReset.Bank

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {services : ClassicalOracleModel}
  {environment :
    (ExecutionModel.quantum AlgorithmGate.model oracles .empty services).Environment}
  (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
  (scratch : CWriteRef ctx (.finite 2))
  (operations : ClassicalOpModel)
  {Reference : Register} {History : Type} [Fintype History]
  (state : State ctx Reference
    ((ExecutionModel.quantum AlgorithmGate.model oracles .empty services).HiddenState × History))

/-- Changing the unused arithmetic grant preserves every output store and hidden-state block. -/
lemma code_execute_operationModel {allowAllocation : Bool} :
    ((code (allowAllocation := allowAllocation) (oracles := oracles) qubits scratch operations
        services).execute
      ⟨environment.quantum, environment.classical⟩
        Reference state).mapHistory (fun record => (record.1, record.2.1)) =
    ((code (allowAllocation := allowAllocation) (oracles := oracles) qubits scratch .empty
        services).execute
      ⟨environment.quantum, environment.classical⟩
        Reference state).mapHistory (fun record => (record.1, record.2.1)) :=
  sequence_execute_operationModel (allowAllocation := allowAllocation) (services := services)
    (implementations (oracles := oracles) qubits) (readouts qubits scratch) operations state

/-- The complete quantum-reference marginal is independent of the unused arithmetic grant. -/
lemma quantumMarginal_operationModel {allowAllocation : Bool} :
    ((code (allowAllocation := allowAllocation) (oracles := oracles) qubits scratch operations
        services).execute
      ⟨environment.quantum, environment.classical⟩ Reference state).quantumMarginal =
    ((code (allowAllocation := allowAllocation) (oracles := oracles) qubits scratch .empty
        services).execute
      ⟨environment.quantum, environment.classical⟩ Reference state).quantumMarginal := by
  have same := congrArg ExecutionState.quantumMarginal
    (code_execute_operationModel (environment := environment)
      (allowAllocation := allowAllocation) qubits scratch operations
        state)
  simpa only [State.mapHistory_quantumMarginal] using same

/-- Retained-read quantum-reference blocks are likewise independent of that grant. -/
lemma filteredMarginal_operationModel {allowAllocation : Bool} (predicate : Store ctx → Prop) :
    (((code (allowAllocation := allowAllocation) (oracles := oracles) qubits scratch operations
        services).execute
      ⟨environment.quantum, environment.classical⟩
        Reference state).filterClassical (fun entry => predicate entry.1)).quantumMarginal =
    (((code (allowAllocation := allowAllocation) (oracles := oracles) qubits scratch .empty
        services).execute
      ⟨environment.quantum, environment.classical⟩
        Reference state).filterClassical (fun entry => predicate entry.1)).quantumMarginal := by
  classical
  have same := congrArg
    (fun output : State ctx Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles .empty services).HiddenState ×
        History) =>
      (output.filterClassical (fun entry => predicate entry.1)).quantumMarginal)
    (code_execute_operationModel (environment := environment)
      (allowAllocation := allowAllocation) qubits scratch operations
        state)
  simpa only [State.mapHistory, filter_map,
    ExecutionState.mapClassical_quantumMarginal] using same

/-- Reset establishes zero with the unchanged reference marginal under any arithmetic grant. -/
lemma zResetBank_complete_entry_operationModel {allowAllocation : Bool}
    (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index) :
    ((code (allowAllocation := allowAllocation) (oracles := oracles) qubits scratch operations
        services).execute
      ⟨environment.quantum, environment.classical⟩
        Reference state).quantumMarginal.matrix (left, leftRef) (right, rightRef) =
      if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
        ∑ basis : ctx.register.Index,
          state.quantumMarginal.matrix (basis, leftRef) (basis, rightRef)
      else 0 := by
  rw [quantumMarginal_operationModel (allowAllocation := allowAllocation)]
  exact zResetBank_complete_entry (allowAllocation := allowAllocation) (services := services) qubits
      scratch state
    left right leftRef rightRef

/-- Earlier classical reads retain their joint reference blocks while the bank becomes zero. -/
lemma zResetBank_complete_read_entry_operationModel {allowAllocation : Bool} {shape : CShape}
    (observed : CInputRef ctx shape) (separate : scratch.key ∉ observed.storageKeys)
    (value : shape.Value)
    (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index) :
    (((code (allowAllocation := allowAllocation) (oracles := oracles) qubits scratch operations
        services).execute
      ⟨environment.quantum, environment.classical⟩ Reference state).filterClassical
        (fun entry => entry.1.read observed = value)).quantumMarginal.matrix
          (left, leftRef) (right, rightRef) =
      if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
        ∑ basis : ctx.register.Index,
          (state.filterClassical (fun entry => entry.1.read observed =
            value)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)
      else 0 := by
  have same := filteredMarginal_operationModel (environment := environment)
    (allowAllocation := allowAllocation) (services :=
      services) qubits scratch
    operations state (fun store => store.read observed = value)
  exact (congrArg (fun density : DensityOperator (Register.prod ctx.register Reference) =>
      density.matrix (left, leftRef) (right, rightRef)) same).trans
    (zResetBank_complete_read_entry (allowAllocation := allowAllocation) (services := services)
        qubits scratch observed
      separate value state left right leftRef rightRef)

end

end QuantumAlg.ZReset.Bank
