/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank.Scope
import all QuantumAlg.Primitives.ZReset.Sequence.OperationModel
import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Core.Execution.Reference.Observation

/-!
# Classical-language independence of scoped bank reset

The same allocated scratch cell, physical measurements, selected X gates and
scratch-cell release execute in any surrounding classical operation model.
The complete final store, service state and quantum-reference blocks agree
after the mathematical reset path is erased.
-/

namespace QuantumAlg.ZReset.BankScope

open Execution

noncomputable section

variable {services : ClassicalOracleModel}

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {environment : (ExecutionModel.quantum AlgorithmGate.model oracles .empty services).Environment}

/-- Adding a classical operation grant cannot change the actual scoped bank
reset's final state when only its path label is erased. -/
lemma code_execute_operationModel
    (qubits : ∀ wire : Fin ctx.systemCount,
      (ctx.quantumLayout.wire wire).dimension = 2)
    (operations : ClassicalOpModel) {Reference : Register} {History : Type}
    [Fintype History]
    (state : State ctx Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles .empty services).HiddenState × History))
        :
    ((code (services := services) (oracles := oracles) qubits operations).execute
      ⟨environment.quantum, environment.classical⟩ Reference
      state).mapHistory
      (fun record => (record.1, record.2.1)) =
    ((code (services := services) (oracles := oracles) qubits).execute
      ⟨environment.quantum, environment.classical⟩ Reference state).mapHistory
      (fun record => (record.1, record.2.1)) := by
  change (State.popWorkspace ctx.canonicalFreshKey (.finite 2)
      ctx.canonicalFreshKey_fresh
      ((Bank.code (services := services) (oracles := oracles) (zResetBankScope_work_qubits qubits)
        (scratch ctx) operations).execute ⟨environment.quantum, environment.classical⟩ Reference
        (state.pushWorkspace ctx.canonicalFreshKey (.finite 2)
          ctx.canonicalFreshKey_fresh))).mapHistory _ =
    (State.popWorkspace ctx.canonicalFreshKey (.finite 2)
      ctx.canonicalFreshKey_fresh
      ((Bank.code (services := services) (oracles := oracles) (zResetBankScope_work_qubits qubits)
        (scratch ctx)).execute ⟨environment.quantum, environment.classical⟩ Reference
        (state.pushWorkspace ctx.canonicalFreshKey (.finite 2)
          ctx.canonicalFreshKey_fresh))).mapHistory _
  erw [← State.mapHistory_popWorkspace, ← State.mapHistory_popWorkspace]
  exact congrArg (State.popWorkspace ctx.canonicalFreshKey (.finite 2)
      ctx.canonicalFreshKey_fresh)
    (ZReset.sequence_execute_operationModel
      (Bank.implementations (oracles := oracles) (zResetBankScope_work_qubits qubits))
      (Bank.readouts (zResetBankScope_work_qubits qubits) (scratch ctx))
      operations (state.pushWorkspace ctx.canonicalFreshKey (.finite 2)
        ctx.canonicalFreshKey_fresh))

/-- Every store-weighted reference observation is identical for the actual
scoped reset under either classical operation grant. -/
lemma referenceFiberSum_operationModel
    (qubits : ∀ wire : Fin ctx.systemCount,
      (ctx.quantumLayout.wire wire).dimension = 2)
    (operations : ClassicalOpModel) {Reference : Register} {History : Type}
    [Fintype History]
    (state : State ctx Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles .empty services).HiddenState × History))
    (weight : Store ctx → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code (services := services) (oracles := oracles) qubits operations).execute
        ⟨environment.quantum, environment.classical⟩ Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
    ExecutionState.referenceFiberSum
      ((code (services := services) (oracles := oracles) qubits).execute
        ⟨environment.quantum, environment.classical⟩ Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef := by
  have erased := congrArg
    (fun output : State ctx Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles .empty services).HiddenState × History)
        =>
      ExecutionState.referenceFiberSum output
        (fun entry _ => weight entry.1) leftRef rightRef)
    (code_execute_operationModel (environment := environment) qubits operations state)
  simpa only [State.mapHistory, ExecutionState.referenceFiberSum_mapClassical]
    using erased

end

end QuantumAlg.ZReset.BankScope
