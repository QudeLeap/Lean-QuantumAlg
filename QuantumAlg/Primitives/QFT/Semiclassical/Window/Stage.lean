/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Program
import all QuantumAlg.Core.Execution.Measured.Stage
import all QuantumAlg.Core.Execution.Store.Blocks

/-!
# Complete stored blocks of the real measured and corrected window head

Every original classical/service/history block reaching the final store is
retained. The same actual MZ outcome selects the tail phases and native X.
The complete original physical context and external reference remain present.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

def nativeStageKraus (ports : Ports ctx totalBits (active + 1))
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (outcome : Fin (ctx.quantumLayout.wire (ports.wires 0)).dimension) :
    HilbertOperator (ctx.register.prod Reference) :=
  (UnitaryOperator.prodTensor
    ((afterHead ports (.finite outcome)).matrix environment) (1 : UnitaryOperator Reference) :
      HilbertOperator (ctx.register.prod Reference)) *
        ZMeasurement.projector (R := ctx.register.prod Reference)
          (fun basis => basis.1 (ports.wires 0)) outcome *
          (UnitaryOperator.prodTensor
            ((Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp (ports.wires 0)
              (ports.qubits 0)).matrix environment) (1 : UnitaryOperator Reference) :
                HilbertOperator (ctx.register.prod Reference))

/-- Actual H/MZ/selected phase-and-X has its exact complete retained-store Kraus sum. -/
lemma window_stage_store_matrix (ports : Ports ctx totalBits (active + 1))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (ExecutionState.filterClassical
      ((stage ports).execute environment Reference state)
        (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ outcome : Fin (ctx.quantumLayout.wire (ports.wires 0)).dimension,
          if original.1.write (ports.measuredOutput 0) (.finite outcome) = stored then
            nativeStageKraus ports environment.quantum Reference outcome *
              (state.block original).matrix *
                (nativeStageKraus ports environment.quantum Reference outcome).conjTranspose
          else 0 := by
  unfold stage nativeStageKraus
  exact Circuit.unitary_measureZ_selected_store_matrix
    (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := operations) (services := services)
    (Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp (ports.wires 0) (ports.qubits 0))
    (ports.wires 0) (ports.measuredOutput 0) (afterHead ports) environment state stored

/-- The next actual head consumes the real preceding corrected state, without a new bank. -/
lemma window_readout_succ_store (ports : Ports ctx totalBits (active + 1))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (ExecutionState.filterClassical
      ((readout (active + 1) ports).execute environment Reference state)
        (fun entry => entry.1 = stored)).quantumMarginal =
      (ExecutionState.filterClassical
        ((readout active ports.tail).execute environment Reference
          ((stage ports).execute environment Reference state))
        (fun entry => entry.1 = stored)).quantumMarginal :=
  Circuit.seq_store_marginal (stage ports) (readout active ports.tail) environment state stored

/-- The real previous-cell phase word feeds the same physical measured recursion. -/
lemma window_inverseCode_store (ports : Ports ctx totalBits active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (ExecutionState.filterClassical
      ((inverseCode ports).execute environment Reference state)
        (fun entry => entry.1 = stored)).quantumMarginal =
      (ExecutionState.filterClassical
        ((readout active ports).execute environment Reference
          ((priorFeedback ports (List.finRange active)).execute environment Reference state))
        (fun entry => entry.1 = stored)).quantumMarginal :=
  Circuit.seq_store_marginal (priorFeedback ports (List.finRange active)) (readout active ports)
    environment state stored

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
