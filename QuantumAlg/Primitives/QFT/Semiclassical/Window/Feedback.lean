/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Ports
import all QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.PhaseOperator
import all QuantumAlg.Core.Execution.Selected.Store

/-!
# Actual same-stream feedback from earlier windows

The original retained cell selects a placed native negative Fourier phase.
Future cells and the other stream contribute the identity circuit. The
interpreter equations retain complete stores, history and arbitrary reference;
no outcome is supplied as a mathematical replacement for a stored read.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}

def phaseProgram (ports : Ports ctx totalBits active) (previous : BitPosition totalBits)
    (current : Fin active) (value : CShape.Value (.finite 2)) :
    UnitaryCircuit AlgorithmGate.model oracles ctx.quantumLayout :=
  match value with
  | .finite bit => if bit.val = 1 then
      Gate.singleQubitAt ctx.quantumLayout oracles
        (phaseGateOp (-Source.phaseAngle ((ports.position current).val - previous.2.val - 1)))
        (ports.wires current) (ports.qubits current)
    else UnitaryCircuit.identity AlgorithmGate.model oracles ctx.quantumLayout

/-- One real retained result chooses the actual native phase word. -/
def selected (ports : Ports ctx totalBits active) (previous : BitPosition totalBits)
    (current : Fin active) :
    Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false :=
  .branch (.storage (ports.results previous).toCStorageRef)
    (fun value => .unitary (phaseProgram ports previous current value))

def one (ports : Ports ctx totalBits active) (previous : BitPosition totalBits)
    (current : Fin active) :
    Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false :=
  if ports.past previous then
    selected (oracles := oracles) (operations := operations) (services := services)
      ports previous current
  else Circuit.id (model := .quantum AlgorithmGate.model oracles operations services)
    (allowAllocation := false) ctx

lemma one_of_past (ports : Ports ctx totalBits active) (previous : BitPosition totalBits)
    (current : Fin active) (prior : ports.past previous) :
    one (oracles := oracles) (operations := operations) (services := services)
        ports previous current = selected ports previous current := by
  simp only [one, if_pos prior]

lemma one_of_other_stream (ports : Ports ctx totalBits active)
    (previous : BitPosition totalBits) (current : Fin active)
    (other : previous.1 ≠ ports.stream) :
    one (oracles := oracles) (operations := operations) (services := services)
        ports previous current =
      Circuit.id (model := .quantum AlgorithmGate.model oracles operations services)
        (allowAllocation := false) ctx := by
  simp only [one, Ports.past, other, false_and, ↓reduceIte]

lemma one_of_future (ports : Ports ctx totalBits active) (previous : BitPosition totalBits)
    (current : Fin active) (future : ports.start ≤ previous.2.val) :
    one (oracles := oracles) (operations := operations) (services := services)
        ports previous current =
      Circuit.id (model := .quantum AlgorithmGate.model oracles operations services)
        (allowAllocation := false) ctx := by
  have excluded : ¬ports.past previous := fun prior => (Nat.not_lt_of_ge future) prior.2
  simp only [one, if_neg excluded]

/-- Exact history records the value read from that same actual retained cell. -/
lemma selected_execute (ports : Ports ctx totalBits active) (previous : BitPosition totalBits)
    (current : Fin active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    ((selected ports previous current).execute environment Reference state) =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        ((phaseProgram ports previous current
          (entry.1.read (.storage (ports.results previous).toCStorageRef))).matrix
            environment.quantum) (1 : UnitaryOperator Reference)).mapClassical
          (fun entry => (entry.1, (entry.2.1,
            (entry.2.2, ⟨entry.1.read (.storage (ports.results previous).toCStorageRef), ()⟩)))) :=
  Circuit.selectedUnitary_execute (.storage (ports.results previous).toCStorageRef)
    (phaseProgram ports previous current) environment state

/-- The full original store selects its native matrix on the entire reference-correlated block. -/
lemma selected_store_matrix (ports : Ports ctx totalBits active)
    (previous : BitPosition totalBits) (current : Fin active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (ExecutionState.filterClassical
      ((selected ports previous current).execute environment Reference state)
        (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      (DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor
          ((phaseProgram ports previous current
            (stored.read (.storage (ports.results previous).toCStorageRef))).matrix
              environment.quantum) (1 : UnitaryOperator Reference))
        (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal).matrix :=
  Circuit.selectedUnitary_store_matrix (.storage (ports.results previous).toCStorageRef)
    (phaseProgram ports previous current) environment state stored

/-- The selected phase charges precisely one native one-qubit event or the empty trace. -/
lemma phaseProgram_eventTrace (ports : Ports ctx totalBits active)
    (previous : BitPosition totalBits) (current : Fin active)
    (value : CShape.Value (.finite 2)) :
    (phaseProgram (oracles := oracles) ports previous current value).eventTrace
        operations services =
      if value.toFin.val = 1 then [.gate .singleQubit] else [] := by
  cases value with
  | finite bit =>
      dsimp only [phaseProgram, CShape.Value.toFin]
      by_cases selected : bit.val = 1
      · simp only [selected, ↓reduceIte]
        rfl
      · simp only [selected, ↓reduceIte]
        rfl

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback
