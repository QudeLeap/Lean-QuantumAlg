/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect
import all QuantumAlg.Core.Execution.Measurement.Readout.Effect

/-!
# Actual output probabilities for a prefix followed by qubit readout

The run executes its supplied prefix, measures the named wires into actual
finite result cells, and returns the structural vector of those cells. Its
complete Output lists every live storage key. The Boolean mask belongs only
to the mathematical event being tested on this real output distribution.

The existing interpreter and its exact original-store history determine all
probabilities. Once the prefix finishes, its full quantum marginal determines
every event on these newly written results. The prefix may contain classical
control, measurements, and allocation, with no restriction on its history.
-/

namespace QuantumAlg.AlgorithmRun

variable {allowAllocation allowLeft allowRight : Bool}

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {pre ctx : RuntimeCtx .quantum} {width : Nat}

/-- Execute a prefix and actual qubit readout, returning the complete finite-cell vector. -/
def qubitReadout
    (prior : Circuit (.quantum gates oracles operations services) pre ctx allowAllocation)
    (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2)) :
    AlgorithmRun (.quantum gates oracles operations services) pre ctx
      (.fixedVector width (.finite 2)) allowAllocation where
  code := .seq prior (.measurementSequence (QubitReadouts.readouts wires qubits cells))
  output := Output.all ctx (.read (QubitReadouts.input cells))

/-- Actual final readout events pair only with the prefix's full quantum marginal. -/
lemma qubitReadout_effectWeight
    (prior : Circuit (.quantum gates oracles operations services) pre ctx allowAllocation)
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (cells index).key)
    {Reference : Register}
    (input : ExecutionState (Store pre × services.HiddenState)
      (Register.prod pre.register Reference))
    (event : (Fin width → Bool) → Bool) :
    ((qubitReadout prior wires qubits cells).execute environment Reference input).effectWeight
        (fun record => if event (QubitReadouts.mask (record.1.read
          (QubitReadouts.input cells))) = true then
            Effect.one (Register.prod ctx.register Reference)
          else Effect.zero (Register.prod ctx.register Reference)) =
      (QubitReadouts.eventEffect wires event Reference).weight
        (prior.execute environment Reference
          (input.mapClassical
            (fun original => (original.1, (original.2, original.1))))).quantumMarginal := by
  unfold execute
  change ((Circuit.seq prior
    (Circuit.measurementSequence (QubitReadouts.readouts wires qubits cells))).execute
      environment Reference (input.mapClassical
        (fun original => (original.1, (original.2, original.1))))).effectWeight _ = _
  rw [Circuit.execute_seq]
  erw [State.effectWeight_mapHistory]
  exact QubitReadouts.measurement_eventEffectWeight wires qubits cells distinct
    environment _ event

/-- The real output PMF gives the same event weight, with its actual original-store history. -/
lemma qubitReadout_eventProbability
    (prior : Circuit (.quantum gates oracles operations services) pre ctx allowAllocation)
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (cells index).key)
    {Reference : Register} (input : Execution.OracleInput services pre Reference)
    (event : (Fin width → Bool) → Bool) :
    ((qubitReadout prior wires qubits cells).outputDistribution environment input).map
        (fun value => event (QubitReadouts.mask value)) true =
      ENNReal.ofReal ((QubitReadouts.eventEffect wires event Reference).weight
        (prior.execute environment Reference
          (input.state.mapClassical
            (fun original => (original.1, (original.2, original.1))))).quantumMarginal) := by
  rw [outputDistribution_event_eq_effectWeight]
  exact congrArg ENNReal.ofReal
    (qubitReadout_effectWeight prior environment wires qubits cells distinct input.state event)

/-- Different actual prefixes have equal readout probabilities when their full marginals agree. -/
lemma qubitReadout_eventProbability_eq_of_quantumMarginal_eq
    {leftGates rightGates : GateModel} {leftOracles rightOracles : OracleModel}
    {leftOperations rightOperations : ClassicalOpModel}
    {leftServices rightServices : ClassicalOracleModel}
    {leftPre rightPre : RuntimeCtx .quantum}
    (leftPrefix : Circuit (.quantum leftGates leftOracles leftOperations leftServices) leftPre ctx
      allowLeft)
    (rightPrefix : Circuit (.quantum rightGates rightOracles rightOperations rightServices)
      rightPre ctx allowRight)
    (leftEnvironment :
      (ExecutionModel.quantum leftGates leftOracles leftOperations leftServices).Environment)
    (rightEnvironment :
      (ExecutionModel.quantum rightGates rightOracles rightOperations rightServices).Environment)
    (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (cells index).key)
    {Reference : Register}
    (leftInput : Execution.OracleInput leftServices leftPre Reference)
    (rightInput : Execution.OracleInput rightServices rightPre Reference)
    (same :
      (leftPrefix.execute leftEnvironment Reference
        (leftInput.state.mapClassical
          (fun original => (original.1, (original.2, original.1))))).quantumMarginal =
      (rightPrefix.execute rightEnvironment Reference
        (rightInput.state.mapClassical
          (fun original => (original.1, (original.2, original.1))))).quantumMarginal)
    (event : (Fin width → Bool) → Bool) :
    ((qubitReadout leftPrefix wires qubits cells).outputDistribution leftEnvironment leftInput).map
        (fun value => event (QubitReadouts.mask value)) true =
      ((qubitReadout rightPrefix wires qubits cells).outputDistribution
        rightEnvironment rightInput).map
        (fun value => event (QubitReadouts.mask value)) true := by
  rw [qubitReadout_eventProbability leftPrefix leftEnvironment
      wires qubits cells distinct leftInput event,
    qubitReadout_eventProbability rightPrefix rightEnvironment
      wires qubits cells distinct rightInput event, same]

end

end QuantumAlg.AlgorithmRun
