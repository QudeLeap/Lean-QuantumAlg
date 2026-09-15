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

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution

variable {pre ctx : RuntimeCtx .quantum} {width : Nat}

/-- Execute a prefix and actual qubit readout, returning the complete finite-cell vector. -/
def qubitReadout (prior : Circuit pre ctx) (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2)) :
    AlgorithmRun pre ctx (.fixedVector width (.finite 2)) where
  code := .seq prior (.measurementSequence (QubitReadouts.readouts wires qubits cells))
  output := Output.all ctx (.read (QubitReadouts.input cells))

/-- Actual final readout events pair only with the prefix's full quantum marginal. -/
theorem qubitReadout_effectWeight (prior : Circuit pre ctx)
    (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (cells index).key)
    {Reference : Register}
    (input : ExecutionState (Store pre) (Register.prod pre.register Reference))
    (event : (Fin width → Bool) → Bool) :
    ((qubitReadout prior wires qubits cells).execute Reference input).effectWeight
        (fun record => if event (QubitReadouts.mask (record.1.read
          (QubitReadouts.input cells))) = true then
            Effect.one (Register.prod ctx.register Reference)
          else Effect.zero (Register.prod ctx.register Reference)) =
      (QubitReadouts.eventEffect wires event Reference).weight
        (prior.execute Reference
          (input.mapClassical (fun store => (store, store)))).quantumMarginal := by
  unfold execute
  change ((Circuit.seq prior
    (Circuit.measurementSequence (QubitReadouts.readouts wires qubits cells))).execute
      Reference (input.mapClassical (fun store => (store, store)))).effectWeight _ = _
  rw [Circuit.execute_seq]
  erw [State.effectWeight_mapHistory]
  exact QubitReadouts.measurement_eventEffectWeight wires qubits cells distinct _ event

/-- The real output PMF gives the same event weight, with its actual original-store history. -/
theorem qubitReadout_eventProbability (prior : Circuit pre ctx)
    (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (cells index).key)
    {Reference : Register} (input : Execution.Input pre Reference)
    (event : (Fin width → Bool) → Bool) :
    ((qubitReadout prior wires qubits cells).outputDistribution input).map
        (fun value => event (QubitReadouts.mask value)) true =
      ENNReal.ofReal ((QubitReadouts.eventEffect wires event Reference).weight
        (prior.execute Reference
          (input.state.mapClassical (fun store => (store, store)))).quantumMarginal) := by
  rw [outputDistribution_event_eq_effectWeight]
  exact congrArg ENNReal.ofReal
    (qubitReadout_effectWeight prior wires qubits cells distinct input.state event)

/-- Different actual prefixes have equal readout probabilities when their full marginals agree. -/
theorem qubitReadout_eventProbability_eq_of_quantumMarginal_eq
    {leftPre rightPre : RuntimeCtx .quantum}
    (leftPrefix : Circuit leftPre ctx) (rightPrefix : Circuit rightPre ctx)
    (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (cells index).key)
    {Reference : Register}
    (leftInput : Execution.Input leftPre Reference)
    (rightInput : Execution.Input rightPre Reference)
    (same :
      (leftPrefix.execute Reference
        (leftInput.state.mapClassical (fun store => (store, store)))).quantumMarginal =
      (rightPrefix.execute Reference
        (rightInput.state.mapClassical (fun store => (store, store)))).quantumMarginal)
    (event : (Fin width → Bool) → Bool) :
    ((qubitReadout leftPrefix wires qubits cells).outputDistribution leftInput).map
        (fun value => event (QubitReadouts.mask value)) true =
      ((qubitReadout rightPrefix wires qubits cells).outputDistribution rightInput).map
        (fun value => event (QubitReadouts.mask value)) true := by
  rw [qubitReadout_eventProbability leftPrefix wires qubits cells distinct leftInput event,
    qubitReadout_eventProbability rightPrefix wires qubits cells distinct rightInput event, same]

end

end QuantumAlg.AlgorithmRun
