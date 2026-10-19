/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Completion
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Resources
import all QuantumAlg.Core.Execution.Measurement.Sequence

/-!
# Independent complete event bounds for actual declared Shor rounds

The closed allowance includes the original sampler, native quantum peripheral
gates and sole query, actual phase measurements and paid bit packing, full
native recovery and first-success feedback, then physical same-bank reset.
No allowance is projected from the path or resource pool being verified.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

/-- The complete selected quantum word, each real phase readout and its one paid bit pack. -/
def observationEnvelope (N : Nat) : ResourcePool (executionModel N) :=
  DeclaredSource.eventEnvelope (modulusBits N) (phaseBits N) BitWord.model .empty +
    ((phaseBits N) • ResourcePool.singleton (model := executionModel N)
      (.measurement (2 : ℕ+)) +
      ResourcePool.singleton (model := executionModel N)
        (.classicalOperation
          (BitWord.selectedCoordinate (execution := executionModel N)
            (.nominalEncoding (.packFiniteBits (phaseBits N))))))

/-- The original real residue sampler precedes the complete selected observation. -/
def iterationEnvelope (N : Nat) : ResourcePool (executionModel N) :=
  Sampler.Retained.nativeEnvelope (executionModel N) N + observationEnvelope N

/-- A complete round includes paid factor recovery, feedback and the actual physical reset. -/
def completionEnvelope (N : Nat) : ResourcePool (executionModel N) :=
  iterationEnvelope N + (NativeFactorScan.visitEnvelope (executionModel N) N +
    ZReset.Bank.envelope
      (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
      (bankQubits N) BitWord.model)

private abbrev phaseMeasurements (ctx : RuntimeCtx .quantum) (N : Nat)
    (sameWires : ctx.quantumWires = (layout N).wires) :
    Circuit (executionModel N) (Storage.context ctx N) (Storage.context ctx N) :=
  Circuit.measurementSequence (gates := AlgorithmGate.model)
    (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
    (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
    (readouts ctx N sameWires)

private lemma allocation_trace (ctx : RuntimeCtx .quantum) (N : Nat)
    (path : (allocate ctx N).Path) : (allocate ctx N).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (model := executionModel N)
    (Storage.resultContext ctx N) 2 (phaseBits N) path.2

/-- Every actual stored-base selection has the same original native peripheral and query pool. -/
lemma selected_pool_eq (ctx : RuntimeCtx .quantum) (N : Nat)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (path : (selected ctx N sameWires parameter).Path) :
    (selected ctx N sameWires parameter).resourcePool path =
      DeclaredSource.eventEnvelope (modulusBits N) (phaseBits N) BitWord.model .empty := by
  rcases path with ⟨value, memberPath⟩
  change ResourcePool.ofList
    ((member N ((Storage.quantumWires ctx N).trans sameWires)
      value).eventTrace BitWord.model .empty) = _
  exact (UnitaryCircuit.ofList_eventTrace_eq_eventCost
    (member N ((Storage.quantumWires ctx N).trans sameWires) value)
    BitWord.model .empty).trans ((member_eventCost N
      ((Storage.quantumWires ctx N).trans sameWires) value).trans
        (DeclaredSource.circuit_eventCost_eq_envelope (modulusBits N) (phaseBits N)
          (selectedBase value) BitWord.model .empty))

/-- Every actual phase wire pays its dimension-two measurement, including all retained outcomes. -/
lemma readouts_pool_eq (ctx : RuntimeCtx .quantum) (N : Nat)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (path : (phaseMeasurements ctx N sameWires).Path) :
    (phaseMeasurements ctx N sameWires).resourcePool path =
        (phaseBits N) • ResourcePool.singleton (model := executionModel N)
          (.measurement (2 : ℕ+)) := by
  have qubits (item : ZReadout (Storage.context ctx N))
      (_present : item ∈ readouts ctx N sameWires) :
      ((Storage.context ctx N).quantumLayout.wire item.wire).dimension = 2 :=
    shorDeclared_context_qubits N ((Storage.quantumWires ctx N).trans sameWires) item.wire
  rw [Circuit.measurementSequence_qubit_resourcePool (gates := AlgorithmGate.model)
      (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
      (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
      (readouts ctx N sameWires) qubits]
  simp only [readouts, List.length_ofFn]
  rfl

/-- The actual selected member, phase measurements and pack fit the independent observation pool. -/
lemma body_pool_le (ctx : RuntimeCtx .quantum) (N : Nat)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (path : (body ctx N sameWires parameter).Path) :
    (body ctx N sameWires parameter).resourcePool path ≤ observationEnvelope N := by
  rcases path with ⟨selectedPath, measuredPath, packedPath⟩
  change ResourcePool.ofList ((selected ctx N sameWires parameter).eventTrace selectedPath ++
    ((phaseMeasurements ctx N sameWires).eventTrace measuredPath ++
        [.classicalOperation (.nominalEncoding (.packFiniteBits (phaseBits N)))])) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  change (selected ctx N sameWires parameter).resourcePool selectedPath +
    ((phaseMeasurements ctx N sameWires).resourcePool measuredPath +
      ResourcePool.ofList (model := executionModel N)
        [.classicalOperation (.nominalEncoding (.packFiniteBits (phaseBits N)))]) ≤ _
  rw [selected_pool_eq, readouts_pool_eq]
  exact le_rfl

/-- Real result-cell allocation adds no hidden event to the same complete observation. -/
lemma code_pool_le (ctx : RuntimeCtx .quantum) (N : Nat)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (path : (code ctx N sameWires parameter).Path) :
    (code ctx N sameWires parameter).resourcePool path ≤ observationEnvelope N := by
  change ResourcePool.ofList ((allocate ctx N).eventTrace path.1 ++
    (body ctx N sameWires parameter).eventTrace path.2) ≤ _
  rw [allocation_trace, List.nil_append]
  exact body_pool_le ctx N sameWires parameter path.2

/-- Every real sampled observation charges the original full residue preparation and draw. -/
lemma Iteration.code_pool_le (ctx : RuntimeCtx .quantum) (N : Nat)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (path : (Iteration.code ctx N sameWires).Path) :
    (Iteration.code ctx N sameWires).resourcePool path ≤ iterationEnvelope N := by
  change ResourcePool.ofList
    ((Sampler.Retained.circuit (model := executionModel N) ctx N).eventTrace path.1 ++
      (Runtime.code (Iteration.sampledContext ctx N) N
        ((Iteration.sampled_quantumWires ctx N).trans sameWires)
        (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef)).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (Sampler.Retained.samplerRetained_pool_le (model := executionModel N)
    ctx N path.1) (Runtime.code_pool_le (Iteration.sampledContext ctx N) N
      ((Iteration.sampled_quantumWires ctx N).trans sameWires)
      (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef) path.2)

/-- Full actual recovery, selection and same-bank reset complete the one-round event allowance. -/
lemma Completion.code_pool_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (Completion.code ctx N input sameWires cells result).Path) :
    (Completion.code ctx N input sameWires cells result).resourcePool path ≤
      completionEnvelope N := by
  change ResourcePool.ofList ((Iteration.code ctx N sameWires).eventTrace path.1 ++
    ((Completion.feedback ctx N input cells result).eventTrace path.2.1 ++
      (reset (Iteration.context ctx N) N
        ((Iteration.quantumWires ctx N).trans sameWires)).eventTrace path.2.2)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add (Iteration.code_pool_le ctx N sameWires path.1)
    (add_le_add (NativeFactorScan.visit_pool_le (model := executionModel N) input
      (Completion.inputs ctx N) (Completion.cells ctx N cells) (Completion.liftWrite ctx N result)
      path.2.1) (reset_events_le (Iteration.context ctx N) N
        ((Iteration.quantumWires ctx N).trans sameWires) path.2.2))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
