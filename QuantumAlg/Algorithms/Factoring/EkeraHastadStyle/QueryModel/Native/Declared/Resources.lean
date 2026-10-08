/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Program
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds

/-!
# Resources of the declared short-DLP observation

The runtime parameter chooses one query from the fixed group-operation model.
These identities account for the selected physical circuit on the actual
execution path, with the active classical-operation model retained.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

open Execution

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)
  (input : Input N)

/-- The selected branch emits exactly the placed stage's native event trace. -/
theorem selected_eventTrace (parameter : CInputRef base (ParameterShape N))
    (path : (selected base noQuantum N input parameter).Path) :
    (selected base noQuantum N input parameter).eventTrace path =
      (Native.declaredMember N (Native.nativeOracle_context_wires base noQuantum N)
        input path.1).eventTrace BitWord.model .empty := rfl

/-- The path's charged pool is derived from that exact selected circuit. -/
theorem selected_resourcePool (parameter : CInputRef base (ParameterShape N))
    (path : (selected base noQuantum N input parameter).Path) :
    (selected base noQuantum N input parameter).resourcePool path =
      (Native.declaredMember N (Native.nativeOracle_context_wires base noQuantum N)
        input path.1).eventCost BitWord.model .empty := by
  rw [Circuit.resourcePool, selected_eventTrace]
  exact UnitaryCircuit.ofList_eventTrace_eq_eventCost _ BitWord.model .empty

/-- Every selected runtime parameter costs exactly one declared group query,
also inside the active bit-word classical model. -/
theorem selected_groupQueryCount (parameter : CInputRef base (ParameterShape N))
    (path : (selected base noQuantum N input parameter).Path) :
    ResourcePool.count (model := model input) (.oracle .groupOperation)
      ((selected base noQuantum N input parameter).resourcePool path) = 1 := by
  rw [selected_resourcePool,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  exact Native.declaredMember_groupQueryCount N
    (Native.nativeOracle_context_wires base noQuantum N) input path.1

private theorem readouts_events
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := ShortDLP.declaredModel (Native.encoding input))
      (operations := BitWord.model)
      (readouts base noQuantum N)).Path) :
    (Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := ShortDLP.declaredModel (Native.encoding input))
      (operations := BitWord.model)
      (readouts base noQuantum N)).eventTrace path =
      List.replicate (measurementBits N)
        (Circuit.zEvent (gates := AlgorithmGate.model)
          (oracles := ShortDLP.declaredModel (Native.encoding input))
          (operations := BitWord.model) 2) := by
  rw [Circuit.measurementSequence_eventTrace, readouts, List.map_ofFn]
  simp only [Native.nativeOracle_context_qubits N
    (Native.nativeOracle_context_wires base noQuantum N)]
  exact List.ofFn_const _ _

/-- The actual one-shot path contains bank preparation, the selected declared
stage, every source exponent measurement, and one paid bit packing. -/
theorem code_eventTrace (parameter : CInputRef base (ParameterShape N))
    (path : (code base noQuantum N input parameter).Path) :
    (code base noQuantum N input parameter).eventTrace path =
      (prepare base noQuantum N input).eventTrace path.1 ++
        (Native.declaredMember N (Native.nativeOracle_context_wires base noQuantum N)
          input path.2.2.1.1).eventTrace BitWord.model .empty ++
        (List.replicate (measurementBits N)
          (Circuit.zEvent (gates := AlgorithmGate.model)
            (oracles := ShortDLP.declaredModel (Native.encoding input))
            (operations := BitWord.model) 2) ++
          [.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))]) := by
  change (prepare base noQuantum N input).eventTrace path.1 ++
    (((MeasurementCells.allocate (model := model input)
      (Native.bankContext base noQuantum N) 2 (measurementBits N)).eventTrace
      path.2.1.1 ++ []) ++
        ((selected base noQuantum N input parameter).eventTrace path.2.2.1 ++
          ((Circuit.measurementSequence (gates := AlgorithmGate.model)
            (oracles := ShortDLP.declaredModel (Native.encoding input))
            (operations := BitWord.model)
            (readouts base noQuantum N)).eventTrace path.2.2.2.1 ++
            [.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))]))) = _
  rw [MeasurementCells.allocate_eventTrace,
    selected_eventTrace, readouts_events]
  simp only [List.nil_append, List.append_nil, List.append_assoc]

/-- Forgetting order in that exact path yields the preparation charge, the
selected stage ledger, every Z outcome, and the one classical packing charge. -/
theorem code_resourcePool (parameter : CInputRef base (ParameterShape N))
    (path : (code base noQuantum N input parameter).Path) :
    (code base noQuantum N input parameter).resourcePool path =
      ResourcePool.ofList ((prepare base noQuantum N input).eventTrace path.1) +
        ((Native.declaredMember N (Native.nativeOracle_context_wires base noQuantum N)
          input path.2.2.1.1).eventCost BitWord.model .empty +
          ((measurementBits N) • ResourcePool.singleton
            (Circuit.zEvent (gates := AlgorithmGate.model)
              (oracles := ShortDLP.declaredModel (Native.encoding input))
              (operations := BitWord.model) 2) +
            ResourcePool.singleton
              (Resource.Event.classicalOperation
                (model := model input)
                (.nominalEncoding (.packFiniteBits (measurementBits N)))))) := by
  rw [Circuit.resourcePool, code_eventTrace]
  simp only [ResourcePool.ofList_append, ResourcePool.ofList_cons,
    ResourcePool.ofList_nil, add_zero,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    ResourcePool.ofList_replicate, ResourcePool.scale, add_assoc]

private theorem prepare_groupQueryCount
    (path : (prepare base noQuantum N input).Path) :
    ResourcePool.count (model := model input) (.oracle .groupOperation)
      (ResourcePool.ofList ((prepare base noQuantum N input).eventTrace path)) = 0 := by
  simp only [prepare, Circuit.eventTrace, ZeroPreparation.eventTrace,
    ResourcePool.count_ofList]
  apply List.count_eq_zero_of_not_mem
  intro member
  obtain ⟨index, equality⟩ := List.mem_ofFn.mp member
  cases equality

/-- The entire one-shot program makes exactly one declared group query on
every runtime path; preparation, measurement and packing add none. -/
theorem code_groupQueryCount (parameter : CInputRef base (ParameterShape N))
    (path : (code base noQuantum N input parameter).Path) :
    ResourcePool.count (model := model input) (.oracle .groupOperation)
      ((code base noQuantum N input parameter).resourcePool path) = 1 := by
  rw [code_resourcePool, ResourcePool.count_add,
    ResourcePool.count_add, ResourcePool.count_add,
    prepare_groupQueryCount]
  have stage :
      ResourcePool.count (model := model input) (.oracle .groupOperation)
        ((Native.declaredMember N (Native.nativeOracle_context_wires base noQuantum N)
          input path.2.2.1.1).eventCost BitWord.model .empty) = 1 := by
    rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
    exact Native.declaredMember_groupQueryCount N
      (Native.nativeOracle_context_wires base noQuantum N) input path.2.2.1.1
  rw [stage]
  simp [Circuit.zEvent, ResourcePool.count_nsmul, ResourcePool.count_singleton]

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
