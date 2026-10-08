/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Initialization
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Complete resources of actual intrinsic ECDLP sampling

The same code charges zero preparation, the native infinity-tag X, both
parallel peripheral pairs, the one declared query and every actual Z read.
The original borrowed point inputs remain in both real storage ledgers.
These observations concern one sample; recovery and retry costs are separate.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling

noncomputable section

open QuantumAlg.Execution

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

attribute [local implicit_reducible] readoutCode

/-- The complete sampling ledger includes initialization and all terminal measurements. -/
public def eventBudget (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    ResourcePool (executionModel I A) :=
  ZeroPreparation.eventCost AlgorithmGate.model (model I A) (layout I) BitWord.model .empty +
    (nativeProgram I A expansion).eventCost BitWord.model .empty +
    sampleWidth I • ResourcePool.singleton (model := executionModel I A) (.measurement (2 : ℕ+))

private theorem allocation_trace (I : ECDLPInstance E) (A : Access I)
    (path : (allocationCode I A).Path) : (allocationCode I A).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (model := executionModel I A)
    (bankContext I) 2 (sampleWidth I) path

private theorem preparation_pool (I : ECDLPInstance E) (A : Access I)
    (path : (preparationCode I A).Path) :
    ResourcePool.ofList ((preparationCode I A).eventTrace path) =
      ZeroPreparation.eventCost AlgorithmGate.model (model I A) (layout I) BitWord.model .empty :=
  rfl

private theorem program_pool (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    ResourcePool.ofList ((nativeProgram I A expansion).eventTrace BitWord.model .empty) =
      (nativeProgram I A expansion).eventCost BitWord.model .empty :=
  UnitaryCircuit.ofList_eventTrace_eq_eventCost (nativeProgram I A expansion) BitWord.model .empty

private theorem readouts_qubits (I : ECDLPInstance E)
    (item : ZReadout (post I)) (present : item ∈ readouts I) :
    ((post I).quantumLayout.wire item.wire).dimension = 2 := by
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact exponent_dimension I index

private theorem measurement_pool (I : ECDLPInstance E) (A : Access I)
    (path : (readoutCode I A).Path) :
    ResourcePool.ofList ((readoutCode I A).eventTrace path) =
      sampleWidth I •
        ResourcePool.singleton (model := executionModel I A) (.measurement (2 : ℕ+)) := by
  rw [← Circuit.resourcePool]
  change (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := model I A)
    (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
    (readouts I)).resourcePool path = _
  rw [Circuit.measurementSequence_qubit_resourcePool (readouts I) (readouts_qubits I)]
  simp only [readouts, List.length_ofFn]
  rfl

/-- Every actual path has exactly the complete allocation-to-readout ledger. -/
public theorem code_events (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (path : (code I A expansion).Path) :
    (code I A expansion).resourcePool path = eventBudget I A expansion := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, initialCode,
    Circuit.eventTrace, allocation_trace, ResourcePool.ofList_append,
    ResourcePool.ofList_nil, add_zero, program_pool, measurement_pool, preparation_pool]
  unfold eventBudget
  abel

/-- All actual result cells, qubits and original classical points coexist in resident storage. -/
public theorem post_residentSpace (I : ECDLPInstance E) :
    (post I).residentSpace =
      sampleWidth I • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout (layout I) + (pre I).residentSpace) := by
  rw [post, MeasurementCells.context_residentSpace, bankContext,
    RuntimeCtx.residentSpace_addOwnedLayout]

/-- The separate auxiliary ledger retains the same owned bank and retained measurement cells. -/
public theorem post_auxiliarySpace (I : ECDLPInstance E) :
    (post I).auxiliarySpace =
      sampleWidth I • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout (layout I) + (pre I).auxiliarySpace) := by
  rw [post, MeasurementCells.context_auxiliarySpace, bankContext,
    RuntimeCtx.auxiliarySpace_addOwnedLayout]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling
