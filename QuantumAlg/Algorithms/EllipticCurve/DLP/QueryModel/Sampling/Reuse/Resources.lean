/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse
import all QuantumAlg.Primitives.ZReset.Bank
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Every physical event and retained cell of reused ECDLP sampling

Both complete resets reserve one Z measurement and at most one native X per
actual system. The initialized source word and every exponent readout are
charged between them. The dedicated reset bit remains in both live ledgers.
These are round-level allowances; checked recovery is charged separately.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

namespace Sampling.Reuse

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Reserve both real resets, the initialized native word and all exponent measurements. -/
public def eventBudget (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    ResourcePool (executionModel I) :=
  ZReset.Bank.envelope (oracles := model I) (context I).systemCount BitWord.model +
    ((nativeProgram I expansion).eventCost BitWord.model .empty +
      (sampleWidth I • ResourcePool.singleton (model := executionModel I)
        (.measurement (2 : ℕ+)) +
          ZReset.Bank.envelope (oracles := model I) (context I).systemCount BitWord.model))

private lemma readout_pool {allowAllocation : Bool} (I : ECDLPInstance E)
    (path : (Circuit.measurementSequence (allowAllocation := allowAllocation)
      (gates := AlgorithmGate.model) (oracles := model I)
      (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
      (readouts I)).Path) :
    (Circuit.measurementSequence (allowAllocation := allowAllocation)
      (gates := AlgorithmGate.model) (oracles := model I)
      (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
      (readouts I)).resourcePool path =
        sampleWidth I • ResourcePool.singleton (model := executionModel I)
          (.measurement (2 : ℕ+)) := by
  rw [Circuit.measurementSequence_qubit_resourcePool (readouts I)
    (fun item _ => ecdlpReuse_qubits I item.wire)]
  simp only [readouts, List.length_ofFn]
  rfl

/-- Every actual round path includes all reset, native, query and terminal-read events. -/
public lemma ecdlpReuse_code_events_le {allowAllocation : Bool}
    (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (path : (code (allowAllocation := allowAllocation) I expansion).Path) :
    (code (allowAllocation := allowAllocation) I expansion).resourcePool path ≤ eventBudget I
        expansion := by
  have resets := ZReset.Bank.zResetBank_resourcePool_le (allowAllocation := allowAllocation)
      (services := .empty) (oracles := model I)
    (operations := BitWord.model) (ecdlpReuse_qubits I) (scratch I)
  have measures := readout_pool (allowAllocation := allowAllocation) I path.2.2.1
  have program := UnitaryCircuit.ofList_eventTrace_eq_eventCost
    (nativeProgram I expansion) BitWord.model .empty
  change ResourcePool.ofList (_ ++ (_ ++ (_ ++ _))) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]
  change (reset (allowAllocation := allowAllocation) I).resourcePool path.1 +
    (ResourcePool.ofList ((nativeProgram I expansion).eventTrace BitWord.model .empty) +
      ((Circuit.measurementSequence (allowAllocation := allowAllocation)
        (readouts I)).resourcePool path.2.2.1 +
        (reset (allowAllocation := allowAllocation) I).resourcePool path.2.2.2)) ≤ _
  rw [program]
  exact add_le_add (resets path.1)
    (add_le_add le_rfl (add_le_add measures.le (resets path.2.2.2)))

/-- Resident storage contains the entire original sampling context and the one real reset cell. -/
public lemma ecdlpReuse_context_resident (I : ECDLPInstance E) :
    (context I).residentSpace = SpacePool.ofShape (.finite 2) +
      (Sampling.post I).residentSpace := by
  rw [context, RuntimeCtx.residentSpace_addRetained]

/-- The same reset destination is charged to auxiliary storage beside all original roles. -/
public lemma ecdlpReuse_context_auxiliary (I : ECDLPInstance E) :
    (context I).auxiliarySpace = SpacePool.ofShape (.finite 2) +
      (Sampling.post I).auxiliarySpace := by
  rw [context, RuntimeCtx.auxiliarySpace_addRetained]

end

end Sampling.Reuse

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
