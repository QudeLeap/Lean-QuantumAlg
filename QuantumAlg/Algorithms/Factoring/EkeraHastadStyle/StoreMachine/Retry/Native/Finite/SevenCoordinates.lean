/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Space
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Gates
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Counts
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.AllKeys

/-!
# Seven symbolic coordinates of one complete native factoring execution

The formulas apply to every original modulus input and every finite batch
count. All seven observations use the same actual path. Quantum computation
time is bounded by the complete independent event-depth allowance; every
classical operation and the terminal selector remain in the native event ledger.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry

noncomputable section

open Execution ShortDLP.CompiledMAU

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Seven independent width-only ceilings for one actual all-key run path. -/
def SevenCoordinateBounds (input : Input N) (count : Nat)
    (path : (run base noQuantum input count).code.Path) : Prop :=
    (run base noQuantum input count).code.peakResidentSpace
      path (.quantumSystems 2) ≤
        base.residentSpace (.quantumSystems 2) + qubitBound N count ∧
    ResourcePool.count (model := RuntimeRound.model) (.gate .toffoli)
      ((run base noQuantum input count).code.resourcePool path) ≤
        gateCountBound N count .toffoli ∧
    ResourcePool.count (model := RuntimeRound.model) (.gate .cnot)
      ((run base noQuantum input count).code.resourcePool path) ≤
        gateCountBound N count .cnot ∧
    ResourcePool.count (model := RuntimeRound.model) (.gate .singleQubit)
      ((run base noQuantum input count).code.resourcePool path) ≤
        gateCountBound N count .singleQubit ∧
    (run base noQuantum input count).code.quantumTime path ≤ depthBound N count ∧
    ((run base noQuantum input count).code.peakResidentSpace
      path .classicalBits ≤
        base.residentSpace .classicalBits + classicalBitBound N count ∧
    (run base noQuantum input count).code.peakAuxiliarySpace
      path .classicalBits ≤
        base.auxiliarySpace .classicalBits + classicalBitBound N count) ∧
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((run base noQuantum input count).code.resourcePool path) ≤
        scalarClassicalOperationBound N count

/-- The same physical path meets all seven parameterized ceilings. -/
lemma sevenCoordinates (input : Input N) (count : Nat)
    (path : (run base noQuantum input count).code.Path) :
    SevenCoordinateBounds base noQuantum input count path := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact run_resident_qubits_le base noQuantum input count path
  · exact run_gateCount_le base noQuantum input count path .toffoli
  · exact run_gateCount_le base noQuantum input count path .cnot
  · exact run_gateCount_le base noQuantum input count path .singleQubit
  · exact run_quantumTime_le base noQuantum input count path
  · exact ⟨run_resident_classicalBits_le base noQuantum input count path,
      run_auxiliary_classicalBits_le base noQuantum input count path⟩
  · exact run_classicalOperation_le_widthBound base noQuantum input count path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry
